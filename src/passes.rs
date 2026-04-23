use std::collections::HashMap;
use std::fmt;

use crate::ast::{AstWorld, BinOp, Builtin, NodeId, NodeKind, TypeInfo, UnaryOp};
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnalysisError {
    pub span: Option<Span>,
    pub message: String,
}

impl AnalysisError {
    fn new(span: Option<Span>, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }
}

impl fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(span) => write!(f, "{} at bytes {}..{}", self.message, span.start, span.end),
            None => write!(f, "{}", self.message),
        }
    }
}

impl std::error::Error for AnalysisError {}

// ---------------------------------------------------------------------------
// Pass: literal type annotation
//
// Populates the `types` component store for all literal nodes.
// Leaves every other component store untouched.
// ---------------------------------------------------------------------------

pub fn annotate_literal_types(world: &mut AstWorld<'_>) {
    let ids: Vec<NodeId> = world.kinds.keys().collect();
    for id in ids {
        let ty = match &world.kinds[id] {
            NodeKind::IntLit(_) => Some(TypeInfo::Int),
            NodeKind::FloatLit(_) => Some(TypeInfo::Float),
            NodeKind::BoolLit(_) => Some(TypeInfo::Bool),
            NodeKind::StringLit(_) => Some(TypeInfo::Str),
            _ => None,
        };
        if let Some(t) = ty {
            world.types.insert(id, t);
        }
    }
}

// ---------------------------------------------------------------------------
// Pass: parent-link computation
//
// Walks the tree and fills `world.parents` so that every non-root node knows
// its parent. Not needed during parsing — only computed if a consumer asks.
// ---------------------------------------------------------------------------

pub fn compute_parents(world: &mut AstWorld<'_>, id: NodeId, parent: Option<NodeId>) {
    if let Some(p) = parent {
        world.parents.insert(id, p);
    }

    // Collect children without holding a borrow on `world`.
    // NodeKind is Copy, so *world.kind(id) gives an owned copy with no clone.
    let children: Vec<NodeId> = match *world.kind(id) {
        NodeKind::Program(items) => items.to_vec(),
        NodeKind::FnDecl {
            params,
            ret_ty,
            body,
            ..
        } => {
            let mut ch: Vec<_> = params.to_vec();
            ch.extend(ret_ty);
            ch.push(body);
            ch
        }
        NodeKind::Param { ty, .. } => ty.into_iter().collect(),
        NodeKind::Block(stmts) => stmts.to_vec(),
        NodeKind::LetStmt { ty, init, .. } => ty.into_iter().chain(init).collect(),
        NodeKind::AssignStmt { target, value } => vec![target, value],
        NodeKind::ReturnStmt(v) => v.into_iter().collect(),
        NodeKind::IfStmt {
            cond,
            then_block,
            else_block,
        } => {
            let mut ch = vec![cond, then_block];
            ch.extend(else_block);
            ch
        }
        NodeKind::WhileStmt { cond, body } => vec![cond, body],
        NodeKind::BinOp { lhs, rhs, .. } => vec![lhs, rhs],
        NodeKind::UnaryOp { operand, .. } => vec![operand],
        NodeKind::Call { callee, args } => {
            let mut ch = vec![callee];
            ch.extend_from_slice(args);
            ch
        }
        NodeKind::BuiltinCall { args, .. } => args.to_vec(),
        // Leaves
        NodeKind::IntLit(_)
        | NodeKind::FloatLit(_)
        | NodeKind::BoolLit(_)
        | NodeKind::StringLit(_)
        | NodeKind::Ident(_)
        | NodeKind::TypeName(_) => vec![],
    };

    for child in children {
        compute_parents(world, child, Some(id));
    }
}

// ---------------------------------------------------------------------------
// Pass: name resolution + type checking
//
// Populates:
//   - `resolved`: identifier uses -> declaration nodes
//   - `types`: expressions, type names, params, lets, and function declarations
//
// This keeps semantic facts in ECS component stores, so codegen does not need
// to rediscover undefined names, bad calls, or mismatched types accidentally.
// ---------------------------------------------------------------------------

type AnalysisResult<T> = Result<T, AnalysisError>;

#[derive(Clone)]
struct FuncSig {
    node: NodeId,
    params: Vec<TypeInfo>,
    ret: TypeInfo,
}

#[derive(Clone)]
struct Binding {
    decl: NodeId,
    ty: TypeInfo,
}

/// Statement/block control-flow summary used to reject non-unit functions
/// whose bodies can fall through without hitting a `return`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Flow {
    MayContinue,
    AlwaysReturns,
}

impl Flow {
    fn returns(self) -> bool {
        matches!(self, Self::AlwaysReturns)
    }
}

pub fn analyze_program(world: &mut AstWorld<'_>, root: NodeId) -> AnalysisResult<()> {
    // These are derived component stores. Clear them so repeated analysis
    // cannot observe stale type/resolution/parent facts from an earlier run.
    world.types.clear();
    world.parents.clear();
    world.resolved.clear();

    compute_parents(world, root, None);

    let mut analyzer = Analyzer::new(world);
    analyzer.collect_functions(root)?;
    analyzer.check_program(root)
}

struct Analyzer<'w, 'arena> {
    world: &'w mut AstWorld<'arena>,
    funcs: HashMap<String, FuncSig>,
    scopes: Vec<HashMap<String, Binding>>,
}

impl<'w, 'arena> Analyzer<'w, 'arena> {
    fn new(world: &'w mut AstWorld<'arena>) -> Self {
        Self {
            world,
            funcs: HashMap::new(),
            scopes: Vec::new(),
        }
    }

    fn collect_functions(&mut self, root: NodeId) -> AnalysisResult<()> {
        let items = match *self.world.kind(root) {
            NodeKind::Program(items) => items,
            _ => return Err(self.error(root, "root must be a Program node")),
        };

        for &item in items {
            let NodeKind::FnDecl {
                name,
                params,
                ret_ty,
                ..
            } = *self.world.kind(item)
            else {
                return Err(self.error(item, "top-level item must be a function"));
            };

            if Builtin::from_name(name).is_some() {
                return Err(self.error(item, format!("function name `{name}` is reserved")));
            }
            if self.funcs.contains_key(name) {
                return Err(self.error(item, format!("duplicate function `{name}`")));
            }

            let mut param_types = Vec::new();
            for &param in params {
                let NodeKind::Param { ty: Some(ty), .. } = *self.world.kind(param) else {
                    return Err(self.error(param, "function parameter is missing a type"));
                };
                param_types.push(self.type_from_node(ty)?);
            }

            let ret = ret_ty
                .map(|ty| self.type_from_node(ty))
                .transpose()?
                .unwrap_or(TypeInfo::Unit);
            if ret == TypeInfo::Str {
                return Err(self.error(item, "functions cannot return str yet"));
            }

            self.world.types.insert(
                item,
                TypeInfo::Fn {
                    params: param_types.clone(),
                    ret: Box::new(ret.clone()),
                },
            );

            self.funcs.insert(
                name.to_string(),
                FuncSig {
                    node: item,
                    params: param_types,
                    ret,
                },
            );
        }

        let Some(main) = self.funcs.get("main").cloned() else {
            return Err(AnalysisError::new(None, "program must define `fn main()`"));
        };
        if !main.params.is_empty() {
            return Err(self.error(main.node, "`main` must not take parameters"));
        }
        if main.ret != TypeInfo::Unit {
            return Err(self.error(main.node, "`main` must not declare a return type"));
        }

        Ok(())
    }

    fn check_program(&mut self, root: NodeId) -> AnalysisResult<()> {
        let items = match *self.world.kind(root) {
            NodeKind::Program(items) => items,
            _ => return Err(self.error(root, "root must be a Program node")),
        };

        for &item in items {
            self.check_function(item)?;
        }

        self.world.types.insert(root, TypeInfo::Unit);
        Ok(())
    }

    fn check_function(&mut self, id: NodeId) -> AnalysisResult<()> {
        let NodeKind::FnDecl {
            name,
            params,
            ret_ty,
            body,
            ..
        } = *self.world.kind(id)
        else {
            return Err(self.error(id, "expected function declaration"));
        };

        let expected_ret = ret_ty
            .map(|ty| self.type_from_node(ty))
            .transpose()?
            .unwrap_or(TypeInfo::Unit);

        self.push_scope();
        for &param in params {
            let NodeKind::Param { name, ty: Some(ty) } = *self.world.kind(param) else {
                return Err(self.error(param, "function parameter is missing a type"));
            };
            let param_ty = self.type_from_node(ty)?;
            self.define_local(param, name, param_ty.clone())?;
            self.world.types.insert(param, param_ty);
        }

        let flow = self.check_block(body, &expected_ret)?;
        self.pop_scope();

        if expected_ret != TypeInfo::Unit && !flow.returns() {
            return Err(self.error(
                id,
                format!(
                    "function `{name}` may exit without returning {}",
                    describe_type(&expected_ret)
                ),
            ));
        }

        Ok(())
    }

    fn check_block(&mut self, id: NodeId, expected_ret: &TypeInfo) -> AnalysisResult<Flow> {
        let stmts = match *self.world.kind(id) {
            NodeKind::Block(stmts) => stmts,
            _ => return Err(self.error(id, "expected block")),
        };

        self.push_scope();
        let mut returns = false;
        for &stmt in stmts {
            if self.check_stmt(stmt, expected_ret)?.returns() {
                returns = true;
            }
        }
        self.pop_scope();

        self.world.types.insert(id, TypeInfo::Unit);
        Ok(if returns {
            Flow::AlwaysReturns
        } else {
            Flow::MayContinue
        })
    }

    fn check_stmt(&mut self, id: NodeId, expected_ret: &TypeInfo) -> AnalysisResult<Flow> {
        match *self.world.kind(id) {
            NodeKind::LetStmt { name, ty, init } => {
                self.check_let(id, name, ty, init)?;
                Ok(Flow::MayContinue)
            }
            NodeKind::AssignStmt { target, value } => {
                self.check_assign(id, target, value)?;
                Ok(Flow::MayContinue)
            }
            NodeKind::ReturnStmt(expr) => {
                self.check_return(id, expr, expected_ret)?;
                Ok(Flow::AlwaysReturns)
            }
            NodeKind::IfStmt {
                cond,
                then_block,
                else_block,
            } => self.check_if(id, cond, then_block, else_block, expected_ret),
            NodeKind::WhileStmt { cond, body } => {
                self.check_while(id, cond, body, expected_ret)?;
                Ok(Flow::MayContinue)
            }
            NodeKind::Block(_) => self.check_block(id, expected_ret),
            NodeKind::Call { .. }
            | NodeKind::BuiltinCall { .. }
            | NodeKind::Ident(_)
            | NodeKind::IntLit(_)
            | NodeKind::FloatLit(_)
            | NodeKind::BoolLit(_)
            | NodeKind::StringLit(_)
            | NodeKind::BinOp { .. }
            | NodeKind::UnaryOp { .. } => {
                self.check_expr(id)?;
                Ok(Flow::MayContinue)
            }
            NodeKind::Program(_)
            | NodeKind::FnDecl { .. }
            | NodeKind::Param { .. }
            | NodeKind::TypeName(_) => Err(self.error(id, "node is not a statement")),
        }
    }

    fn check_let(
        &mut self,
        id: NodeId,
        name: &'arena str,
        ty: Option<NodeId>,
        init: Option<NodeId>,
    ) -> AnalysisResult<()> {
        let declared_ty = ty.map(|ty| self.type_from_node(ty)).transpose()?;
        let init_ty = init.map(|expr| self.check_expr(expr)).transpose()?;

        let final_ty = match (declared_ty, init_ty) {
            (Some(declared), Some(init)) => {
                self.require_assignable(id, &declared, &init)?;
                declared
            }
            (Some(declared), None) => declared,
            (None, Some(init)) => init,
            (None, None) => {
                return Err(self.error(
                    id,
                    "let statement needs a type annotation, an initializer, or both",
                ));
            }
        };

        self.define_local(id, name, final_ty.clone())?;
        self.world.types.insert(id, final_ty);
        Ok(())
    }

    fn check_assign(&mut self, id: NodeId, target: NodeId, value: NodeId) -> AnalysisResult<()> {
        let NodeKind::Ident(name) = *self.world.kind(target) else {
            return Err(self.error(target, "assignment target must be an identifier"));
        };
        let binding = self
            .resolve_local(name)
            .ok_or_else(|| self.error(target, format!("undefined variable `{name}`")))?;
        let value_ty = self.check_expr(value)?;

        self.world.resolved.insert(target, binding.decl);
        self.world.types.insert(target, binding.ty.clone());
        self.require_assignable(id, &binding.ty, &value_ty)?;
        self.world.types.insert(id, TypeInfo::Unit);
        Ok(())
    }

    fn check_return(
        &mut self,
        id: NodeId,
        expr: Option<NodeId>,
        expected_ret: &TypeInfo,
    ) -> AnalysisResult<()> {
        let actual = match expr {
            Some(expr) => self.check_expr(expr)?,
            None => TypeInfo::Unit,
        };
        self.require_assignable(id, expected_ret, &actual)?;
        self.world.types.insert(id, TypeInfo::Unit);
        Ok(())
    }

    fn check_if(
        &mut self,
        id: NodeId,
        cond: NodeId,
        then_block: NodeId,
        else_block: Option<NodeId>,
        expected_ret: &TypeInfo,
    ) -> AnalysisResult<Flow> {
        let cond_ty = self.check_expr(cond)?;
        self.require_type(cond, &TypeInfo::Bool, &cond_ty, "if condition")?;
        let then_flow = self.check_block(then_block, expected_ret)?;
        let else_flow = else_block
            .map(|else_block| self.check_stmt(else_block, expected_ret))
            .transpose()?
            .unwrap_or(Flow::MayContinue);

        self.world.types.insert(id, TypeInfo::Unit);
        Ok(if then_flow.returns() && else_flow.returns() {
            Flow::AlwaysReturns
        } else {
            Flow::MayContinue
        })
    }

    fn check_while(
        &mut self,
        id: NodeId,
        cond: NodeId,
        body: NodeId,
        expected_ret: &TypeInfo,
    ) -> AnalysisResult<()> {
        let cond_ty = self.check_expr(cond)?;
        self.require_type(cond, &TypeInfo::Bool, &cond_ty, "while condition")?;
        self.check_block(body, expected_ret)?;
        self.world.types.insert(id, TypeInfo::Unit);
        Ok(())
    }

    fn check_expr(&mut self, id: NodeId) -> AnalysisResult<TypeInfo> {
        let ty = match *self.world.kind(id) {
            NodeKind::IntLit(_) => TypeInfo::Int,
            NodeKind::FloatLit(_) => TypeInfo::Float,
            NodeKind::BoolLit(_) => TypeInfo::Bool,
            NodeKind::StringLit(_) => TypeInfo::Str,
            NodeKind::Ident(name) => self.check_ident(id, name)?,
            NodeKind::BinOp { op, lhs, rhs } => self.check_binop(id, op, lhs, rhs)?,
            NodeKind::UnaryOp { op, operand } => self.check_unary(id, op, operand)?,
            NodeKind::Call { callee, args } => self.check_call(id, callee, args)?,
            NodeKind::BuiltinCall { builtin, args } => self.check_builtin(id, builtin, args)?,
            NodeKind::AssignStmt { target, value } => {
                self.check_assign(id, target, value)?;
                TypeInfo::Unit
            }
            _ => return Err(self.error(id, "node is not an expression")),
        };

        self.world.types.insert(id, ty.clone());
        Ok(ty)
    }

    fn check_ident(&mut self, id: NodeId, name: &'arena str) -> AnalysisResult<TypeInfo> {
        let binding = self
            .resolve_local(name)
            .ok_or_else(|| self.error(id, format!("undefined variable `{name}`")))?;
        self.world.resolved.insert(id, binding.decl);
        Ok(binding.ty)
    }

    fn check_binop(
        &mut self,
        id: NodeId,
        op: BinOp,
        lhs: NodeId,
        rhs: NodeId,
    ) -> AnalysisResult<TypeInfo> {
        let lhs_ty = self.check_expr(lhs)?;
        let rhs_ty = self.check_expr(rhs)?;

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Pow => {
                self.require_same(id, &lhs_ty, &rhs_ty)?;
                if lhs_ty == TypeInfo::Int || lhs_ty == TypeInfo::Float {
                    Ok(lhs_ty)
                } else {
                    Err(self.error(
                        id,
                        format!(
                            "operator `{}` requires int or float operands",
                            binop_name(op)
                        ),
                    ))
                }
            }
            BinOp::Mod | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                self.require_type(lhs, &TypeInfo::Int, &lhs_ty, "left operand")?;
                self.require_type(rhs, &TypeInfo::Int, &rhs_ty, "right operand")?;
                Ok(TypeInfo::Int)
            }
            BinOp::Eq | BinOp::Ne => {
                self.require_same(id, &lhs_ty, &rhs_ty)?;
                if matches!(lhs_ty, TypeInfo::Int | TypeInfo::Float | TypeInfo::Bool) {
                    Ok(TypeInfo::Bool)
                } else {
                    Err(self.error(id, "equality is supported for int, float, and bool"))
                }
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.require_same(id, &lhs_ty, &rhs_ty)?;
                if lhs_ty == TypeInfo::Int || lhs_ty == TypeInfo::Float {
                    Ok(TypeInfo::Bool)
                } else {
                    Err(self.error(id, "comparison requires int or float operands"))
                }
            }
            BinOp::And | BinOp::Or => {
                self.require_type(lhs, &TypeInfo::Bool, &lhs_ty, "left operand")?;
                self.require_type(rhs, &TypeInfo::Bool, &rhs_ty, "right operand")?;
                Ok(TypeInfo::Bool)
            }
        }
    }

    fn check_unary(
        &mut self,
        id: NodeId,
        op: UnaryOp,
        operand: NodeId,
    ) -> AnalysisResult<TypeInfo> {
        let operand_ty = self.check_expr(operand)?;
        match op {
            UnaryOp::Neg => {
                if operand_ty == TypeInfo::Int || operand_ty == TypeInfo::Float {
                    Ok(operand_ty)
                } else {
                    Err(self.error(id, "unary `-` requires an int or float operand"))
                }
            }
            UnaryOp::Not => {
                self.require_type(operand, &TypeInfo::Bool, &operand_ty, "operand")?;
                Ok(TypeInfo::Bool)
            }
            UnaryOp::BitNot => {
                self.require_type(operand, &TypeInfo::Int, &operand_ty, "operand")?;
                Ok(TypeInfo::Int)
            }
        }
    }

    fn check_call(
        &mut self,
        id: NodeId,
        callee: NodeId,
        args: &'arena [NodeId],
    ) -> AnalysisResult<TypeInfo> {
        let NodeKind::Ident(name) = *self.world.kind(callee) else {
            return Err(self.error(callee, "callee must be a function name"));
        };
        let sig = self
            .funcs
            .get(name)
            .cloned()
            .ok_or_else(|| self.error(callee, format!("undefined function `{name}`")))?;

        self.world.resolved.insert(callee, sig.node);
        self.world.types.insert(
            callee,
            TypeInfo::Fn {
                params: sig.params.clone(),
                ret: Box::new(sig.ret.clone()),
            },
        );

        if args.len() != sig.params.len() {
            return Err(self.error(
                id,
                format!(
                    "function `{name}` expects {} argument(s), got {}",
                    sig.params.len(),
                    args.len()
                ),
            ));
        }

        for (&arg, expected) in args.iter().zip(sig.params.iter()) {
            let actual = self.check_expr(arg)?;
            self.require_assignable(arg, expected, &actual)?;
        }

        Ok(sig.ret)
    }

    fn check_builtin(
        &mut self,
        id: NodeId,
        builtin: Builtin,
        args: &'arena [NodeId],
    ) -> AnalysisResult<TypeInfo> {
        match builtin {
            Builtin::Print => {
                self.require_arity(id, "print", args, 1)?;
                let arg_ty = self.check_expr(args[0])?;
                if matches!(
                    arg_ty,
                    TypeInfo::Unit | TypeInfo::Fn { .. } | TypeInfo::Unknown
                ) {
                    return Err(self.error(id, "print() requires a printable value"));
                }
                Ok(TypeInfo::Unit)
            }
            Builtin::Argc => {
                self.require_arity(id, "argc", args, 0)?;
                Ok(TypeInfo::Int)
            }
            Builtin::Arg => {
                self.require_arity(id, "arg", args, 1)?;
                let arg_ty = self.check_expr(args[0])?;
                self.require_type(args[0], &TypeInfo::Int, &arg_ty, "arg() index")?;
                Ok(TypeInfo::Str)
            }
        }
    }

    fn type_from_node(&mut self, id: NodeId) -> AnalysisResult<TypeInfo> {
        let ty = match *self.world.kind(id) {
            NodeKind::TypeName("int") => TypeInfo::Int,
            NodeKind::TypeName("float") => TypeInfo::Float,
            NodeKind::TypeName("bool") => TypeInfo::Bool,
            NodeKind::TypeName("str") => TypeInfo::Str,
            NodeKind::TypeName(name) => {
                return Err(self.error(id, format!("unknown type `{name}`")));
            }
            _ => return Err(self.error(id, "expected type name")),
        };
        self.world.types.insert(id, ty.clone());
        Ok(ty)
    }

    fn define_local(&mut self, id: NodeId, name: &'arena str, ty: TypeInfo) -> AnalysisResult<()> {
        let scope = self.scopes.last_mut().expect("scope stack is empty");
        if scope.contains_key(name) {
            return Err(self.error(id, format!("duplicate binding `{name}`")));
        }
        scope.insert(name.to_string(), Binding { decl: id, ty });
        Ok(())
    }

    fn resolve_local(&self, name: &str) -> Option<Binding> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop().expect("scope stack underflow");
    }

    fn require_arity(
        &self,
        id: NodeId,
        name: &str,
        args: &[NodeId],
        expected: usize,
    ) -> AnalysisResult<()> {
        if args.len() == expected {
            Ok(())
        } else {
            Err(self.error(
                id,
                format!(
                    "{name}() expects {expected} argument(s), got {}",
                    args.len()
                ),
            ))
        }
    }

    fn require_assignable(
        &self,
        id: NodeId,
        expected: &TypeInfo,
        actual: &TypeInfo,
    ) -> AnalysisResult<()> {
        if expected == actual {
            Ok(())
        } else {
            Err(self.error(
                id,
                format!(
                    "expected {}, got {}",
                    describe_type(expected),
                    describe_type(actual)
                ),
            ))
        }
    }

    fn require_same(&self, id: NodeId, lhs: &TypeInfo, rhs: &TypeInfo) -> AnalysisResult<()> {
        if lhs == rhs {
            Ok(())
        } else {
            Err(self.error(
                id,
                format!(
                    "type mismatch: {} and {}",
                    describe_type(lhs),
                    describe_type(rhs)
                ),
            ))
        }
    }

    fn require_type(
        &self,
        id: NodeId,
        expected: &TypeInfo,
        actual: &TypeInfo,
        label: &str,
    ) -> AnalysisResult<()> {
        if expected == actual {
            Ok(())
        } else {
            Err(self.error(
                id,
                format!(
                    "{label} must be {}, got {}",
                    describe_type(expected),
                    describe_type(actual)
                ),
            ))
        }
    }

    fn error(&self, id: NodeId, message: impl Into<String>) -> AnalysisError {
        AnalysisError::new(Some(self.world.span(id)), message)
    }
}

fn describe_type(ty: &TypeInfo) -> String {
    match ty {
        TypeInfo::Int => "int".to_string(),
        TypeInfo::Float => "float".to_string(),
        TypeInfo::Bool => "bool".to_string(),
        TypeInfo::Str => "str".to_string(),
        TypeInfo::Unit => "unit".to_string(),
        TypeInfo::Fn { params, ret } => {
            let params = params
                .iter()
                .map(describe_type)
                .collect::<Vec<_>>()
                .join(", ");
            format!("fn({params}) -> {}", describe_type(ret))
        }
        TypeInfo::Unknown => "unknown".to_string(),
    }
}

fn binop_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Pow => "**",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
    }
}
