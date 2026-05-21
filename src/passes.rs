use std::collections::HashMap;
use std::fmt;

use bumpalo::Bump;

use crate::ast::{AstWorld, BinOp, Builtin, NodeId, NodeKind, TypeInfo, UnaryOp};
use crate::modules::{Binding, ModuleGraph, ModuleId};
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

    // Recurse per arm so we don't allocate a Vec<NodeId> for the child list.
    match *world.kind(id) {
        NodeKind::Program(items) | NodeKind::Block(items) => {
            for &child in items {
                compute_parents(world, child, Some(id));
            }
        }
        NodeKind::FnDecl {
            params,
            ret_ty,
            body,
            ..
        } => {
            for &p in params {
                compute_parents(world, p, Some(id));
            }
            if let Some(r) = ret_ty {
                compute_parents(world, r, Some(id));
            }
            compute_parents(world, body, Some(id));
        }
        NodeKind::Param { ty, .. } | NodeKind::LetStmt { ty, init: None, .. } => {
            if let Some(t) = ty {
                compute_parents(world, t, Some(id));
            }
        }
        NodeKind::LetStmt { ty, init: Some(init), .. } => {
            if let Some(t) = ty {
                compute_parents(world, t, Some(id));
            }
            compute_parents(world, init, Some(id));
        }
        NodeKind::AssignStmt { target, value } => {
            compute_parents(world, target, Some(id));
            compute_parents(world, value, Some(id));
        }
        NodeKind::ReturnStmt(Some(v)) => compute_parents(world, v, Some(id)),
        NodeKind::ReturnStmt(None) => {}
        NodeKind::IfStmt {
            cond,
            then_block,
            else_block,
        } => {
            compute_parents(world, cond, Some(id));
            compute_parents(world, then_block, Some(id));
            if let Some(eb) = else_block {
                compute_parents(world, eb, Some(id));
            }
        }
        NodeKind::WhileStmt { cond, body } => {
            compute_parents(world, cond, Some(id));
            compute_parents(world, body, Some(id));
        }
        NodeKind::BinOp { lhs, rhs, .. } => {
            compute_parents(world, lhs, Some(id));
            compute_parents(world, rhs, Some(id));
        }
        NodeKind::UnaryOp { operand, .. } => compute_parents(world, operand, Some(id)),
        NodeKind::Call { callee, args } => {
            compute_parents(world, callee, Some(id));
            for &a in args {
                compute_parents(world, a, Some(id));
            }
        }
        NodeKind::BuiltinCall { args, .. } => {
            for &a in args {
                compute_parents(world, a, Some(id));
            }
        }
        NodeKind::IntLit(_)
        | NodeKind::FloatLit(_)
        | NodeKind::BoolLit(_)
        | NodeKind::StringLit(_)
        | NodeKind::Ident(_)
        | NodeKind::Path { .. }
        | NodeKind::TypeName(_)
        | NodeKind::UseDecl { .. } => {}
    }
}

// ---------------------------------------------------------------------------
// Semantic analysis
//
// Drives the full multi-module pipeline:
//   1. collect_signatures — per-module function table + mangled names
//   2. resolve_use_decls  — wire imports/aliases on each module
//   3. type-check bodies  — pass-aware lookup through the module graph
// ---------------------------------------------------------------------------

type AnalysisResult<T> = Result<T, AnalysisError>;

#[derive(Clone)]
struct FuncSig {
    node: NodeId,
    params: Vec<TypeInfo>,
    ret: TypeInfo,
    is_pub: bool,
}

#[derive(Clone)]
struct Local {
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

/// Per-module function tables, indexed by `ModuleId.0`.
type ModuleFuncs = Vec<HashMap<String, FuncSig>>;

pub fn analyze<'arena>(
    world: &mut AstWorld<'arena>,
    graph: &mut ModuleGraph,
    arena: &'arena Bump,
) -> AnalysisResult<()> {
    world.types.clear();
    world.parents.clear();
    world.resolved.clear();
    world.mangled_names.clear();

    // Parent links across the whole world (every module's root).
    for module in &graph.modules {
        compute_parents(world, module.root, None);
    }

    // Phase 1: collect signatures + assign mangled names.
    let mut module_funcs: ModuleFuncs = vec![HashMap::new(); graph.modules.len()];
    for module_idx in 0..graph.modules.len() {
        collect_signatures(world, graph, ModuleId(module_idx as u32), &mut module_funcs, arena)?;
    }

    // Phase 2: resolve `use` decls on each module (populates module.imports / module_aliases).
    for module_idx in 0..graph.modules.len() {
        resolve_use_decls(world, graph, ModuleId(module_idx as u32), &module_funcs)?;
    }

    // Phase 3: type-check every module.
    for module_idx in 0..graph.modules.len() {
        let mid = ModuleId(module_idx as u32);
        let mut analyzer = Analyzer {
            world,
            graph,
            module: mid,
            module_funcs: &module_funcs,
            scopes: Vec::new(),
        };
        analyzer.check_program()?;
    }

    Ok(())
}

fn collect_signatures<'arena>(
    world: &mut AstWorld<'arena>,
    graph: &ModuleGraph,
    module_id: ModuleId,
    module_funcs: &mut ModuleFuncs,
    arena: &'arena Bump,
) -> AnalysisResult<()> {
    let module = &graph.modules[module_id.0 as usize];
    let is_entry = module_id == graph.entry;
    let mod_path = module.mod_path.clone();
    let root = module.root;

    let items = match *world.kind(root) {
        NodeKind::Program(items) => items,
        _ => return Err(error_at(world, root, "root must be a Program node")),
    };

    let funcs = &mut module_funcs[module_id.0 as usize];

    for &item in items {
        match *world.kind(item) {
            NodeKind::FnDecl {
                name,
                params,
                ret_ty,
                is_pub,
                ..
            } => {
                if Builtin::from_name(name).is_some() {
                    return Err(error_at(
                        world,
                        item,
                        format!("function name `{name}` is reserved"),
                    ));
                }
                if !is_entry && name == "main" {
                    return Err(error_at(
                        world,
                        item,
                        "`fn main` is only allowed in the entry module",
                    ));
                }
                if funcs.contains_key(name) {
                    return Err(error_at(world, item, format!("duplicate function `{name}`")));
                }

                let mut param_types = Vec::new();
                for &param in params {
                    let NodeKind::Param { ty: Some(ty), .. } = *world.kind(param) else {
                        return Err(error_at(world, param, "function parameter is missing a type"));
                    };
                    param_types.push(type_from_node(world, ty)?);
                }

                let ret = ret_ty
                    .map(|ty| type_from_node(world, ty))
                    .transpose()?
                    .unwrap_or(TypeInfo::Unit);
                if ret == TypeInfo::Str {
                    return Err(error_at(world, item, "functions cannot return str yet"));
                }

                world.types.insert(
                    item,
                    TypeInfo::Fn {
                        params: param_types.clone(),
                        ret: Box::new(ret.clone()),
                    },
                );

                // Mangling: entry `main` stays as `main` for the linker.
                // Otherwise: `ecs[__seg]*__name` so cross-module symbols stay distinct.
                let mangled: &'arena str = if is_entry && name == "main" {
                    "main"
                } else {
                    arena.alloc_str(&mangle_name(&mod_path, name))
                };
                world.mangled_names.insert(item, mangled);

                funcs.insert(
                    name.to_string(),
                    FuncSig {
                        node: item,
                        params: param_types,
                        ret,
                        is_pub,
                    },
                );
            }
            NodeKind::UseDecl { .. } => { /* validated in phase 2 */ }
            _ => {
                return Err(error_at(world, item, "top-level item must be a function or use"));
            }
        }
    }

    if is_entry {
        let main = funcs.get("main").cloned().ok_or_else(|| {
            AnalysisError::new(None, "program must define `fn main()`")
        })?;
        if !main.params.is_empty() {
            return Err(error_at(world, main.node, "`main` must not take parameters"));
        }
        if main.ret != TypeInfo::Unit {
            return Err(error_at(
                world,
                main.node,
                "`main` must not declare a return type",
            ));
        }
    }

    Ok(())
}

/// A path resolves to either a module (a known prefix in the graph) or a
/// function (a public item in the trailing module). The semantic pass uses
/// this to populate `bindings` and to resolve call-site paths.
#[derive(Clone, Copy, Debug)]
enum Resolved {
    Module(ModuleId),
    Func { node: NodeId, owner: ModuleId },
}

fn resolve_use_decls(
    world: &AstWorld<'_>,
    graph: &mut ModuleGraph,
    module_id: ModuleId,
    module_funcs: &ModuleFuncs,
) -> AnalysisResult<()> {
    let root = graph.modules[module_id.0 as usize].root;
    let items = match *world.kind(root) {
        NodeKind::Program(items) => items,
        _ => return Ok(()),
    };

    let mut bindings: HashMap<String, Binding> = HashMap::new();

    for &item in items {
        let NodeKind::UseDecl { path } = *world.kind(item) else {
            continue;
        };
        if path.contains(&"*") {
            return Err(error_at(world, item, "glob imports are not supported"));
        }
        if path.is_empty() {
            return Err(error_at(world, item, "empty `use` path"));
        }

        // Reserved-name guard takes precedence over duplicate-import.
        let last = *path.last().unwrap();
        if Builtin::from_name(last).is_some() {
            return Err(error_at(
                world,
                item,
                format!("`{last}` is a built-in and cannot be imported"),
            ));
        }

        let resolved = resolve_path_segments(graph, module_funcs, path)
            .map_err(|msg| error_at(world, item, msg))?;

        match resolved {
            Resolved::Module(m) if m == module_id => {
                let label = display_path(path);
                return Err(error_at(
                    world,
                    item,
                    format!("module `{label}` cannot import itself"),
                ));
            }
            _ => {}
        }

        if bindings.contains_key(last) {
            return Err(error_at(
                world,
                item,
                format!("name `{last}` is imported twice"),
            ));
        }
        bindings.insert(last.to_string(), resolved.into());
    }

    graph.modules[module_id.0 as usize].bindings = bindings;
    Ok(())
}

/// Walk a multi-segment path through the module graph for a `use` declaration.
fn resolve_path_segments(
    graph: &ModuleGraph,
    module_funcs: &ModuleFuncs,
    segments: &[&str],
) -> Result<Resolved, String> {
    if segments.is_empty() {
        return Err("empty path".to_string());
    }

    // Walk segments[0..n-1] as a module chain; the resulting prefix must be
    // a loaded module (so we can look up the trailing segment as an item) or
    // — if the whole path is itself a loaded module — the path itself.
    if let Some(mod_id) = graph.lookup(segments) {
        return Ok(Resolved::Module(mod_id));
    }

    if segments.len() == 1 {
        return Err(format!("module `{}` not found", segments[0]));
    }

    let prefix = &segments[..segments.len() - 1];
    let owner = graph
        .lookup(prefix)
        .ok_or_else(|| format!("module `{}` not found", display_path(prefix)))?;
    let last = *segments.last().unwrap();
    let sig = module_funcs[owner.0 as usize].get(last).ok_or_else(|| {
        format!(
            "module `{}` has no item `{last}`",
            display_path(prefix)
        )
    })?;
    if !sig.is_pub {
        return Err(format!(
            "function `{last}` in module `{}` is not public",
            display_path(prefix)
        ));
    }
    Ok(Resolved::Func {
        node: sig.node,
        owner,
    })
}

fn display_path(segments: &[&str]) -> String {
    segments.join("::")
}

impl From<Resolved> for Binding {
    fn from(r: Resolved) -> Self {
        match r {
            Resolved::Module(m) => Binding::Module(m),
            Resolved::Func { node, owner } => Binding::Func { node, owner },
        }
    }
}

fn mangle_name(mod_path: &[String], fn_name: &str) -> String {
    let mut s = String::from("ecs");
    for seg in mod_path {
        s.push_str("__");
        s.push_str(seg);
    }
    s.push_str("__");
    s.push_str(fn_name);
    s
}

fn type_from_node(world: &mut AstWorld<'_>, id: NodeId) -> AnalysisResult<TypeInfo> {
    let ty = match *world.kind(id) {
        NodeKind::TypeName("int") => TypeInfo::Int,
        NodeKind::TypeName("float") => TypeInfo::Float,
        NodeKind::TypeName("bool") => TypeInfo::Bool,
        NodeKind::TypeName("str") => TypeInfo::Str,
        NodeKind::TypeName(name) => {
            return Err(error_at(world, id, format!("unknown type `{name}`")));
        }
        _ => return Err(error_at(world, id, "expected type name")),
    };
    world.types.insert(id, ty.clone());
    Ok(ty)
}

fn error_at(world: &AstWorld<'_>, id: NodeId, message: impl Into<String>) -> AnalysisError {
    AnalysisError::new(Some(world.span(id)), message)
}

struct Analyzer<'w, 'arena, 'g> {
    world: &'w mut AstWorld<'arena>,
    graph: &'g ModuleGraph,
    module: ModuleId,
    module_funcs: &'g ModuleFuncs,
    scopes: Vec<HashMap<String, Local>>,
}

impl<'w, 'arena, 'g> Analyzer<'w, 'arena, 'g> {
    fn check_program(&mut self) -> AnalysisResult<()> {
        let root = self.graph.modules[self.module.0 as usize].root;
        let items = match *self.world.kind(root) {
            NodeKind::Program(items) => items,
            _ => return Err(self.error(root, "root must be a Program node")),
        };

        for &item in items {
            if matches!(*self.world.kind(item), NodeKind::FnDecl { .. }) {
                self.check_function(item)?;
            }
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
            | NodeKind::Path { .. }
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
            | NodeKind::UseDecl { .. }
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
            NodeKind::Path { .. } => {
                return Err(self.error(id, "module paths are only valid as call targets"));
            }
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
        // R3: callee is always a Path. Resolve via this module's bindings and
        // the graph; lookup is uniform from depth 1 to arbitrary depth.
        let NodeKind::Path { segments } = *self.world.kind(callee) else {
            return Err(self.error(callee, "callee must be a function path"));
        };

        let (target_node, owner) = self.resolve_call_path(callee, segments)?;
        // Borrow sig from module_funcs (lifetime 'g, independent of `self`)
        // so we can call &mut self methods while reading sig fields.
        let module_funcs: &'g ModuleFuncs = self.module_funcs;
        let sig: &'g FuncSig = module_funcs[owner.0 as usize]
            .values()
            .find(|s| s.node == target_node)
            .ok_or_else(|| self.error(callee, "internal: resolved function has no signature"))?;
        let display_name = display_path(segments);

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
                    "function `{display_name}` expects {} argument(s), got {}",
                    sig.params.len(),
                    args.len()
                ),
            ));
        }

        for (&arg, expected) in args.iter().zip(sig.params.iter()) {
            let actual = self.check_expr(arg)?;
            self.require_assignable(arg, expected, &actual)?;
        }

        Ok(sig.ret.clone())
    }

    /// Resolve a call-site path to a function node and its owning module.
    ///
    /// Resolution order:
    ///   1. Same-module function (single segment only — locals are checked elsewhere).
    ///   2. Local binding from a `use` decl. `Func` is callable as a bare name;
    ///      `Module(m)` rebases the rest of the walk to start at `m`'s path.
    ///   3. Absolute path through the module graph: `segments[0]` must name a
    ///      loaded top-level module (or a namespace prefix that is one).
    ///
    /// Once a starting module is established, middle segments walk further
    /// into the namespace tree (each step must be a known prefix) and the
    /// final segment must be a public function in the resolved module.
    fn resolve_call_path(
        &self,
        callee: NodeId,
        segments: &[&'arena str],
    ) -> AnalysisResult<(NodeId, ModuleId)> {
        if segments.is_empty() {
            return Err(self.error(callee, "empty path"));
        }

        let module = &self.graph.modules[self.module.0 as usize];

        // (1) Single-segment, same-module function.
        if segments.len() == 1 {
            let name = segments[0];
            if let Some(sig) = self.module_funcs[self.module.0 as usize].get(name) {
                return Ok((sig.node, self.module));
            }
            // (2) Local `use` binding: must be a Func (Module here would be
            // a bare module name used in value position, not callable).
            if let Some(binding) = module.bindings.get(name) {
                return match *binding {
                    Binding::Func { node, owner } => Ok((node, owner)),
                    Binding::Module(_) => Err(self.error(
                        callee,
                        format!("`{name}` is a module, not a function"),
                    )),
                };
            }
            return Err(self.error(callee, format!("undefined function `{name}`")));
        }

        // (2) Local binding rebase: `use math::geometry;` binds `geometry` to
        // Module(geo); a path `geometry::area(...)` continues from geo's path.
        let head = segments[0];
        let (start_path, rest): (Vec<String>, &[&str]) =
            if let Some(Binding::Module(m)) = module.bindings.get(head).copied() {
                (
                    self.graph.modules[m.0 as usize].mod_path.clone(),
                    &segments[1..],
                )
            } else if let Some(Binding::Func { .. }) = module.bindings.get(head).copied() {
                return Err(self.error(
                    callee,
                    format!("`{head}` is a function, not a module"),
                ));
            } else if self.graph.is_namespace(&[head]) {
                // (3) Absolute: `segments[0]` is a top-level loaded module or namespace.
                (vec![head.to_string()], &segments[1..])
            } else {
                return Err(self.error(callee, format!("module `{head}` not found")));
            };

        // Walk remaining segments through the namespace tree. All but the
        // last must extend a known prefix; the last must be a public function
        // in the resolved module.
        let mut current_path = start_path;
        for &seg in &rest[..rest.len().saturating_sub(1)] {
            current_path.push(seg.to_string());
            if !self.graph.is_namespace(&current_path) {
                return Err(self.error(
                    callee,
                    format!("module `{}` not found", current_path.join("::")),
                ));
            }
        }

        let owner = self
            .graph
            .lookup(&current_path)
            .ok_or_else(|| {
                self.error(
                    callee,
                    format!(
                        "`{}` is a namespace, not a module with items",
                        current_path.join("::")
                    ),
                )
            })?;

        let item = *rest
            .last()
            .expect("multi-segment path always has a trailing item segment");
        let owner_label = current_path.join("::");
        let sig = self.module_funcs[owner.0 as usize].get(item).ok_or_else(|| {
            self.error(
                callee,
                format!("module `{owner_label}` has no item `{item}`"),
            )
        })?;
        // Same-module access (e.g. `math::abs` from inside math.ecs) doesn't
        // require `pub`; cross-module access does.
        if owner != self.module && !sig.is_pub {
            return Err(self.error(
                callee,
                format!("function `{item}` in module `{owner_label}` is not public"),
            ));
        }
        Ok((sig.node, owner))
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
        type_from_node(self.world, id)
    }

    fn define_local(&mut self, id: NodeId, name: &'arena str, ty: TypeInfo) -> AnalysisResult<()> {
        let scope = self.scopes.last_mut().expect("scope stack is empty");
        if scope.contains_key(name) {
            return Err(self.error(id, format!("duplicate binding `{name}`")));
        }
        scope.insert(name.to_string(), Local { decl: id, ty });
        Ok(())
    }

    fn resolve_local(&self, name: &str) -> Option<Local> {
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
