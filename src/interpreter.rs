use std::collections::HashMap;
use std::fmt;
use std::io::Write;

use crate::ast::{AstWorld, BinOp, Builtin, NodeId, NodeKind, UnaryOp};
use crate::modules::ModuleGraph;

// ---------------------------------------------------------------------------
// Runtime values
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Unit,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{n}"),
            Value::Float(x) => write!(f, "{x}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Str(s) => write!(f, "{s}"),
            Value::Unit => write!(f, "()"),
        }
    }
}

// ---------------------------------------------------------------------------
// Control-flow signal (private)
// ---------------------------------------------------------------------------

enum Flow {
    Val(Value),
    Ret(Value),
}

impl Flow {
    fn into_value(self) -> Value {
        match self {
            Flow::Val(v) | Flow::Ret(v) => v,
        }
    }
}

// ---------------------------------------------------------------------------
// Execution environment
// ---------------------------------------------------------------------------

pub struct Env<'w, 'arena> {
    scopes: Vec<HashMap<String, Value>>,
    /// Function table keyed by arena-allocated mangled name.
    fns: HashMap<&'arena str, (&'arena [NodeId], NodeId)>,
    /// Command-line arguments visible to `argc()` / `arg(i)`.
    args: Vec<String>,
    out: &'w mut dyn Write,
}

impl<'w, 'arena> Env<'w, 'arena> {
    fn new(args: Vec<String>, out: &'w mut dyn Write) -> Self {
        Self {
            scopes: vec![HashMap::new()],
            fns: HashMap::new(),
            args,
            out,
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn define(&mut self, name: &str, value: Value) {
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), value);
    }

    fn get(&self, name: &str) -> Value {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return v.clone();
            }
        }
        panic!("undefined variable: {name}");
    }

    fn assign(&mut self, name: &str, value: Value) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(name) {
                scope.insert(name.to_string(), value);
                return;
            }
        }
        panic!("assignment to undefined variable: {name}");
    }
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Run a program (multi-module) and capture output into the provided writer.
/// No command-line arguments are visible — `argc()` returns `1` (program
/// name only). Use [`run_with_args_and_output`] to pass argv.
pub fn run_with_output<'arena, W: Write>(
    world: &AstWorld<'arena>,
    graph: &ModuleGraph,
    out: &mut W,
) -> Value {
    run_with_args_and_output(world, graph, vec!["<program>".to_string()], out)
}

/// Run a program with an explicit `argv`. `args[0]` is the program name,
/// matching the C/codegen convention.
pub fn run_with_args_and_output<'arena, W: Write>(
    world: &AstWorld<'arena>,
    graph: &ModuleGraph,
    args: Vec<String>,
    out: &mut W,
) -> Value {
    let mut env: Env<'_, 'arena> = Env::new(args, out);

    // Register every FnDecl across every module, keyed by mangled name.
    for module in &graph.modules {
        let items = match world.kind(module.root) {
            NodeKind::Program(items) => *items,
            _ => panic!("module root must be a Program node"),
        };
        for item in items.iter().copied() {
            if let NodeKind::FnDecl { params, body, .. } = world.kind(item) {
                env.fns.insert(world.mangled(item), (*params, *body));
            }
        }
    }

    // Entry-module `main` is mangled to "main" by the semantic pass.
    let (_params, body) = *env.fns.get("main").expect("no main function found");

    match eval_block(world, body, &mut env) {
        Flow::Val(v) | Flow::Ret(v) => v,
    }
}

/// Run a program, printing output to stdout and reading argv from
/// `std::env::args()`.
pub fn run<'arena>(world: &AstWorld<'arena>, graph: &ModuleGraph) -> Value {
    let args: Vec<String> = std::env::args().collect();
    run_with_args_and_output(world, graph, args, &mut std::io::stdout())
}

// ---------------------------------------------------------------------------
// Core evaluator
// ---------------------------------------------------------------------------

fn eval<'arena>(world: &AstWorld<'arena>, id: NodeId, env: &mut Env<'_, 'arena>) -> Flow {
    match *world.kind(id) {
        NodeKind::IntLit(n) => Flow::Val(Value::Int(n)),
        NodeKind::FloatLit(f) => Flow::Val(Value::Float(f)),
        NodeKind::BoolLit(b) => Flow::Val(Value::Bool(b)),
        NodeKind::StringLit(s) => Flow::Val(Value::Str(s.to_string())),
        NodeKind::Ident(name) => Flow::Val(env.get(name)),
        NodeKind::BinOp { op, lhs, rhs } => eval_binop(world, env, op, lhs, rhs),
        NodeKind::UnaryOp { op, operand } => eval_unaryop(world, env, op, operand),
        NodeKind::Call { callee, args } => eval_call(world, env, callee, args),
        NodeKind::BuiltinCall { builtin, args } => eval_builtin_call(world, env, builtin, args),
        NodeKind::LetStmt { name, init, .. } => eval_let(world, env, name, init),
        NodeKind::AssignStmt { target, value } => eval_assign(world, env, target, value),
        NodeKind::ReturnStmt(opt) => eval_return(world, env, opt),
        NodeKind::IfStmt {
            cond,
            then_block,
            else_block,
        } => eval_if(world, env, cond, then_block, else_block),
        NodeKind::WhileStmt { cond, body } => eval_while(world, env, cond, body),
        NodeKind::Block(_) => eval_block(world, id, env),
        NodeKind::Program(_)
        | NodeKind::FnDecl { .. }
        | NodeKind::Param { .. }
        | NodeKind::Path { .. }
        | NodeKind::UseDecl { .. }
        | NodeKind::TypeName(_) => {
            panic!("cannot evaluate {:?} directly", world.kind(id))
        }
    }
}

// ---------------------------------------------------------------------------
// Per-node evaluators
// ---------------------------------------------------------------------------

fn eval_binop<'arena>(
    world: &AstWorld<'arena>,
    env: &mut Env<'_, 'arena>,
    op: BinOp,
    lhs: NodeId,
    rhs: NodeId,
) -> Flow {
    let l = eval(world, lhs, env).into_value();
    let r = eval(world, rhs, env).into_value();
    Flow::Val(apply_binop(op, l, r))
}

fn eval_unaryop<'arena>(
    world: &AstWorld<'arena>,
    env: &mut Env<'_, 'arena>,
    op: UnaryOp,
    operand: NodeId,
) -> Flow {
    let v = eval(world, operand, env).into_value();
    Flow::Val(apply_unary(op, v))
}

fn eval_call<'arena>(
    world: &AstWorld<'arena>,
    env: &mut Env<'_, 'arena>,
    callee: NodeId,
    args: &[NodeId],
) -> Flow {
    // R4: callee is always a Path; semantic stored target FnDecl in world.resolved,
    // and the mangled name lives in world.mangled_names. Interpreter looks up
    // the same mangled name in env.fns.
    let target_fn = world.resolved[callee];
    let mangled = world.mangled(target_fn);

    let arg_vals: Vec<Value> = args
        .iter()
        .map(|&a| eval(world, a, env).into_value())
        .collect();

    let (param_ids, body) = *env
        .fns
        .get(mangled)
        .unwrap_or_else(|| panic!("undefined function: {mangled}"));

    env.push_scope();
    for (&param_id, val) in param_ids.iter().zip(arg_vals) {
        if let NodeKind::Param { name, .. } = world.kind(param_id) {
            env.define(name, val);
        }
    }
    let result = eval_block(world, body, env);
    env.pop_scope();

    Flow::Val(result.into_value())
}

/// Evaluate a call to a language built-in.
fn eval_builtin_call<'arena>(
    world: &AstWorld<'arena>,
    env: &mut Env<'_, 'arena>,
    builtin: Builtin,
    args: &[NodeId],
) -> Flow {
    match builtin {
        Builtin::Print => {
            let arg_vals: Vec<Value> = args
                .iter()
                .map(|&a| eval(world, a, env).into_value())
                .collect();
            let s = arg_vals
                .iter()
                .map(Value::to_string)
                .collect::<Vec<_>>()
                .join(" ");
            writeln!(env.out, "{s}").expect("write failed");
            Flow::Val(Value::Unit)
        }
        Builtin::Argc => Flow::Val(Value::Int(env.args.len() as i64)),
        Builtin::Arg => {
            assert!(args.len() == 1, "arg() takes exactly 1 argument");
            let idx = match eval(world, args[0], env).into_value() {
                Value::Int(n) => n,
                other => panic!("arg() index must be int, got {other:?}"),
            };
            let s = env
                .args
                .get(idx as usize)
                .unwrap_or_else(|| panic!("arg({idx}) out of bounds (argc = {})", env.args.len()))
                .clone();
            Flow::Val(Value::Str(s))
        }
    }
}

fn eval_let<'arena>(world: &AstWorld<'arena>, env: &mut Env<'_, 'arena>, name: &str, init: Option<NodeId>) -> Flow {
    let val = match init {
        Some(init_id) => eval(world, init_id, env).into_value(),
        None => Value::Unit,
    };
    env.define(name, val);
    Flow::Val(Value::Unit)
}

fn eval_assign<'arena>(world: &AstWorld<'arena>, env: &mut Env<'_, 'arena>, target: NodeId, value: NodeId) -> Flow {
    let name = match world.kind(target) {
        NodeKind::Ident(n) => *n,
        _ => panic!("assignment target must be an identifier"),
    };
    let val = eval(world, value, env).into_value();
    env.assign(name, val);
    Flow::Val(Value::Unit)
}

fn eval_return<'arena>(world: &AstWorld<'arena>, env: &mut Env<'_, 'arena>, opt: Option<NodeId>) -> Flow {
    let val = match opt {
        Some(expr) => eval(world, expr, env).into_value(),
        None => Value::Unit,
    };
    Flow::Ret(val)
}

fn eval_if<'arena>(
    world: &AstWorld<'arena>,
    env: &mut Env<'_, 'arena>,
    cond: NodeId,
    then_block: NodeId,
    else_block: Option<NodeId>,
) -> Flow {
    let cond_val = eval(world, cond, env).into_value();
    match cond_val {
        Value::Bool(true) => eval(world, then_block, env),
        Value::Bool(false) => match else_block {
            Some(eb) => eval(world, eb, env),
            None => Flow::Val(Value::Unit),
        },
        _ => panic!("if condition must be a boolean"),
    }
}

fn eval_while<'arena>(world: &AstWorld<'arena>, env: &mut Env<'_, 'arena>, cond: NodeId, body: NodeId) -> Flow {
    loop {
        let cond_val = eval(world, cond, env).into_value();
        match cond_val {
            Value::Bool(false) => break,
            Value::Bool(true) => match eval_block(world, body, env) {
                Flow::Val(_) => {}
                Flow::Ret(v) => return Flow::Ret(v),
            },
            _ => panic!("while condition must be a boolean"),
        }
    }
    Flow::Val(Value::Unit)
}

// ---------------------------------------------------------------------------
// Block evaluator — manages its own scope
// ---------------------------------------------------------------------------

fn eval_block<'arena>(world: &AstWorld<'arena>, id: NodeId, env: &mut Env<'_, 'arena>) -> Flow {
    let stmts = match world.kind(id) {
        NodeKind::Block(stmts) => *stmts,
        _ => panic!("eval_block called on non-Block node"),
    };

    env.push_scope();
    for stmt in stmts.iter().copied() {
        match eval(world, stmt, env) {
            Flow::Val(_) => {}
            Flow::Ret(v) => {
                env.pop_scope();
                return Flow::Ret(v);
            }
        }
    }
    env.pop_scope();
    Flow::Val(Value::Unit)
}

// ---------------------------------------------------------------------------
// Operator helpers
// ---------------------------------------------------------------------------

fn apply_binop(op: BinOp, l: Value, r: Value) -> Value {
    match (op, l, r) {
        // Int arithmetic
        (BinOp::Add, Value::Int(a), Value::Int(b)) => Value::Int(a + b),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Value::Int(a - b),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Value::Int(a * b),
        (BinOp::Div, Value::Int(a), Value::Int(b)) => Value::Int(a / b),
        (BinOp::Mod, Value::Int(a), Value::Int(b)) => Value::Int(a % b),
        (BinOp::Pow, Value::Int(a), Value::Int(b)) => Value::Int(a.pow(b as u32)),
        // Float arithmetic
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Value::Float(a + b),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Value::Float(a - b),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Value::Float(a * b),
        (BinOp::Div, Value::Float(a), Value::Float(b)) => Value::Float(a / b),
        (BinOp::Pow, Value::Float(a), Value::Float(b)) => Value::Float(a.powf(b)),
        // Int comparisons
        (BinOp::Eq, Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
        (BinOp::Ne, Value::Int(a), Value::Int(b)) => Value::Bool(a != b),
        (BinOp::Lt, Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
        (BinOp::Le, Value::Int(a), Value::Int(b)) => Value::Bool(a <= b),
        (BinOp::Gt, Value::Int(a), Value::Int(b)) => Value::Bool(a > b),
        (BinOp::Ge, Value::Int(a), Value::Int(b)) => Value::Bool(a >= b),
        // Bool comparisons
        (BinOp::Eq, Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
        (BinOp::Ne, Value::Bool(a), Value::Bool(b)) => Value::Bool(a != b),
        // Logical
        (BinOp::And, Value::Bool(a), Value::Bool(b)) => Value::Bool(a && b),
        (BinOp::Or, Value::Bool(a), Value::Bool(b)) => Value::Bool(a || b),
        // Bitwise
        (BinOp::BitAnd, Value::Int(a), Value::Int(b)) => Value::Int(a & b),
        (BinOp::BitOr,  Value::Int(a), Value::Int(b)) => Value::Int(a | b),
        (BinOp::BitXor, Value::Int(a), Value::Int(b)) => Value::Int(a ^ b),
        (BinOp::Shl,    Value::Int(a), Value::Int(b)) => Value::Int(a << b),
        (BinOp::Shr,    Value::Int(a), Value::Int(b)) => Value::Int(a >> b),
        // String concat
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Value::Str(a + &b),
        // Type error
        (op, l, r) => panic!("type error: cannot apply {op:?} to {l:?} and {r:?}"),
    }
}

fn apply_unary(op: UnaryOp, v: Value) -> Value {
    match (op, v) {
        (UnaryOp::Neg, Value::Int(n)) => Value::Int(-n),
        (UnaryOp::Neg, Value::Float(f)) => Value::Float(-f),
        (UnaryOp::Not, Value::Bool(b)) => Value::Bool(!b),
        (UnaryOp::BitNot, Value::Int(n)) => Value::Int(!n),
        (op, v) => panic!("type error: cannot apply {op:?} to {v:?}"),
    }
}
