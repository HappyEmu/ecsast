use std::collections::HashMap;
use std::fmt;

use crate::ast::{AstWorld, BinOp, NodeId, NodeKind, UnaryOp};

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
            Value::Int(n)   => write!(f, "{n}"),
            Value::Float(x) => write!(f, "{x}"),
            Value::Bool(b)  => write!(f, "{b}"),
            Value::Str(s)   => write!(f, "{s}"),
            Value::Unit     => write!(f, "()"),
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

// ---------------------------------------------------------------------------
// Execution environment
// ---------------------------------------------------------------------------

pub struct Env {
    scopes: Vec<HashMap<String, Value>>,
    fns: HashMap<String, (Vec<NodeId>, NodeId)>,
}

impl Env {
    fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            fns: HashMap::new(),
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn define(&mut self, name: &str, value: Value) {
        self.scopes.last_mut().unwrap().insert(name.to_string(), value);
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
// Public entry point
// ---------------------------------------------------------------------------

pub fn run_program(world: &AstWorld<'_>, root: NodeId) -> Value {
    let mut env = Env::new();

    // Register all top-level FnDecls
    let items = match world.kind(root) {
        NodeKind::Program(items) => *items,
        _ => panic!("root must be a Program node"),
    };
    for item in items.iter().copied() {
        if let NodeKind::FnDecl { name, params, body, .. } = world.kind(item) {
            env.fns.insert(name.to_string(), (params.to_vec(), *body));
        }
    }

    // Look up and call main
    let (params, body) = env.fns.get("main")
        .expect("no main function found")
        .clone();
    assert!(params.is_empty(), "main must take no parameters");

    match eval_block(world, body, &mut env) {
        Flow::Val(v) | Flow::Ret(v) => v,
    }
}

// ---------------------------------------------------------------------------
// Core evaluator
// ---------------------------------------------------------------------------

fn eval(world: &AstWorld<'_>, id: NodeId, env: &mut Env) -> Flow {
    match *world.kind(id) {
        NodeKind::IntLit(n)    => Flow::Val(Value::Int(n)),
        NodeKind::FloatLit(f)  => Flow::Val(Value::Float(f)),
        NodeKind::BoolLit(b)   => Flow::Val(Value::Bool(b)),
        NodeKind::StringLit(s) => Flow::Val(Value::Str(s.to_string())),

        NodeKind::Ident(name) => Flow::Val(env.get(name)),

        NodeKind::BinOp { op, lhs, rhs } => {
            let l = match eval(world, lhs, env) { Flow::Val(v) | Flow::Ret(v) => v };
            let r = match eval(world, rhs, env) { Flow::Val(v) | Flow::Ret(v) => v };
            Flow::Val(apply_binop(op, l, r))
        }

        NodeKind::UnaryOp { op, operand } => {
            let v = match eval(world, operand, env) { Flow::Val(v) | Flow::Ret(v) => v };
            Flow::Val(apply_unary(op, v))
        }

        NodeKind::Call { callee, args } => {
            // Extract function name
            let fn_name = match world.kind(callee) {
                NodeKind::Ident(name) => *name,
                _ => panic!("callee must be an identifier"),
            };

            // Evaluate arguments
            let mut arg_vals = Vec::new();
            for &a in args {
                let v = match eval(world, a, env) { Flow::Val(v) | Flow::Ret(v) => v };
                arg_vals.push(v);
            }

            // Built-in: print
            if fn_name == "print" {
                let s = arg_vals.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ");
                println!("{s}");
                return Flow::Val(Value::Unit);
            }

            // User-defined function
            let (param_ids, body) = env.fns
                .get(fn_name)
                .unwrap_or_else(|| panic!("undefined function: {fn_name}"))
                .clone();

            env.push_scope();
            for (&param_id, val) in param_ids.iter().zip(arg_vals) {
                if let NodeKind::Param { name, .. } = world.kind(param_id) {
                    env.define(name, val);
                }
            }
            let result = eval_block(world, body, env);
            env.pop_scope();

            match result {
                Flow::Val(v) | Flow::Ret(v) => Flow::Val(v),
            }
        }

        NodeKind::LetStmt { name, init, .. } => {
            let val = match init {
                Some(init_id) => match eval(world, init_id, env) {
                    Flow::Val(v) | Flow::Ret(v) => v,
                },
                None => Value::Unit,
            };
            env.define(name, val);
            Flow::Val(Value::Unit)
        }

        NodeKind::AssignStmt { target, value } => {
            let name = match world.kind(target) {
                NodeKind::Ident(n) => *n,
                _ => panic!("assignment target must be an identifier"),
            };
            let val = match eval(world, value, env) {
                Flow::Val(v) | Flow::Ret(v) => v,
            };
            env.assign(name, val);
            Flow::Val(Value::Unit)
        }

        NodeKind::ReturnStmt(opt) => {
            let val = match opt {
                Some(expr) => match eval(world, expr, env) {
                    Flow::Val(v) | Flow::Ret(v) => v,
                },
                None => Value::Unit,
            };
            Flow::Ret(val)
        }

        NodeKind::IfStmt { cond, then_block, else_block } => {
            let cond_val = match eval(world, cond, env) {
                Flow::Val(v) | Flow::Ret(v) => v,
            };
            match cond_val {
                Value::Bool(true)  => eval(world, then_block, env),
                Value::Bool(false) => match else_block {
                    Some(eb) => eval(world, eb, env),
                    None     => Flow::Val(Value::Unit),
                },
                _ => panic!("if condition must be a boolean"),
            }
        }

        NodeKind::WhileStmt { cond, body } => {
            loop {
                let cond_val = match eval(world, cond, env) {
                    Flow::Val(v) | Flow::Ret(v) => v,
                };
                match cond_val {
                    Value::Bool(false) => break,
                    Value::Bool(true)  => {
                        match eval_block(world, body, env) {
                            Flow::Val(_)    => {}
                            Flow::Ret(v)    => return Flow::Ret(v),
                        }
                    }
                    _ => panic!("while condition must be a boolean"),
                }
            }
            Flow::Val(Value::Unit)
        }

        NodeKind::Block(_) => eval_block(world, id, env),

        NodeKind::Program(_)
        | NodeKind::FnDecl { .. }
        | NodeKind::Param { .. }
        | NodeKind::TypeName(_) => {
            panic!("cannot evaluate {:?} directly", world.kind(id))
        }
    }
}

// ---------------------------------------------------------------------------
// Block evaluator — manages its own scope
// ---------------------------------------------------------------------------

fn eval_block(world: &AstWorld<'_>, id: NodeId, env: &mut Env) -> Flow {
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
        // Float arithmetic
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Value::Float(a + b),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Value::Float(a - b),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Value::Float(a * b),
        (BinOp::Div, Value::Float(a), Value::Float(b)) => Value::Float(a / b),
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
        (BinOp::Or,  Value::Bool(a), Value::Bool(b)) => Value::Bool(a || b),
        // String concat
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Value::Str(a + &b),
        // Type error
        (op, l, r) => panic!("type error: cannot apply {op:?} to {l:?} and {r:?}"),
    }
}

fn apply_unary(op: UnaryOp, v: Value) -> Value {
    match (op, v) {
        (UnaryOp::Neg, Value::Int(n))   => Value::Int(-n),
        (UnaryOp::Neg, Value::Float(f)) => Value::Float(-f),
        (UnaryOp::Not, Value::Bool(b))  => Value::Bool(!b),
        (op, v) => panic!("type error: cannot apply {op:?} to {v:?}"),
    }
}
