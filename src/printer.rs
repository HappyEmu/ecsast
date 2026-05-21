use crate::ast::{AstWorld, NodeId, NodeKind};

pub fn print_ast(world: &AstWorld<'_>, id: NodeId, indent: usize) {
    let pad = "  ".repeat(indent);
    let sp = world.span(id);
    let head = format!("[{}..{}]", sp.start, sp.end);

    let ty = world
        .types
        .get(id)
        .map(|t| format!(" :: {t:?}"))
        .unwrap_or_default();

    match world.kind(id) {
        NodeKind::Program(items) => {
            println!("{pad}Program {head}");
            for &item in *items {
                print_ast(world, item, indent + 1);
            }
        }
        NodeKind::FnDecl {
            name,
            params,
            ret_ty,
            body,
            inline,
            is_pub,
        } => {
            let inl = if *inline { " (inline)" } else { "" };
            let vis = if *is_pub { "pub " } else { "" };
            let mangled = world
                .mangled_names
                .get(id)
                .map(|m| format!(" = {m}"))
                .unwrap_or_default();
            println!("{pad}{vis}FnDecl `{name}`{mangled}{inl}{ty} {head}");
            for &p in *params {
                print_ast(world, p, indent + 1);
            }
            if let Some(ty_node) = ret_ty {
                print_ast(world, *ty_node, indent + 1);
            }
            print_ast(world, *body, indent + 1);
        }
        NodeKind::UseDecl { path } => {
            println!("{pad}Use `{}` {head}", path.join("::"));
        }
        NodeKind::Path { segments } => {
            let resolved = world
                .resolved
                .get(id)
                .map(|r| format!(" -> {r:?}"))
                .unwrap_or_default();
            println!("{pad}Path `{}`{resolved}{ty} {head}", segments.join("::"));
        }
        NodeKind::Param { name, ty: ty_node } => {
            println!("{pad}Param `{name}`{ty} {head}");
            if let Some(t) = ty_node {
                print_ast(world, *t, indent + 1);
            }
        }
        NodeKind::Block(stmts) => {
            println!("{pad}Block {head}");
            for &stmt in *stmts {
                print_ast(world, stmt, indent + 1);
            }
        }
        NodeKind::LetStmt { name, ty: ty_node, init } => {
            println!("{pad}Let `{name}`{ty} {head}");
            if let Some(t) = ty_node {
                print_ast(world, *t, indent + 1);
            }
            if let Some(i) = init {
                print_ast(world, *i, indent + 1);
            }
        }
        NodeKind::AssignStmt { target, value } => {
            println!("{pad}Assign {head}");
            print_ast(world, *target, indent + 1);
            print_ast(world, *value, indent + 1);
        }
        NodeKind::ReturnStmt(val) => {
            println!("{pad}Return {head}");
            if let Some(v) = val {
                print_ast(world, *v, indent + 1);
            }
        }
        NodeKind::IfStmt {
            cond,
            then_block,
            else_block,
        } => {
            println!("{pad}If {head}");
            print_ast(world, *cond, indent + 1);
            print_ast(world, *then_block, indent + 1);
            if let Some(eb) = else_block {
                print_ast(world, *eb, indent + 1);
            }
        }
        NodeKind::WhileStmt { cond, body } => {
            println!("{pad}While {head}");
            print_ast(world, *cond, indent + 1);
            print_ast(world, *body, indent + 1);
        }
        NodeKind::BinOp { op, lhs, rhs } => {
            println!("{pad}BinOp {op:?}{ty} {head}");
            print_ast(world, *lhs, indent + 1);
            print_ast(world, *rhs, indent + 1);
        }
        NodeKind::UnaryOp { op, operand } => {
            println!("{pad}UnaryOp {op:?}{ty} {head}");
            print_ast(world, *operand, indent + 1);
        }
        NodeKind::Call { callee, args } => {
            println!("{pad}Call{ty} {head}");
            print_ast(world, *callee, indent + 1);
            for &a in *args {
                print_ast(world, a, indent + 1);
            }
        }
        NodeKind::BuiltinCall { builtin, args } => {
            println!("{pad}BuiltinCall({builtin:?}){ty} {head}");
            for &a in *args {
                print_ast(world, a, indent + 1);
            }
        }
        NodeKind::IntLit(n) => println!("{pad}IntLit({n}){ty} {head}"),
        NodeKind::FloatLit(f) => println!("{pad}FloatLit({f}){ty} {head}"),
        NodeKind::BoolLit(b) => println!("{pad}BoolLit({b}){ty} {head}"),
        NodeKind::StringLit(s) => println!("{pad}StringLit({s:?}){ty} {head}"),
        NodeKind::Ident(name) => {
            let resolved = world
                .resolved
                .get(id)
                .map(|r| format!(" -> {r:?}"))
                .unwrap_or_default();
            println!("{pad}Ident(`{name}`){resolved}{ty} {head}");
        }
        NodeKind::TypeName(name) => println!("{pad}Type(`{name}`) {head}"),
    }
}
