use crate::ast::{AstWorld, NodeId, NodeKind};

pub fn print_ast(world: &AstWorld<'_>, id: NodeId, indent: usize) {
    let pad = "  ".repeat(indent);
    let sp = world.span(id);
    // Show the type annotation if it has been populated by a pass.
    let ty = world
        .types
        .get(id)
        .map(|t| format!("  :: {t:?}"))
        .unwrap_or_default();

    match world.kind(id) {
        NodeKind::Program(items) => {
            println!("{pad}Program [{s}..{e}]", s = sp.start, e = sp.end);
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
        } => {
            let inl = if *inline { " (inline)" } else { "" };
            println!("{pad}FnDecl `{name}`{inl} [{s}..{e}]", s = sp.start, e = sp.end);
            for &p in *params {
                print_ast(world, p, indent + 1);
            }
            if let Some(ty_node) = ret_ty {
                print_ast(world, *ty_node, indent + 1);
            }
            print_ast(world, *body, indent + 1);
        }
        NodeKind::Param { name, ty: ty_node } => {
            println!("{pad}Param `{name}` [{s}..{e}]", s = sp.start, e = sp.end);
            if let Some(t) = ty_node {
                print_ast(world, *t, indent + 1);
            }
        }
        NodeKind::Block(stmts) => {
            println!("{pad}Block [{s}..{e}]", s = sp.start, e = sp.end);
            for &stmt in *stmts {
                print_ast(world, stmt, indent + 1);
            }
        }
        NodeKind::LetStmt {
            name,
            ty: ty_node,
            init,
        } => {
            println!("{pad}Let `{name}` [{s}..{e}]", s = sp.start, e = sp.end);
            if let Some(t) = ty_node {
                print_ast(world, *t, indent + 1);
            }
            if let Some(i) = init {
                print_ast(world, *i, indent + 1);
            }
        }
        NodeKind::AssignStmt { target, value } => {
            println!("{pad}Assign [{s}..{e}]", s = sp.start, e = sp.end);
            print_ast(world, *target, indent + 1);
            print_ast(world, *value, indent + 1);
        }
        NodeKind::ReturnStmt(val) => {
            println!("{pad}Return [{s}..{e}]", s = sp.start, e = sp.end);
            if let Some(v) = val {
                print_ast(world, *v, indent + 1);
            }
        }
        NodeKind::IfStmt {
            cond,
            then_block,
            else_block,
        } => {
            println!("{pad}If [{s}..{e}]", s = sp.start, e = sp.end);
            print_ast(world, *cond, indent + 1);
            print_ast(world, *then_block, indent + 1);
            if let Some(eb) = else_block {
                print_ast(world, *eb, indent + 1);
            }
        }
        NodeKind::WhileStmt { cond, body } => {
            println!("{pad}While [{s}..{e}]", s = sp.start, e = sp.end);
            print_ast(world, *cond, indent + 1);
            print_ast(world, *body, indent + 1);
        }
        NodeKind::BinOp { op, lhs, rhs } => {
            println!("{pad}BinOp {op:?} [{s}..{e}]", s = sp.start, e = sp.end);
            print_ast(world, *lhs, indent + 1);
            print_ast(world, *rhs, indent + 1);
        }
        NodeKind::UnaryOp { op, operand } => {
            println!("{pad}UnaryOp {op:?} [{s}..{e}]", s = sp.start, e = sp.end);
            print_ast(world, *operand, indent + 1);
        }
        NodeKind::Call { callee, args } => {
            println!("{pad}Call [{s}..{e}]", s = sp.start, e = sp.end);
            print_ast(world, *callee, indent + 1);
            for &a in *args {
                print_ast(world, a, indent + 1);
            }
        }
        NodeKind::BuiltinCall { builtin, args } => {
            println!("{pad}BuiltinCall({builtin:?}) [{s}..{e}]", s = sp.start, e = sp.end);
            for &a in *args {
                print_ast(world, a, indent + 1);
            }
        }
        NodeKind::IntLit(n) => {
            println!("{pad}IntLit({n}){ty} [{s}..{e}]", s = sp.start, e = sp.end)
        }
        NodeKind::FloatLit(f) => println!(
            "{pad}FloatLit({f}){ty} [{s}..{e}]",
            s = sp.start,
            e = sp.end
        ),
        NodeKind::BoolLit(b) => {
            println!("{pad}BoolLit({b}){ty} [{s}..{e}]", s = sp.start, e = sp.end)
        }
        NodeKind::StringLit(s) => println!(
            "{pad}StringLit({s:?}){ty} [{st}..{e}]",
            st = sp.start,
            e = sp.end
        ),
        NodeKind::Ident(name) => println!(
            "{pad}Ident(`{name}`){ty} [{s}..{e}]",
            s = sp.start,
            e = sp.end
        ),
        NodeKind::TypeName(name) => {
            println!("{pad}Type(`{name}`) [{s}..{e}]", s = sp.start, e = sp.end)
        }
    }
}
