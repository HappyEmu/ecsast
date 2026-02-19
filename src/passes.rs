use crate::ast::{AstWorld, NodeId, NodeKind, TypeInfo};

// ---------------------------------------------------------------------------
// Pass: literal type annotation
//
// Populates the `types` component store for all literal nodes.
// Leaves every other component store untouched.
// ---------------------------------------------------------------------------

pub fn annotate_literal_types(world: &mut AstWorld<'_>) {
    let ids: Vec<NodeId> = world.kinds.keys().copied().collect();
    for id in ids {
        let ty = match &world.kinds[&id] {
            NodeKind::IntLit(_)    => Some(TypeInfo::Int),
            NodeKind::FloatLit(_)  => Some(TypeInfo::Float),
            NodeKind::BoolLit(_)   => Some(TypeInfo::Bool),
            NodeKind::StringLit(_) => Some(TypeInfo::Str),
            _                      => None,
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
        NodeKind::FnDecl { params, ret_ty, body, .. } => {
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
        NodeKind::IfStmt { cond, then_block, else_block } => {
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
