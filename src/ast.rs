use std::collections::HashMap;

use crate::span::Span;

// ---------------------------------------------------------------------------
// Entity
// ---------------------------------------------------------------------------

/// An AST node entity, identified by a unique integer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);

// ---------------------------------------------------------------------------
// Core component: NodeKind
//
// Every node must have exactly one NodeKind.  All other components are
// optional and populated lazily by later passes.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub enum NodeKind<'arena> {
    // Literals
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(&'arena str),

    // Expressions
    Ident(&'arena str),
    BinOp { op: BinOp, lhs: NodeId, rhs: NodeId },
    UnaryOp { op: UnaryOp, operand: NodeId },
    Call { callee: NodeId, args: &'arena [NodeId] },

    // Statements
    LetStmt { name: &'arena str, ty: Option<NodeId>, init: Option<NodeId> },
    AssignStmt { target: NodeId, value: NodeId },
    ReturnStmt(Option<NodeId>),
    IfStmt { cond: NodeId, then_block: NodeId, else_block: Option<NodeId> },
    WhileStmt { cond: NodeId, body: NodeId },
    Block(&'arena [NodeId]),

    // Items
    FnDecl { name: &'arena str, params: &'arena [NodeId], ret_ty: Option<NodeId>, body: NodeId },
    Param { name: &'arena str, ty: Option<NodeId> },

    // Types
    TypeName(&'arena str),

    // Root
    Program(&'arena [NodeId]),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

// ---------------------------------------------------------------------------
// Lazy component: TypeInfo
//
// Populated by a type-checking pass, not by the parser.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeInfo {
    Int,
    Float,
    Bool,
    Str,
    Unit,
    Fn { params: Vec<TypeInfo>, ret: Box<TypeInfo> },
    Unknown,
}

// ---------------------------------------------------------------------------
// The ECS world
//
// Each field is one component store: HashMap<NodeId, ComponentData>.
//
// Components are populated:
//   - eagerly  during parsing   → kinds, spans
//   - lazily   by later passes  → types, parents, resolved
//
// A missing entry simply means "not yet computed".  Passes can populate
// a store independently without touching others.
// ---------------------------------------------------------------------------

pub struct AstWorld<'arena> {
    next_id: u32,

    // --- Eagerly populated during parsing ---
    pub kinds: HashMap<NodeId, NodeKind<'arena>>,
    pub spans: HashMap<NodeId, Span>,

    // --- Lazily populated by later passes ---
    /// Resolved type for a node (type-checker pass).
    pub types: HashMap<NodeId, TypeInfo>,
    /// Parent node (parent-link pass).
    pub parents: HashMap<NodeId, NodeId>,
    /// Name-resolution: `Ident` node → declaration node.
    pub resolved: HashMap<NodeId, NodeId>,
}

impl<'arena> AstWorld<'arena> {
    pub fn new() -> Self {
        Self {
            next_id: 0,
            kinds: HashMap::new(),
            spans: HashMap::new(),
            types: HashMap::new(),
            parents: HashMap::new(),
            resolved: HashMap::new(),
        }
    }

    /// Allocate a new node with a kind and source span (eagerly populated).
    pub fn alloc(&mut self, kind: NodeKind<'arena>, span: Span) -> NodeId {
        let id = NodeId(self.next_id);
        self.next_id += 1;
        self.kinds.insert(id, kind);
        self.spans.insert(id, span);
        id
    }

    pub fn kind(&self, id: NodeId) -> &NodeKind<'arena> {
        &self.kinds[&id]
    }

    pub fn span(&self, id: NodeId) -> Span {
        self.spans[&id]
    }
}
