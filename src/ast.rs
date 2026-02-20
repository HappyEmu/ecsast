use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap};

use crate::span::Span;

// ---------------------------------------------------------------------------
// Entity
// ---------------------------------------------------------------------------

slotmap::new_key_type! {
    /// An AST node entity, identified by a slotmap key.
    pub struct NodeId;
}

// ---------------------------------------------------------------------------
// Built-in functions
//
// The parser resolves known built-in names at parse time and stores them as
// `NodeKind::BuiltinCall` rather than `NodeKind::Call`.  Adding a new
// built-in only requires a new variant here plus arms in the codegen and
// interpreter dispatch functions — no struct fields or if/else chains.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    Print,
    Argc,
    Arg,
}

impl Builtin {
    /// Return the `Builtin` variant for a given function name, or `None` if
    /// the name does not name a built-in.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "print" => Some(Self::Print),
            "argc" => Some(Self::Argc),
            "arg" => Some(Self::Arg),
            _ => None,
        }
    }
}

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
    BinOp {
        op: BinOp,
        lhs: NodeId,
        rhs: NodeId,
    },
    UnaryOp {
        op: UnaryOp,
        operand: NodeId,
    },
    Call {
        callee: NodeId,
        args: &'arena [NodeId],
    },
    /// A call to a language built-in resolved at parse time.
    /// Avoids string comparisons at codegen / interpreter time.
    BuiltinCall {
        builtin: Builtin,
        args: &'arena [NodeId],
    },

    // Statements
    LetStmt {
        name: &'arena str,
        ty: Option<NodeId>,
        init: Option<NodeId>,
    },
    AssignStmt {
        target: NodeId,
        value: NodeId,
    },
    ReturnStmt(Option<NodeId>),
    IfStmt {
        cond: NodeId,
        then_block: NodeId,
        else_block: Option<NodeId>,
    },
    WhileStmt {
        cond: NodeId,
        body: NodeId,
    },
    Block(&'arena [NodeId]),

    // Items
    FnDecl {
        name: &'arena str,
        params: &'arena [NodeId],
        ret_ty: Option<NodeId>,
        body: NodeId,
        inline: bool,
    },
    Param {
        name: &'arena str,
        ty: Option<NodeId>,
    },

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
    Pow,
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
    Fn {
        params: Vec<TypeInfo>,
        ret: Box<TypeInfo>,
    },
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
    // --- Eagerly populated during parsing ---
    pub kinds: SlotMap<NodeId, NodeKind<'arena>>,
    pub spans: SecondaryMap<NodeId, Span>,

    // --- Lazily populated by later passes ---
    /// Resolved type for a node (type-checker pass).
    pub types: SparseSecondaryMap<NodeId, TypeInfo>,
    /// Parent node (parent-link pass).
    pub parents: SecondaryMap<NodeId, NodeId>,
    /// Name-resolution: `Ident` node → declaration node.
    pub resolved: SecondaryMap<NodeId, NodeId>,
}

impl<'arena> AstWorld<'arena> {
    pub fn new() -> Self {
        Self {
            kinds: SlotMap::with_key(),
            spans: SecondaryMap::new(),
            types: SparseSecondaryMap::new(),
            parents: SecondaryMap::new(),
            resolved: SecondaryMap::new(),
        }
    }

    /// Allocate a new node with a kind and source span (eagerly populated).
    pub fn alloc(&mut self, kind: NodeKind<'arena>, span: Span) -> NodeId {
        let id = self.kinds.insert(kind);
        self.spans.insert(id, span);
        id
    }

    pub fn kind(&self, id: NodeId) -> &NodeKind<'arena> {
        &self.kinds[id]
    }

    pub fn span(&self, id: NodeId) -> Span {
        self.spans[id]
    }
}
