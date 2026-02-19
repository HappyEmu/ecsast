use bumpalo::Bump;

use crate::ast::{AstWorld, BinOp, NodeId, NodeKind, UnaryOp};
use crate::lexer::{Token, TokenKind};
use crate::span::Span;

// ---------------------------------------------------------------------------
// Parser
//
// A hand-written recursive-descent parser.
// Binary expressions are parsed with precedence climbing so that operator
// precedence and associativity are handled in a single, table-driven loop
// rather than one function level per precedence tier.
// ---------------------------------------------------------------------------

pub struct Parser<'src, 'arena> {
    tokens: &'src [Token],
    pos: usize,
    arena: &'arena Bump,
    pub world: AstWorld<'arena>,
}

// ---------------------------------------------------------------------------
// Precedence-climbing helpers
// ---------------------------------------------------------------------------

/// Binding power (precedence) for binary operators.
/// Returns `(left_bp, right_bp)` — right_bp > left_bp means right-associative.
fn infix_bp(kind: &TokenKind) -> Option<(u8, u8)> {
    let bp = match kind {
        TokenKind::PipePipe => (1, 2),                 // ||
        TokenKind::AmpAmp => (3, 4),                   // &&
        TokenKind::EqEq | TokenKind::BangEq => (5, 6), // == !=
        TokenKind::Lt | TokenKind::LtEq | TokenKind::Gt | TokenKind::GtEq => (7, 8), // < <= > >=
        TokenKind::Plus | TokenKind::Minus => (9, 10), // + -
        TokenKind::Star | TokenKind::Slash | TokenKind::Percent => (11, 12), // * / %
        _ => return None,
    };
    Some(bp)
}

fn token_to_binop(kind: &TokenKind) -> BinOp {
    match kind {
        TokenKind::Plus => BinOp::Add,
        TokenKind::Minus => BinOp::Sub,
        TokenKind::Star => BinOp::Mul,
        TokenKind::Slash => BinOp::Div,
        TokenKind::Percent => BinOp::Mod,
        TokenKind::EqEq => BinOp::Eq,
        TokenKind::BangEq => BinOp::Ne,
        TokenKind::Lt => BinOp::Lt,
        TokenKind::LtEq => BinOp::Le,
        TokenKind::Gt => BinOp::Gt,
        TokenKind::GtEq => BinOp::Ge,
        TokenKind::AmpAmp => BinOp::And,
        TokenKind::PipePipe => BinOp::Or,
        other => panic!("not a binary operator: {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// Core parser helpers
// ---------------------------------------------------------------------------

impl<'src, 'arena> Parser<'src, 'arena> {
    pub fn new(tokens: &'src [Token], arena: &'arena Bump) -> Self {
        Self {
            tokens,
            pos: 0,
            arena,
            world: AstWorld::new(),
        }
    }

    fn peek(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    fn peek_token(&self) -> &Token {
        &self.tokens[self.pos]
    }

    /// Consume the current token and return a clone of it.
    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    /// Advance only if the current token matches `expected` (by discriminant).
    fn eat(&mut self, expected: &TokenKind) -> bool {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Advance and return the token, panicking if the discriminant doesn't match.
    fn expect(&mut self, expected: &TokenKind) -> Token {
        if std::mem::discriminant(self.peek()) != std::mem::discriminant(expected) {
            panic!(
                "expected {:?} but got {:?} at span {:?}",
                expected,
                self.peek(),
                self.peek_token().span,
            );
        }
        self.advance()
    }

    fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.peek()) == std::mem::discriminant(kind)
    }

    // Shorthand span helpers
    fn start_span(&self) -> u32 {
        self.peek_token().span.start
    }

    fn end_of(&self, id: NodeId) -> u32 {
        self.world.span(id).end
    }
}

// ---------------------------------------------------------------------------
// Grammar
// ---------------------------------------------------------------------------

impl<'src, 'arena> Parser<'src, 'arena> {
    // ---- Top level ---------------------------------------------------------

    pub fn parse_program(&mut self) -> NodeId {
        let start = self.start_span();
        let mut items = Vec::new();
        while !self.at(&TokenKind::Eof) {
            items.push(self.parse_item());
        }
        let end = self.start_span(); // EOF position
        self.world.alloc(
            NodeKind::Program(self.arena.alloc_slice_copy(&items)),
            Span::new(start, end),
        )
    }

    fn parse_item(&mut self) -> NodeId {
        match self.peek() {
            TokenKind::Fn => self.parse_fn_decl(),
            other => panic!("expected top-level item, got {:?}", other),
        }
    }

    // ---- Function declaration -----------------------------------------------

    fn parse_fn_decl(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::Fn);

        let name = match self.advance().kind {
            TokenKind::Ident(s) => self.arena.alloc_str(&s),
            other => panic!("expected function name, got {:?}", other),
        };

        self.expect(&TokenKind::LParen);
        let mut params = Vec::new();
        while !self.at(&TokenKind::RParen) && !self.at(&TokenKind::Eof) {
            params.push(self.parse_param());
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RParen);

        let ret_ty = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type())
        } else {
            None
        };

        let body = self.parse_block();
        let end = self.end_of(body);
        self.world.alloc(
            NodeKind::FnDecl {
                name,
                params: self.arena.alloc_slice_copy(&params),
                ret_ty,
                body,
            },
            Span::new(start, end),
        )
    }

    fn parse_param(&mut self) -> NodeId {
        let start = self.start_span();
        let name = match self.advance().kind {
            TokenKind::Ident(s) => self.arena.alloc_str(&s),
            other => panic!("expected parameter name, got {:?}", other),
        };
        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.parse_type())
        } else {
            None
        };
        let end = self.start_span();
        self.world
            .alloc(NodeKind::Param { name, ty }, Span::new(start, end))
    }

    fn parse_type(&mut self) -> NodeId {
        let tok = self.advance();
        match tok.kind {
            TokenKind::Ident(name) => self
                .world
                .alloc(NodeKind::TypeName(self.arena.alloc_str(&name)), tok.span),
            other => panic!("expected type name, got {:?}", other),
        }
    }

    // ---- Block and statements ----------------------------------------------

    fn parse_block(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::LBrace);
        let mut stmts = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Eof) {
            stmts.push(self.parse_stmt());
        }
        let end = self.peek_token().span.end; // end of `}`
        self.expect(&TokenKind::RBrace);
        self.world.alloc(
            NodeKind::Block(self.arena.alloc_slice_copy(&stmts)),
            Span::new(start, end),
        )
    }

    fn parse_stmt(&mut self) -> NodeId {
        match self.peek() {
            TokenKind::Let => self.parse_let_stmt(),
            TokenKind::Return => self.parse_return_stmt(),
            TokenKind::If => self.parse_if_stmt(),
            TokenKind::While => self.parse_while_stmt(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_let_stmt(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::Let);

        let name = match self.advance().kind {
            TokenKind::Ident(s) => self.arena.alloc_str(&s),
            other => panic!("expected name after `let`, got {:?}", other),
        };

        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.parse_type())
        } else {
            None
        };

        let init = if self.eat(&TokenKind::Eq) {
            Some(self.parse_expr())
        } else {
            None
        };

        let end = self.start_span();
        self.eat(&TokenKind::Semicolon);
        self.world
            .alloc(NodeKind::LetStmt { name, ty, init }, Span::new(start, end))
    }

    fn parse_return_stmt(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::Return);

        let value = if !self.at(&TokenKind::Semicolon) && !self.at(&TokenKind::RBrace) {
            Some(self.parse_expr())
        } else {
            None
        };

        let end = self.start_span();
        self.eat(&TokenKind::Semicolon);
        self.world
            .alloc(NodeKind::ReturnStmt(value), Span::new(start, end))
    }

    fn parse_if_stmt(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::If);

        let cond = self.parse_expr();
        let then_block = self.parse_block();

        let else_block = if self.eat(&TokenKind::Else) {
            if self.at(&TokenKind::If) {
                Some(self.parse_if_stmt()) // else-if chain
            } else {
                Some(self.parse_block())
            }
        } else {
            None
        };

        let end = else_block
            .map(|n| self.end_of(n))
            .unwrap_or_else(|| self.end_of(then_block));

        self.world.alloc(
            NodeKind::IfStmt {
                cond,
                then_block,
                else_block,
            },
            Span::new(start, end),
        )
    }

    fn parse_while_stmt(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::While);
        let cond = self.parse_expr();
        let body = self.parse_block();
        let end = self.end_of(body);
        self.world
            .alloc(NodeKind::WhileStmt { cond, body }, Span::new(start, end))
    }

    /// An expression used as a statement; consumes an optional trailing `;`.
    fn parse_expr_stmt(&mut self) -> NodeId {
        let expr = self.parse_expr();
        // An assignment expression (`a = b`) is the statement form; anything
        // else can also appear as an expression-statement.
        self.eat(&TokenKind::Semicolon);
        expr
    }

    // ---- Expressions -------------------------------------------------------
    //
    // parse_expr → parse_assign → parse_binary(min_bp=0)
    //
    // Binary expressions use precedence climbing: a single recursive function
    // with a minimum binding-power parameter instead of one function per tier.
    // Assignment is handled separately because it is right-associative and
    // needs lvalue checking.

    pub fn parse_expr(&mut self) -> NodeId {
        self.parse_assign()
    }

    fn parse_assign(&mut self) -> NodeId {
        let lhs = self.parse_binary(0);

        if self.at(&TokenKind::Eq) {
            let start = self.world.span(lhs).start;
            self.advance(); // consume `=`
            let rhs = self.parse_assign(); // right-associative
            let end = self.end_of(rhs);
            self.world.alloc(
                NodeKind::AssignStmt {
                    target: lhs,
                    value: rhs,
                },
                Span::new(start, end),
            )
        } else {
            lhs
        }
    }

    /// Precedence-climbing binary expression parser.
    ///
    /// `min_bp` is the minimum *left* binding power we are willing to consume.
    /// Call with `min_bp = 0` to parse a full binary expression.
    fn parse_binary(&mut self, min_bp: u8) -> NodeId {
        let mut lhs = self.parse_unary();

        loop {
            let (l_bp, r_bp) = match infix_bp(self.peek()) {
                Some(bp) if bp.0 >= min_bp => bp,
                _ => break,
            };

            let op = token_to_binop(self.peek());
            let _ = l_bp; // consumed for documentation
            self.advance(); // consume the operator token

            let rhs = self.parse_binary(r_bp);

            let start = self.world.span(lhs).start;
            let end = self.end_of(rhs);
            lhs = self
                .world
                .alloc(NodeKind::BinOp { op, lhs, rhs }, Span::new(start, end));
        }

        lhs
    }

    fn parse_unary(&mut self) -> NodeId {
        match self.peek() {
            TokenKind::Minus => {
                let start = self.start_span();
                self.advance();
                let operand = self.parse_unary();
                let end = self.end_of(operand);
                self.world.alloc(
                    NodeKind::UnaryOp {
                        op: UnaryOp::Neg,
                        operand,
                    },
                    Span::new(start, end),
                )
            }
            TokenKind::Bang => {
                let start = self.start_span();
                self.advance();
                let operand = self.parse_unary();
                let end = self.end_of(operand);
                self.world.alloc(
                    NodeKind::UnaryOp {
                        op: UnaryOp::Not,
                        operand,
                    },
                    Span::new(start, end),
                )
            }
            _ => self.parse_postfix(),
        }
    }

    /// Postfix: function calls and (potentially) indexing, field access, etc.
    fn parse_postfix(&mut self) -> NodeId {
        let mut expr = self.parse_primary();

        loop {
            if self.at(&TokenKind::LParen) {
                let start = self.world.span(expr).start;
                self.advance(); // `(`
                let mut args = Vec::new();
                while !self.at(&TokenKind::RParen) && !self.at(&TokenKind::Eof) {
                    args.push(self.parse_expr());
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                let end = self.peek_token().span.end;
                self.expect(&TokenKind::RParen);
                expr = self.world.alloc(
                    NodeKind::Call {
                        callee: expr,
                        args: self.arena.alloc_slice_copy(&args),
                    },
                    Span::new(start, end),
                );
            } else {
                break;
            }
        }

        expr
    }

    fn parse_primary(&mut self) -> NodeId {
        let tok = self.advance();
        match tok.kind {
            TokenKind::Int(n) => self.world.alloc(NodeKind::IntLit(n), tok.span),
            TokenKind::Float(f) => self.world.alloc(NodeKind::FloatLit(f), tok.span),
            TokenKind::Bool(b) => self.world.alloc(NodeKind::BoolLit(b), tok.span),
            TokenKind::Str(s) => self
                .world
                .alloc(NodeKind::StringLit(self.arena.alloc_str(&s)), tok.span),
            TokenKind::Ident(name) => self
                .world
                .alloc(NodeKind::Ident(self.arena.alloc_str(&name)), tok.span),
            TokenKind::LParen => {
                let inner = self.parse_expr();
                self.expect(&TokenKind::RParen);
                inner // span is the inner expression (parens are transparent)
            }
            other => panic!("unexpected token in expression: {:?}", other),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use bumpalo::Bump;

    use super::Parser;
    use crate::ast::{AstWorld, BinOp, NodeId, NodeKind, UnaryOp};
    use crate::lexer::Lexer;

    // ── helpers ─────────────────────────────────────────────────────────────

    fn parse<'a>(src: &str, arena: &'a Bump) -> (AstWorld<'a>, NodeId) {
        let tokens = Lexer::new(src).tokenize();
        let mut p = Parser::new(&tokens, arena);
        let root = p.parse_program();
        (p.world, root)
    }

    /// Return the children slice stored inside a `Program` or `Block` node.
    fn children<'a>(world: &AstWorld<'a>, id: NodeId) -> &'a [NodeId] {
        match *world.kind(id) {
            NodeKind::Program(s) | NodeKind::Block(s) => s,
            other => panic!("expected Program or Block, got {:?}", other),
        }
    }

    /// Shorthand: the first (and usually only) FnDecl inside a Program.
    fn first_fn(world: &AstWorld<'_>, root: NodeId) -> NodeId {
        children(world, root)[0]
    }

    /// Unwrap a FnDecl's body.
    fn fn_body(world: &AstWorld<'_>, fn_id: NodeId) -> NodeId {
        let NodeKind::FnDecl { body, .. } = *world.kind(fn_id) else {
            panic!("expected FnDecl");
        };
        body
    }

    // ── tests ────────────────────────────────────────────────────────────────

    // --- structure ---

    #[test]
    fn empty_function() {
        let arena = Bump::new();
        let (world, root) = parse("fn empty() {}", &arena);

        let items = children(&world, root);
        assert_eq!(items.len(), 1);

        let NodeKind::FnDecl {
            name,
            params,
            ret_ty,
            body,
        } = *world.kind(items[0])
        else {
            panic!("expected FnDecl");
        };
        assert_eq!(name, "empty");
        assert!(params.is_empty());
        assert!(ret_ty.is_none());
        assert!(children(&world, body).is_empty());
    }

    #[test]
    fn multiple_top_level_functions() {
        let arena = Bump::new();
        let (world, root) = parse("fn a() {} fn b() {} fn c() {}", &arena);

        let items = children(&world, root);
        assert_eq!(items.len(), 3);

        let names: Vec<&str> = items
            .iter()
            .map(|&id| {
                let NodeKind::FnDecl { name, .. } = *world.kind(id) else {
                    panic!()
                };
                name
            })
            .collect();
        assert_eq!(names, ["a", "b", "c"]);
    }

    // --- function declarations ---

    #[test]
    fn function_with_typed_params_and_return_type() {
        use NodeKind;

        let arena = Bump::new();
        let (world, root) = parse("fn add(a: int, b: int) -> int { return a + b; }", &arena);

        let fn_id = first_fn(&world, root);
        let NodeKind::FnDecl {
            name,
            params,
            ret_ty,
            body,
        } = *world.kind(fn_id)
        else {
            panic!()
        };
        assert_eq!(name, "add");
        assert_eq!(params.len(), 2);

        // param names and types
        let NodeKind::Param { name: p0, ty: t0 } = *world.kind(params[0]) else {
            panic!()
        };
        let NodeKind::Param { name: p1, ty: t1 } = *world.kind(params[1]) else {
            panic!()
        };
        assert_eq!(p0, "a");
        assert_eq!(p1, "b");
        assert!(matches!(
            *world.kind(t0.unwrap()),
            NodeKind::TypeName("int")
        ));
        assert!(matches!(
            *world.kind(t1.unwrap()),
            NodeKind::TypeName("int")
        ));

        // return type
        assert!(matches!(
            *world.kind(ret_ty.unwrap()),
            NodeKind::TypeName("int")
        ));

        // body: `return a + b`
        let stmts = children(&world, body);
        assert_eq!(stmts.len(), 1);
        let NodeKind::ReturnStmt(Some(expr)) = *world.kind(stmts[0]) else {
            panic!()
        };
        let NodeKind::BinOp {
            op: BinOp::Add,
            lhs,
            rhs,
        } = *world.kind(expr)
        else {
            panic!()
        };
        assert!(matches!(*world.kind(lhs), NodeKind::Ident("a")));
        assert!(matches!(*world.kind(rhs), NodeKind::Ident("b")));
    }

    #[test]
    fn function_no_return_type() {
        let arena = Bump::new();
        let (world, root) = parse("fn greet(name: str) {}", &arena);

        let NodeKind::FnDecl { ret_ty, params, .. } = *world.kind(first_fn(&world, root)) else {
            panic!()
        };
        assert!(ret_ty.is_none());
        assert_eq!(params.len(), 1);
    }

    // --- statements ---

    #[test]
    fn let_with_type_annotation_and_init() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let x: int = 42; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt { name, ty, init } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert_eq!(name, "x");
        assert!(matches!(
            *world.kind(ty.unwrap()),
            NodeKind::TypeName("int")
        ));
        assert!(matches!(*world.kind(init.unwrap()), NodeKind::IntLit(42)));
    }

    #[test]
    fn let_without_type_annotation() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let flag = true; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt { name, ty, init } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert_eq!(name, "flag");
        assert!(ty.is_none());
        assert!(matches!(
            *world.kind(init.unwrap()),
            NodeKind::BoolLit(true)
        ));
    }

    #[test]
    fn return_no_value() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { return; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        assert!(matches!(
            *world.kind(children(&world, body)[0]),
            NodeKind::ReturnStmt(None)
        ));
    }

    #[test]
    fn assign_stmt() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { x = 99; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::AssignStmt { target, value } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert!(matches!(*world.kind(target), NodeKind::Ident("x")));
        assert!(matches!(*world.kind(value), NodeKind::IntLit(99)));
    }

    #[test]
    fn right_assoc_assign() {
        // `x = y = 0` must parse as `x = (y = 0)`
        let arena = Bump::new();
        let (world, root) = parse("fn main() { x = y = 0; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::AssignStmt { target, value } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert!(matches!(*world.kind(target), NodeKind::Ident("x")));
        // the value is itself an AssignStmt
        let NodeKind::AssignStmt {
            target: inner_t,
            value: inner_v,
        } = *world.kind(value)
        else {
            panic!("expected nested AssignStmt")
        };
        assert!(matches!(*world.kind(inner_t), NodeKind::Ident("y")));
        assert!(matches!(*world.kind(inner_v), NodeKind::IntLit(0)));
    }

    // --- control flow ---

    #[test]
    fn if_stmt_no_else() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { if cond { return; } }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::IfStmt {
            cond,
            then_block,
            else_block,
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };

        assert!(matches!(*world.kind(cond), NodeKind::Ident("cond")));
        assert!(else_block.is_none());
        assert_eq!(children(&world, then_block).len(), 1);
    }

    #[test]
    fn if_else_stmt() {
        let arena = Bump::new();
        let (world, root) = parse(
            "fn main() { if x { return 1; } else { return 2; } }",
            &arena,
        );

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::IfStmt { else_block, .. } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        let else_id = else_block.expect("expected else block");
        let else_stmts = children(&world, else_id);
        assert_eq!(else_stmts.len(), 1);
        assert!(matches!(
            *world.kind(else_stmts[0]),
            NodeKind::ReturnStmt(Some(_))
        ));
    }

    #[test]
    fn else_if_chain() {
        // `else if` must produce a nested IfStmt as the else branch, not a Block.
        let arena = Bump::new();
        let (world, root) = parse(
            "fn main() { if a { return 1; } else if b { return 2; } else { return 3; } }",
            &arena,
        );

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::IfStmt {
            cond, else_block, ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        assert!(matches!(*world.kind(cond), NodeKind::Ident("a")));

        // else branch is another IfStmt (not a Block)
        let else_id = else_block.expect("expected else-if");
        let NodeKind::IfStmt {
            cond: cond2,
            else_block: else2,
            ..
        } = *world.kind(else_id)
        else {
            panic!("expected IfStmt as else branch")
        };
        assert!(matches!(*world.kind(cond2), NodeKind::Ident("b")));
        assert!(else2.is_some(), "else-if should have a final else block");
    }

    #[test]
    fn while_stmt() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { while n > 0 { n = n - 1; } }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::WhileStmt {
            cond,
            body: loop_body,
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        assert!(matches!(
            *world.kind(cond),
            NodeKind::BinOp { op: BinOp::Gt, .. }
        ));
        assert_eq!(children(&world, loop_body).len(), 1);
    }

    // --- expressions / operators ---

    #[test]
    fn precedence_mul_binds_tighter_than_add() {
        // `1 + 2 * 3` must parse as `1 + (2 * 3)`
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let r: int = 1 + 2 * 3; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        let NodeKind::BinOp {
            op: BinOp::Add,
            lhs,
            rhs,
        } = *world.kind(expr)
        else {
            panic!("expected outer Add")
        };
        assert!(matches!(*world.kind(lhs), NodeKind::IntLit(1)));
        let NodeKind::BinOp {
            op: BinOp::Mul,
            lhs: l2,
            rhs: r2,
        } = *world.kind(rhs)
        else {
            panic!("expected inner Mul")
        };
        assert!(matches!(*world.kind(l2), NodeKind::IntLit(2)));
        assert!(matches!(*world.kind(r2), NodeKind::IntLit(3)));
    }

    #[test]
    fn precedence_comparison_binds_tighter_than_logical_and() {
        // `a < b && c > d` must parse as `(a < b) && (c > d)`
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let r: bool = a < b && c > d; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        let NodeKind::BinOp {
            op: BinOp::And,
            lhs,
            rhs,
        } = *world.kind(expr)
        else {
            panic!("expected And at the top")
        };
        assert!(matches!(
            *world.kind(lhs),
            NodeKind::BinOp { op: BinOp::Lt, .. }
        ));
        assert!(matches!(
            *world.kind(rhs),
            NodeKind::BinOp { op: BinOp::Gt, .. }
        ));
    }

    #[test]
    fn unary_negation() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let x: int = -5; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        let NodeKind::UnaryOp {
            op: UnaryOp::Neg,
            operand,
        } = *world.kind(expr)
        else {
            panic!()
        };
        assert!(matches!(*world.kind(operand), NodeKind::IntLit(5)));
    }

    #[test]
    fn unary_not() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let b: bool = !true; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        let NodeKind::UnaryOp {
            op: UnaryOp::Not,
            operand,
        } = *world.kind(expr)
        else {
            panic!()
        };
        assert!(matches!(*world.kind(operand), NodeKind::BoolLit(true)));
    }

    // --- calls ---

    #[test]
    fn call_no_args() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { foo(); }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::Call { callee, args } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert!(matches!(*world.kind(callee), NodeKind::Ident("foo")));
        assert!(args.is_empty());
    }

    #[test]
    fn call_with_args() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { add(1, 2); }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::Call { callee, args } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert!(matches!(*world.kind(callee), NodeKind::Ident("add")));
        assert_eq!(args.len(), 2);
        assert!(matches!(*world.kind(args[0]), NodeKind::IntLit(1)));
        assert!(matches!(*world.kind(args[1]), NodeKind::IntLit(2)));
    }

    #[test]
    fn nested_call() {
        // `print(add(1, 2))` — callee of outer call is `print`, inner is `add`
        let arena = Bump::new();
        let (world, root) = parse("fn main() { print(add(1, 2)); }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::Call { callee, args } = *world.kind(children(&world, body)[0]) else {
            panic!()
        };
        assert!(matches!(*world.kind(callee), NodeKind::Ident("print")));
        assert_eq!(args.len(), 1);

        let NodeKind::Call {
            callee: inner_c,
            args: inner_a,
        } = *world.kind(args[0])
        else {
            panic!("expected inner Call")
        };
        assert!(matches!(*world.kind(inner_c), NodeKind::Ident("add")));
        assert_eq!(inner_a.len(), 2);
    }

    // --- literals ---

    #[test]
    fn integer_literal() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let n: int = 123; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        assert!(matches!(*world.kind(expr), NodeKind::IntLit(123)));
    }

    #[test]
    fn float_literal() {
        let arena = Bump::new();
        let (world, root) = parse("fn main() { let f: float = 3.14; }", &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        let NodeKind::FloatLit(v) = *world.kind(expr) else {
            panic!()
        };
        assert!((v - 3.14).abs() < 1e-10);
    }

    #[test]
    fn string_literal() {
        let arena = Bump::new();
        let (world, root) = parse(r#"fn main() { let s: str = "hello"; }"#, &arena);

        let body = fn_body(&world, first_fn(&world, root));
        let NodeKind::LetStmt {
            init: Some(expr), ..
        } = *world.kind(children(&world, body)[0])
        else {
            panic!()
        };
        assert!(matches!(*world.kind(expr), NodeKind::StringLit("hello")));
    }
}
