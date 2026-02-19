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
        TokenKind::PipePipe => (1, 2),  // ||
        TokenKind::AmpAmp   => (3, 4),  // &&
        TokenKind::EqEq | TokenKind::BangEq => (5, 6),           // == !=
        TokenKind::Lt | TokenKind::LtEq
        | TokenKind::Gt | TokenKind::GtEq => (7, 8),             // < <= > >=
        TokenKind::Plus | TokenKind::Minus => (9, 10),           // + -
        TokenKind::Star | TokenKind::Slash | TokenKind::Percent => (11, 12), // * / %
        _ => return None,
    };
    Some(bp)
}

fn token_to_binop(kind: &TokenKind) -> BinOp {
    match kind {
        TokenKind::Plus    => BinOp::Add,
        TokenKind::Minus   => BinOp::Sub,
        TokenKind::Star    => BinOp::Mul,
        TokenKind::Slash   => BinOp::Div,
        TokenKind::Percent => BinOp::Mod,
        TokenKind::EqEq    => BinOp::Eq,
        TokenKind::BangEq  => BinOp::Ne,
        TokenKind::Lt      => BinOp::Lt,
        TokenKind::LtEq    => BinOp::Le,
        TokenKind::Gt      => BinOp::Gt,
        TokenKind::GtEq    => BinOp::Ge,
        TokenKind::AmpAmp  => BinOp::And,
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
        self.world.alloc(NodeKind::Program(self.arena.alloc_slice_copy(&items)), Span::new(start, end))
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
            NodeKind::FnDecl { name, params: self.arena.alloc_slice_copy(&params), ret_ty, body },
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
        self.world.alloc(NodeKind::Param { name, ty }, Span::new(start, end))
    }

    fn parse_type(&mut self) -> NodeId {
        let tok = self.advance();
        match tok.kind {
            TokenKind::Ident(name) => {
                self.world.alloc(NodeKind::TypeName(self.arena.alloc_str(&name)), tok.span)
            }
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
        self.world.alloc(NodeKind::Block(self.arena.alloc_slice_copy(&stmts)), Span::new(start, end))
    }

    fn parse_stmt(&mut self) -> NodeId {
        match self.peek() {
            TokenKind::Let    => self.parse_let_stmt(),
            TokenKind::Return => self.parse_return_stmt(),
            TokenKind::If     => self.parse_if_stmt(),
            TokenKind::While  => self.parse_while_stmt(),
            _                 => self.parse_expr_stmt(),
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
        self.world.alloc(NodeKind::LetStmt { name, ty, init }, Span::new(start, end))
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
        self.world.alloc(NodeKind::ReturnStmt(value), Span::new(start, end))
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
            NodeKind::IfStmt { cond, then_block, else_block },
            Span::new(start, end),
        )
    }

    fn parse_while_stmt(&mut self) -> NodeId {
        let start = self.start_span();
        self.expect(&TokenKind::While);
        let cond = self.parse_expr();
        let body = self.parse_block();
        let end = self.end_of(body);
        self.world.alloc(NodeKind::WhileStmt { cond, body }, Span::new(start, end))
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
            self.world.alloc(NodeKind::AssignStmt { target: lhs, value: rhs }, Span::new(start, end))
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
            lhs = self.world.alloc(NodeKind::BinOp { op, lhs, rhs }, Span::new(start, end));
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
                self.world.alloc(NodeKind::UnaryOp { op: UnaryOp::Neg, operand }, Span::new(start, end))
            }
            TokenKind::Bang => {
                let start = self.start_span();
                self.advance();
                let operand = self.parse_unary();
                let end = self.end_of(operand);
                self.world.alloc(NodeKind::UnaryOp { op: UnaryOp::Not, operand }, Span::new(start, end))
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
                    NodeKind::Call { callee: expr, args: self.arena.alloc_slice_copy(&args) },
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
            TokenKind::Int(n)     => self.world.alloc(NodeKind::IntLit(n), tok.span),
            TokenKind::Float(f)   => self.world.alloc(NodeKind::FloatLit(f), tok.span),
            TokenKind::Bool(b)    => self.world.alloc(NodeKind::BoolLit(b), tok.span),
            TokenKind::Str(s)     => self.world.alloc(NodeKind::StringLit(self.arena.alloc_str(&s)), tok.span),
            TokenKind::Ident(name) => self.world.alloc(NodeKind::Ident(self.arena.alloc_str(&name)), tok.span),
            TokenKind::LParen => {
                let inner = self.parse_expr();
                self.expect(&TokenKind::RParen);
                inner // span is the inner expression (parens are transparent)
            }
            other => panic!("unexpected token in expression: {:?}", other),
        }
    }
}
