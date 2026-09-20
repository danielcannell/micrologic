// Surface grammar:
//
// module  := item*
// item    := axiom | theorem
// axiom   := "axiom" IDENT ':' type '.'
// theorem := "theorem" IDENT ':' type ':=' term '.'
//
// type       := type_or ("->" type)?
// type_or    := type_and ("or" type_or)?
// type_and   := type_not ("and" type_and)?
// type_not   := "not" type_not | type_atom
// type_atom  := type_paren | type_true | type_false | type_ident
// type_paren := "(" type ")"
// type_true  := "True"
// type_false := "False"
// type_ident := IDENT
//
// term        := term_fun | term_case | term_app
// term_fun    := "fun" "(" IDENT ":" type ")" "=" term
// term_case   := "case" term "of" "|" "inl" IDENT "=>" term "|" "inr" IDENT "=>" term
// term_app    := term_atom+
// term_atom   := term_paren | term_pair | term_fst | term_snd | term_inl | term_inr | term_absurd | term_var
// term_paren  := "(" term ")"
// term_pair   := "(" term ("," term)+ ")"   -- right-nested: (a,b,c) = (a,(b,c))
// term_fst    := "fst" term_atom
// term_snd    := "snd" term_atom
// term_inl    := "inl" "[" type "]" term_atom
// term_inr    := "inr" "[" type "]" term_atom
// term_absurd := "absurd" "[" type "]" term_atom
// term_var    := IDENT

use std::str::CharIndices;
use crate::diagnostics::{Diagnostic, Result, Span};

pub mod ast {
    use crate::surface::Span;

    #[derive(Debug, Clone)]
    pub struct Module {
        pub span: Span,
        pub items: Vec<Item>,
    }

    #[derive(Debug, Clone)]
    pub enum Item {
        Axiom(Axiom),
        Theorem(Theorem),
    }

    /// `axiom name : type .`
    #[derive(Debug, Clone)]
    pub struct Axiom {
        pub span: Span,
        pub name: Ident,
        pub typ: Type,
    }

    /// `theorem name : type := body .`
    #[derive(Debug, Clone)]
    pub struct Theorem {
        pub span: Span,
        pub name: Ident,
        pub typ: Type,
        pub body: Term,
    }

    #[derive(Debug, Clone)]
    pub enum Type {
        Lambda(Lambda),
        Or(Or),
        And(And),
        Not(Not),
        True(True),
        False(False),
        Atom(Atom),
    }

    /// `argument_type -> result_type`
    #[derive(Debug, Clone)]
    pub struct Lambda {
        pub span: Span,
        pub argument_type: Box<Type>,
        pub result_type: Box<Type>,
    }

    /// `left or right`
    #[derive(Debug, Clone)]
    pub struct Or {
        pub span: Span,
        pub left: Box<Type>,
        pub right: Box<Type>,
    }

    /// `left and right`
    #[derive(Debug, Clone)]
    pub struct And {
        pub span: Span,
        pub left: Box<Type>,
        pub right: Box<Type>,
    }

    /// `not operand`
    #[derive(Debug, Clone)]
    pub struct Not {
        pub span: Span,
        pub operand: Box<Type>,
    }

    #[derive(Debug, Clone)]
    pub struct True {
        pub span: Span,
    }

    #[derive(Debug, Clone)]
    pub struct False {
        pub span: Span,
    }

    /// `name`
    #[derive(Debug, Clone)]
    pub struct Atom {
        pub span: Span,
        pub name: Ident,
    }

    #[derive(Debug, Clone)]
    pub enum Term {
        Var(Var),
        Fun(Fun),
        App(App),
        Pair(Pair),
        Fst(Fst),
        Snd(Snd),
        Inl(Inl),
        Inr(Inr),
        Case(Case),
        Absurd(Absurd),
    }

    /// `name`
    #[derive(Debug, Clone)]
    pub struct Var {
        pub span: Span,
        pub name: Ident,
    }

    /// `fun (argument : argument_type) = body`
    #[derive(Debug, Clone)]
    pub struct Fun {
        pub span: Span,
        pub argument: Ident,
        pub argument_type: Type,
        pub body: Box<Term>,
    }

    /// `function argument`
    #[derive(Debug, Clone)]
    pub struct App {
        pub span: Span,
        pub function: Box<Term>,
        pub argument: Box<Term>,
    }

    /// `(left, right)`
    #[derive(Debug, Clone)]
    pub struct Pair {
        pub span: Span,
        pub left: Box<Term>,
        pub right: Box<Term>,
    }

    /// `fst pair`
    #[derive(Debug, Clone)]
    pub struct Fst {
        pub span: Span,
        pub pair: Box<Term>,
    }

    /// `snd pair`
    #[derive(Debug, Clone)]
    pub struct Snd {
        pub span: Span,
        pub pair: Box<Term>,
    }

    /// `inl [right_type] left`
    #[derive(Debug, Clone)]
    pub struct Inl {
        pub span: Span,
        pub right_type: Type,
        pub left: Box<Term>,
    }

    /// `inr [left_type] right`
    #[derive(Debug, Clone)]
    pub struct Inr {
        pub span: Span,
        pub left_type: Type,
        pub right: Box<Term>,
    }

    /// `case either of | inl left_name => left_body | inr right_name => right_body`
    #[derive(Debug, Clone)]
    pub struct Case {
        pub span: Span,
        pub either: Box<Term>,
        pub left_name: Ident,
        pub left_body: Box<Term>,
        pub right_name: Ident,
        pub right_body: Box<Term>,
    }

    /// `absurd [goal_type] body`
    #[derive(Debug, Clone)]
    pub struct Absurd {
        pub span: Span,
        pub goal_type: Type,
        pub body: Box<Term>,
    }

    /// `name`
    #[derive(Debug, Clone)]
    pub struct Ident {
        pub span: Span,
        pub text: String,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    // Keywords
    Axiom,   // "axiom
    Theorem, // "theorem"
    Or,      // "or"
    And,     // "and"
    Not,     // "not"
    True,    // "True
    False,   // "False
    Fun,     // "fun"
    Case,    // "case"
    Of,      // "of"
    Inl,     // "inl"
    Inr,     // "inr"
    Fst,     // "fst"
    Snd,     // "snd"
    Absurd,  // "absurd"

    // Delimiters
    LeftParen,    // '('
    RightParen,   // ')'
    LeftBracket,  // '['
    RightBracket, // ']'

    // Punctuation
    Dot,        // '.'
    Bar,        // '|'
    Comma,      // ','
    Colon,      // ':'
    ColonEqual, // ':='
    Equal,      // '='
    FatArrow,   // '=>'
    Arrow,      // '->'

    Ident,

    InvalidToken,
    Eof,
}

#[derive(Debug, Clone)]
pub struct Token<'source> {
    pub kind: TokenKind,
    pub text: &'source str,
    pub span: Span,
}

pub struct Lexer<'source> {
    source: &'source str,
    iter: CharIndices<'source>,

    c: char,
    pos: usize,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source str) -> Self {
        let mut lexer = Self {
            source,
            iter: source.char_indices(),
            c: '\0',
            pos: 0,
        };

        lexer.advance();
        lexer
    }

    pub fn next_token(&mut self) -> Token<'source> {
        loop {
            self.skip_whitespace();

            if self.at_end() {
                return Token {
                    kind: TokenKind::Eof,
                    text: "",
                    span: Span {
                        start: self.source.len(),
                        end: self.source.len(),
                    },
                };
            }

            let start_pos = self.pos;

            let token_kind = match self.next_char() {
                // Single-character tokens
                '(' => TokenKind::LeftParen,
                ')' => TokenKind::RightParen,
                '[' => TokenKind::LeftBracket,
                ']' => TokenKind::RightBracket,
                '.' => TokenKind::Dot,
                '|' => TokenKind::Bar,
                ',' => TokenKind::Comma,

                // Multi-character tokens
                ':' => {
                    if self.accept('=') {
                        TokenKind::ColonEqual
                    } else {
                        TokenKind::Colon
                    }
                }
                '-' => {
                    if self.accept('-') {
                        while !self.at_end() && self.peek_char() != '\n' {
                            self.advance();
                        }
                        continue;
                    } else if self.accept('>') {
                        TokenKind::Arrow
                    } else {
                        TokenKind::InvalidToken
                    }
                }
                '=' => {
                    if self.accept('>') {
                        TokenKind::FatArrow
                    } else {
                        TokenKind::Equal
                    }
                }

                // Identifiers and keywords
                c if is_ident_char(c) => {
                    while is_ident_char(self.peek_char()) {
                        self.advance();
                    }

                    let text = &self.source[start_pos..self.pos];
                    match text {
                        "axiom" => TokenKind::Axiom,
                        "theorem" => TokenKind::Theorem,
                        "or" => TokenKind::Or,
                        "and" => TokenKind::And,
                        "not" => TokenKind::Not,
                        "True" => TokenKind::True,
                        "False" => TokenKind::False,
                        "fun" => TokenKind::Fun,
                        "case" => TokenKind::Case,
                        "of" => TokenKind::Of,
                        "inl" => TokenKind::Inl,
                        "inr" => TokenKind::Inr,
                        "fst" => TokenKind::Fst,
                        "snd" => TokenKind::Snd,
                        "absurd" => TokenKind::Absurd,
                        _ => TokenKind::Ident,
                    }
                }

                _ => TokenKind::InvalidToken,
            };

            let text = &self.source[start_pos..self.pos];

            return Token {
                kind: token_kind,
                text,
                span: Span {
                    start: start_pos,
                    end: self.pos,
                },
            };
        }
    }

    fn skip_whitespace(&mut self) {
        while self.peek_char().is_whitespace() {
            self.advance();
        }
    }

    fn advance(&mut self) {
        if let Some((pos, c)) = self.iter.next() {
            self.pos = pos;
            self.c = c;
        } else {
            self.pos = self.source.len();
            self.c = '\0';
        }
    }

    fn next_char(&mut self) -> char {
        let c = self.c;
        self.advance();
        c
    }

    fn peek_char(&self) -> char {
        self.c
    }

    fn accept(&mut self, c: char) -> bool {
        if self.peek_char() == c {
            self.advance();
            true
        } else {
            false
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.source.len()
    }
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

pub fn parse(source: &str) -> Result<ast::Module> {
    Parser::new(source).parse_module()
}

struct Parser <'source> {
    lexer: Lexer<'source>,
    current: Token<'source>,
    previous: Token<'source>,
}

impl<'source> Parser<'source> {
    fn new(source: &'source str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        let previous = current.clone();

        Parser {
            lexer,
            current,
            previous,
        }
    }

    // module := item*
    fn parse_module(&mut self) -> Result<ast::Module> {
        let start = self.current.span;
        let mut items = Vec::new();

        while !self.at_end() {
            items.push(self.parse_item()?);
        }

        Ok(ast::Module { span: self.span_from(start), items })
    }

    // item := axiom | theorem
    fn parse_item(&mut self) -> Result<ast::Item> {
        match self.peek_token() {
            TokenKind::Axiom => Ok(ast::Item::Axiom(self.parse_axiom()?)),
            TokenKind::Theorem => Ok(ast::Item::Theorem(self.parse_theorem()?)),
            _ => self.unexpected("`axiom` or `theorem`"),
        }
    }

    // axiom := "axiom" IDENT ':' type '.'
    fn parse_axiom(&mut self) -> Result<ast::Axiom> {
        let start = self.current.span;
        self.expect_token(TokenKind::Axiom)?;
        let name = self.parse_ident()?;
        self.expect_token(TokenKind::Colon)?;
        let typ = self.parse_type()?;
        self.expect_token(TokenKind::Dot)?;
        Ok(ast::Axiom { span: self.span_from(start), name, typ })
    }

    // theorem := "theorem" IDENT ':' type ':=' term '.'
    fn parse_theorem(&mut self) -> Result<ast::Theorem> {
        let start = self.current.span;
        self.expect_token(TokenKind::Theorem)?;
        let name = self.parse_ident()?;
        self.expect_token(TokenKind::Colon)?;
        let typ = self.parse_type()?;
        self.expect_token(TokenKind::ColonEqual)?;
        let body = self.parse_term()?;
        self.expect_token(TokenKind::Dot)?;
        Ok(ast::Theorem { span: self.span_from(start), name, typ, body })
    }

    // type := type_or ("->" type)?
    //
    // "->" is right-associative, so we recurse on the right.
    fn parse_type(&mut self) -> Result<ast::Type> {
        let start = self.current.span;
        let left = self.parse_type_or()?;
        if self.accept_token(TokenKind::Arrow) {
            let right = self.parse_type()?;
            Ok(ast::Type::Lambda(ast::Lambda {
                span: self.span_from(start),
                argument_type: Box::new(left),
                result_type: Box::new(right),
            }))
        } else {
            Ok(left)
        }
    }

    // type_or := type_and ("or" type_or)?
    fn parse_type_or(&mut self) -> Result<ast::Type> {
        let start = self.current.span;
        let left = self.parse_type_and()?;
        if self.accept_token(TokenKind::Or) {
            let right = self.parse_type_or()?;
            Ok(ast::Type::Or(ast::Or {
                span: self.span_from(start),
                left: Box::new(left),
                right: Box::new(right),
            }))
        } else {
            Ok(left)
        }
    }

    // type_and := type_not ("and" type_and)?
    fn parse_type_and(&mut self) -> Result<ast::Type> {
        let start = self.current.span;
        let left = self.parse_type_not()?;
        if self.accept_token(TokenKind::And) {
            let right = self.parse_type_and()?;
            Ok(ast::Type::And(ast::And {
                span: self.span_from(start),
                left: Box::new(left),
                right: Box::new(right),
            }))
        } else {
            Ok(left)
        }
    }

    // type_not := "not" type_not | type_atom
    fn parse_type_not(&mut self) -> Result<ast::Type> {
        let start = self.current.span;
        if self.accept_token(TokenKind::Not) {
            let operand = self.parse_type_not()?;
            Ok(ast::Type::Not(ast::Not {
                span: self.span_from(start),
                operand: Box::new(operand),
            }))
        } else {
            self.parse_type_atom()
        }
    }

    // type_atom  := type_paren | type_true | type_false | type_ident
    // type_paren := "(" type ")"
    fn parse_type_atom(&mut self) -> Result<ast::Type> {
        let start = self.current.span;
        match self.peek_token() {
            TokenKind::LeftParen => {
                self.expect_token(TokenKind::LeftParen)?;
                let typ = self.parse_type()?;
                self.expect_token(TokenKind::RightParen)?;
                Ok(typ)
            }
            TokenKind::True => {
                self.advance();
                Ok(ast::Type::True(ast::True { span: start }))
            }
            TokenKind::False => {
                self.advance();
                Ok(ast::Type::False(ast::False { span: start }))
            }
            TokenKind::Ident => {
                let name = self.parse_ident()?;
                Ok(ast::Type::Atom(ast::Atom {
                    span: self.span_from(start),
                    name,
                }))
            }
            _ => self.unexpected("a type"),
        }
    }

    // term := term_fun | term_case | term_app
    fn parse_term(&mut self) -> Result<ast::Term> {
        match self.peek_token() {
            TokenKind::Fun => self.parse_term_fun(),
            TokenKind::Case => self.parse_term_case(),
            _ => self.parse_term_app(),
        }
    }

    // term_fun := "fun" "(" IDENT ":" type ")" "=" term
    fn parse_term_fun(&mut self) -> Result<ast::Term> {
        let start = self.current.span;
        self.expect_token(TokenKind::Fun)?;
        self.expect_token(TokenKind::LeftParen)?;
        let argument = self.parse_ident()?;
        self.expect_token(TokenKind::Colon)?;
        let argument_type = self.parse_type()?;
        self.expect_token(TokenKind::RightParen)?;
        self.expect_token(TokenKind::Equal)?;
        let body = self.parse_term()?;
        Ok(ast::Term::Fun(ast::Fun {
            span: self.span_from(start),
            argument,
            argument_type,
            body: Box::new(body),
        }))
    }

    // term_case := "case" term "of" "|" "inl" IDENT "=>" term "|" "inr" IDENT "=>" term
    fn parse_term_case(&mut self) -> Result<ast::Term> {
        let start = self.current.span;
        self.expect_token(TokenKind::Case)?;
        let either = self.parse_term()?;
        self.expect_token(TokenKind::Of)?;
        self.expect_token(TokenKind::Bar)?;
        self.expect_token(TokenKind::Inl)?;
        let left_name = self.parse_ident()?;
        self.expect_token(TokenKind::FatArrow)?;
        let left_body = self.parse_term()?;
        self.expect_token(TokenKind::Bar)?;
        self.expect_token(TokenKind::Inr)?;
        let right_name = self.parse_ident()?;
        self.expect_token(TokenKind::FatArrow)?;
        let right_body = self.parse_term()?;
        Ok(ast::Term::Case(ast::Case {
            span: self.span_from(start),
            either: Box::new(either),
            left_name,
            left_body: Box::new(left_body),
            right_name,
            right_body: Box::new(right_body),
        }))
    }

    // term_app := term_atom+
    //
    // Application is left-associative: `f a b` parses as `(f a) b`.
    fn parse_term_app(&mut self) -> Result<ast::Term> {
        let start = self.current.span;
        let mut function = self.parse_term_atom()?;
        while self.at_term_atom_start() {
            let argument = self.parse_term_atom()?;
            function = ast::Term::App(ast::App {
                span: self.span_from(start),
                function: Box::new(function),
                argument: Box::new(argument),
            });
        }
        Ok(function)
    }

    // Whether the current token can begin a term_atom, i.e. another argument
    // in an application.
    fn at_term_atom_start(&self) -> bool {
        matches!(
            self.peek_token(),
            TokenKind::LeftParen
                | TokenKind::Fst
                | TokenKind::Snd
                | TokenKind::Inl
                | TokenKind::Inr
                | TokenKind::Absurd
                | TokenKind::Ident
        )
    }

    // term_atom := term_paren | term_pair | term_fst | term_snd | term_inl
    //            | term_inr | term_absurd | term_var
    fn parse_term_atom(&mut self) -> Result<ast::Term> {
        let start = self.current.span;
        match self.peek_token() {
            TokenKind::LeftParen => self.parse_term_paren_or_pair(),
            TokenKind::Fst => {
                self.expect_token(TokenKind::Fst)?;
                let pair = self.parse_term_atom()?;
                Ok(ast::Term::Fst(ast::Fst {
                    span: self.span_from(start),
                    pair: Box::new(pair),
                }))
            }
            TokenKind::Snd => {
                self.expect_token(TokenKind::Snd)?;
                let pair = self.parse_term_atom()?;
                Ok(ast::Term::Snd(ast::Snd {
                    span: self.span_from(start),
                    pair: Box::new(pair),
                }))
            }
            TokenKind::Inl => {
                self.expect_token(TokenKind::Inl)?;
                self.expect_token(TokenKind::LeftBracket)?;
                let right_type = self.parse_type()?;
                self.expect_token(TokenKind::RightBracket)?;
                let left = self.parse_term_atom()?;
                Ok(ast::Term::Inl(ast::Inl {
                    span: self.span_from(start),
                    right_type,
                    left: Box::new(left),
                }))
            }
            TokenKind::Inr => {
                self.expect_token(TokenKind::Inr)?;
                self.expect_token(TokenKind::LeftBracket)?;
                let left_type = self.parse_type()?;
                self.expect_token(TokenKind::RightBracket)?;
                let right = self.parse_term_atom()?;
                Ok(ast::Term::Inr(ast::Inr {
                    span: self.span_from(start),
                    left_type,
                    right: Box::new(right),
                }))
            }
            TokenKind::Absurd => {
                self.expect_token(TokenKind::Absurd)?;
                self.expect_token(TokenKind::LeftBracket)?;
                let goal_type = self.parse_type()?;
                self.expect_token(TokenKind::RightBracket)?;
                let body = self.parse_term_atom()?;
                Ok(ast::Term::Absurd(ast::Absurd {
                    span: self.span_from(start),
                    goal_type,
                    body: Box::new(body),
                }))
            }
            TokenKind::Ident => {
                let name = self.parse_ident()?;
                Ok(ast::Term::Var(ast::Var {
                    span: self.span_from(start),
                    name,
                }))
            }
            _ => self.unexpected("a term"),
        }
    }

    // term_paren := "(" term ")"
    // term_pair  := "(" term ("," term)+ ")"
    //
    // Both start with "(", so we parse the first term and then decide based on
    // whether a "," follows. A tuple of more than two elements desugars into
    // right-nested pairs: `(a, b, c, d)` becomes `(a, (b, (c, d)))`.
    fn parse_term_paren_or_pair(&mut self) -> Result<ast::Term> {
        let start = self.current.span;
        self.expect_token(TokenKind::LeftParen)?;

        let mut elements = vec![self.parse_term()?];
        while self.accept_token(TokenKind::Comma) {
            elements.push(self.parse_term()?);
        }
        self.expect_token(TokenKind::RightParen)?;

        // A lone parenthesised term is just grouping, not a pair.
        if elements.len() == 1 {
            return Ok(elements.pop().unwrap());
        }

        // Fold right into nested pairs. Every synthesised pair is given the span
        // of the whole parenthesised expression.
        let span = self.span_from(start);
        let mut right = elements.pop().unwrap();
        while let Some(left) = elements.pop() {
            right = ast::Term::Pair(ast::Pair {
                span,
                left: Box::new(left),
                right: Box::new(right),
            });
        }
        Ok(right)
    }

    fn parse_ident(&mut self) -> Result<ast::Ident> {
        let span = self.current.span;
        let text = self.current.text.to_string();
        self.expect_token(TokenKind::Ident)?;
        Ok(ast::Ident { span, text })
    }

    fn peek_token(&self) -> TokenKind {
        self.current.kind
    }

    fn check_token(&self, kind: TokenKind) -> bool {
        self.current.kind == kind
    }

    fn accept_token(&mut self, kind: TokenKind) -> bool {
        if self.check_token(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect_token(&mut self, kind: TokenKind) -> Result<()> {
        if self.check_token(kind) {
            self.advance();
            Ok(())
        } else {
            self.unexpected(describe(kind))
        }
    }

    fn advance(&mut self) {
        self.previous = self.current.clone();
        self.current = self.lexer.next_token();
    }

    fn at_end(&self) -> bool {
        self.current.kind == TokenKind::Eof
    }

    fn span_from(&self, start: Span) -> Span {
        Span {
            start: start.start,
            end: self.previous.span.end,
        }
    }

    /// Build an "expected X, but found Y" diagnostic pointing at the current
    /// token, describing the current token in a reader-friendly way.
    fn unexpected<T>(&self, expected: &str) -> Result<T> {
        let found = match self.current.kind {
            TokenKind::Eof => "end of input".to_string(),
            TokenKind::InvalidToken => format!("invalid token `{}`", self.current.text),
            _ => format!("`{}`", self.current.text),
        };
        Err(Diagnostic::error(
            format!("expected {expected}, but found {found}"),
            self.current.span,
        ))
    }
}

/// A reader-friendly description of a token kind, used in "expected ..." messages.
fn describe(kind: TokenKind) -> &'static str {
    match kind {
        TokenKind::Axiom => "`axiom`",
        TokenKind::Theorem => "`theorem`",
        TokenKind::Or => "`or`",
        TokenKind::And => "`and`",
        TokenKind::Not => "`not`",
        TokenKind::True => "`True`",
        TokenKind::False => "`False`",
        TokenKind::Fun => "`fun`",
        TokenKind::Case => "`case`",
        TokenKind::Of => "`of`",
        TokenKind::Inl => "`inl`",
        TokenKind::Inr => "`inr`",
        TokenKind::Fst => "`fst`",
        TokenKind::Snd => "`snd`",
        TokenKind::Absurd => "`absurd`",
        TokenKind::LeftParen => "`(`",
        TokenKind::RightParen => "`)`",
        TokenKind::LeftBracket => "`[`",
        TokenKind::RightBracket => "`]`",
        TokenKind::Dot => "`.`",
        TokenKind::Bar => "`|`",
        TokenKind::Comma => "`,`",
        TokenKind::Colon => "`:`",
        TokenKind::ColonEqual => "`:=`",
        TokenKind::Equal => "`=`",
        TokenKind::FatArrow => "`=>`",
        TokenKind::Arrow => "`->`",
        TokenKind::Ident => "an identifier",
        TokenKind::InvalidToken => "an invalid token",
        TokenKind::Eof => "end of input",
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::{ast, parse, Lexer, TokenKind};

    // Render a type as a fully-parenthesized s-expression so tests can assert
    // on structure (precedence and associativity) without depending on spans.
    fn show_type(typ: &ast::Type) -> String {
        match typ {
            ast::Type::Lambda(l) => {
                format!("(-> {} {})", show_type(&l.argument_type), show_type(&l.result_type))
            }
            ast::Type::Or(o) => format!("(or {} {})", show_type(&o.left), show_type(&o.right)),
            ast::Type::And(a) => format!("(and {} {})", show_type(&a.left), show_type(&a.right)),
            ast::Type::Not(n) => format!("(not {})", show_type(&n.operand)),
            ast::Type::True(_) => "True".to_string(),
            ast::Type::False(_) => "False".to_string(),
            ast::Type::Atom(a) => a.name.text.clone(),
        }
    }

    fn show_term(term: &ast::Term) -> String {
        match term {
            ast::Term::Var(v) => v.name.text.clone(),
            ast::Term::Fun(f) => format!(
                "(fun {} : {} {})",
                f.argument.text,
                show_type(&f.argument_type),
                show_term(&f.body)
            ),
            ast::Term::App(a) => {
                format!("(app {} {})", show_term(&a.function), show_term(&a.argument))
            }
            ast::Term::Pair(p) => format!("(pair {} {})", show_term(&p.left), show_term(&p.right)),
            ast::Term::Fst(f) => format!("(fst {})", show_term(&f.pair)),
            ast::Term::Snd(s) => format!("(snd {})", show_term(&s.pair)),
            ast::Term::Inl(i) => format!("(inl [{}] {})", show_type(&i.right_type), show_term(&i.left)),
            ast::Term::Inr(i) => format!("(inr [{}] {})", show_type(&i.left_type), show_term(&i.right)),
            ast::Term::Case(c) => format!(
                "(case {} inl {} => {} inr {} => {})",
                show_term(&c.either),
                c.left_name.text,
                show_term(&c.left_body),
                c.right_name.text,
                show_term(&c.right_body),
            ),
            ast::Term::Absurd(a) => {
                format!("(absurd [{}] {})", show_type(&a.goal_type), show_term(&a.body))
            }
        }
    }

    // Parse a single `theorem` and return its type and body rendered as
    // s-expressions.
    fn parse_theorem(source: &str) -> (String, String) {
        let module = parse(source).expect("should parse");
        assert_eq!(module.items.len(), 1);
        match &module.items[0] {
            ast::Item::Theorem(t) => (show_type(&t.typ), show_term(&t.body)),
            other => panic!("expected a theorem, got {:?}", other),
        }
    }

    fn parse_type_str(source: &str) -> String {
        let (typ, _) = parse_theorem(&format!("theorem t : {source} := x."));
        typ
    }

    fn parse_term_str(source: &str) -> String {
        let (_, term) = parse_theorem(&format!("theorem t : A := {source}."));
        term
    }

    #[test]
    fn test_type_precedence() {
        // `and` binds tighter than `or`, which binds tighter than `->`.
        assert_eq!(parse_type_str("A and B or C -> D"), "(-> (or (and A B) C) D)");
        // `not` binds tightest.
        assert_eq!(parse_type_str("not A and B"), "(and (not A) B)");
        assert_eq!(parse_type_str("not not A"), "(not (not A))");
    }

    #[test]
    fn test_type_associativity() {
        // `->` is right-associative.
        assert_eq!(parse_type_str("A -> B -> C"), "(-> A (-> B C))");
        // `and` and `or` are right-associative.
        assert_eq!(parse_type_str("A and B and C"), "(and A (and B C))");
        assert_eq!(parse_type_str("A or B or C"), "(or A (or B C))");
        // Parentheses override the defaults.
        assert_eq!(parse_type_str("(A -> B) -> C"), "(-> (-> A B) C)");
    }

    #[test]
    fn test_type_atoms() {
        assert_eq!(parse_type_str("True"), "True");
        assert_eq!(parse_type_str("False"), "False");
        assert_eq!(parse_type_str("(A)"), "A");
    }

    #[test]
    fn test_term_application_is_left_associative() {
        assert_eq!(parse_term_str("f a b c"), "(app (app (app f a) b) c)");
    }

    #[test]
    fn test_term_paren_vs_pair() {
        assert_eq!(parse_term_str("(a)"), "a");
        assert_eq!(parse_term_str("(a, b)"), "(pair a b)");
        // Arguments to a pair are full terms.
        assert_eq!(parse_term_str("(f a, g b)"), "(pair (app f a) (app g b))");
        // Tuples of more than two elements desugar into right-nested pairs.
        assert_eq!(parse_term_str("(a, b, c)"), "(pair a (pair b c))");
        assert_eq!(
            parse_term_str("(a, b, c, d)"),
            "(pair a (pair b (pair c d)))"
        );
        // Explicit nesting on the left still round-trips.
        assert_eq!(parse_term_str("((a, b), c)"), "(pair (pair a b) c)");
    }

    #[test]
    fn test_term_eliminators() {
        assert_eq!(parse_term_str("fst p"), "(fst p)");
        assert_eq!(parse_term_str("snd p"), "(snd p)");
        // `fst`/`snd` take a single atom, so `fst p q` is an application.
        assert_eq!(parse_term_str("fst p q"), "(app (fst p) q)");
    }

    #[test]
    fn test_term_injections_and_absurd() {
        assert_eq!(parse_term_str("inl [B] a"), "(inl [B] a)");
        assert_eq!(parse_term_str("inr [A] b"), "(inr [A] b)");
        assert_eq!(parse_term_str("absurd [A -> B] x"), "(absurd [(-> A B)] x)");
    }

    #[test]
    fn test_term_fun_and_case() {
        assert_eq!(
            parse_term_str("fun (x : A -> B) = x"),
            "(fun x : (-> A B) x)"
        );
        assert_eq!(
            parse_term_str("case e of | inl x => x | inr y => y"),
            "(case e inl x => x inr y => y)"
        );
    }

    #[test]
    fn test_full_module() {
        let source = r#"
            -- The modus ponens theorem
            axiom a : A.
            theorem mp : A and (A -> B) -> B :=
                fun (h : A and (A -> B)) = (snd h) (fst h).
        "#;
        let module = parse(source).expect("should parse");
        assert_eq!(module.items.len(), 2);
        match &module.items[0] {
            ast::Item::Axiom(a) => {
                assert_eq!(a.name.text, "a");
                assert_eq!(show_type(&a.typ), "A");
            }
            other => panic!("expected axiom, got {:?}", other),
        }
        match &module.items[1] {
            ast::Item::Theorem(t) => {
                assert_eq!(t.name.text, "mp");
                assert_eq!(show_type(&t.typ), "(-> (and A (-> A B)) B)");
                assert_eq!(
                    show_term(&t.body),
                    "(fun h : (and A (-> A B)) (app (snd h) (fst h)))"
                );
            }
            other => panic!("expected theorem, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_errors() {
        assert!(parse("theorem t : A B := x.").is_err()); // junk after type
        assert!(parse("axiom a A.").is_err()); // missing colon
        assert!(parse("theorem t : A := .").is_err()); // missing body
    }

    #[test]
    fn test_lex() {
        const EXAMPLES: &str = r#"
            -- A comment
            axiom theorem
            or and not
            True False
            fun
            case of inl inr
            fst snd
            absurd
            ()[]
            .|,: := = => ->
            foo_bar_1'
        "#;

        let expected_tokens = vec![
            (TokenKind::Axiom, "axiom"),
            (TokenKind::Theorem, "theorem"),
            (TokenKind::Or, "or"),
            (TokenKind::And, "and"),
            (TokenKind::Not, "not"),
            (TokenKind::True, "True"),
            (TokenKind::False, "False"),
            (TokenKind::Fun, "fun"),
            (TokenKind::Case, "case"),
            (TokenKind::Of, "of"),
            (TokenKind::Inl, "inl"),
            (TokenKind::Inr, "inr"),
            (TokenKind::Fst, "fst"),
            (TokenKind::Snd, "snd"),
            (TokenKind::Absurd, "absurd"),
            (TokenKind::LeftParen, "("),
            (TokenKind::RightParen, ")"),
            (TokenKind::LeftBracket, "["),
            (TokenKind::RightBracket, "]"),
            (TokenKind::Dot, "."),
            (TokenKind::Bar, "|"),
            (TokenKind::Comma, ","),
            (TokenKind::Colon, ":"),
            (TokenKind::ColonEqual, ":="),
            (TokenKind::Equal, "="),
            (TokenKind::FatArrow, "=>"),
            (TokenKind::Arrow, "->"),
            (TokenKind::Ident, "foo_bar_1'"),
            (TokenKind::Eof, ""),
            (TokenKind::Eof, ""),
        ];

        let mut lexer = Lexer::new(EXAMPLES);

        for (expected_kind, expected_text) in expected_tokens {
            let token = lexer.next_token();
            let actual_text = &EXAMPLES[token.span.start..token.span.end];
            assert_eq!(token.kind, expected_kind);
            assert_eq!(token.text, expected_text);
            assert_eq!(token.text, actual_text);
        }
    }
}
