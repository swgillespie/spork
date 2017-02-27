%{

open Ast
open Span

let make_span () =
    let start = Parsing.symbol_start_pos () in
    let stop = Parsing.symbol_end_pos () in
    (start, stop)

let make_span_of n =
    let start = Parsing.rhs_start_pos n in
    let stop = Parsing.rhs_end_pos n in
    (start, stop)

let parse_error s =
    raise (Parse_error (make_span (), s))

let span_wrap s = spanned_of s (make_span ())

let mk_typealias ident ty = span_wrap (TypeAlias (ident, ty))
let mk_structdecl name fields = 
    span_wrap (StructDecl { struct_name = name; struct_fields = fields; })

let mk_fundecl ident params retty stmts = 
    let funcdecl = {
        fun_name = ident;
        fun_args = params;
        fun_retty = retty;
        fun_body = stmts;
    } in
    span_wrap (FunDecl funcdecl)

%}

%token <string> IDENT
%token <int> INT
%token <string> STRING

%token FUN LET IF ELSE LOOP TRUE FALSE AND OR NOT RETURN STRUCT
%token AS TYPE LPAREN RPAREN LBRACE RBRACE SEMICOLON COLON
%token ARROW COMMA EQUAL CARAT DOUBLE_EQUAL NOT_EQUAL GREATER_EQ
%token GREATER LESS_EQ LESS PLUS MINUS DIV STAR EOF LBRACKET RBRACKET DOT NEW

%start compilation_unit
%type <Ast.compilation_unit> compilation_unit

%%

compilation_unit:
    | item EOF { [$1] }
    | item compilation_unit { $1 :: $2 }

item:
    | TYPE ident EQUAL ty SEMICOLON
      { mk_typealias $2 $4 }
    | STRUCT ident LBRACE fields RBRACE
      { mk_structdecl $2 $4 }
    | FUN ident LPAREN parameters RPAREN return_ty LBRACE statements RBRACE
      { mk_fundecl $2 $4 $6 $8 }

fields:
    | { [] }
    | nonempty_fields { $1 }

nonempty_fields:
    | field { [$1] }
    | field nonempty_fields { $1 :: $2 }

field:
    | ident COLON ty SEMICOLON
    { ($1, $3) }

parameters:
    | { [] }
    | nonempty_parameters { $1 }

nonempty_parameters:
    | ident COLON ty { [($1, $3)] }
    | ident COLON ty COMMA nonempty_parameters { ($1, $3) :: $5 }

return_ty:
    | { None }
    | ARROW ty { Some $2 }

statements:
    | { [] }
    | nonempty_statements { $1 }

nonempty_statements:
    | statement { [$1] }
    | statement nonempty_statements { $1 :: $2 }

statement:
    | RETURN SEMICOLON
      { span_wrap (Return None) }
    | RETURN expr SEMICOLON
      { span_wrap (Return (Some $2)) }
    | LET ident EQUAL expr SEMICOLON
      { span_wrap (VarDecl ($2, $4)) }
    | expr EQUAL expr SEMICOLON
      { span_wrap (Assign ($1, $3)) }
    | IF expr LBRACE statements RBRACE
      { span_wrap (If ($2, $4, None)) }
    | IF expr LBRACE statements RBRACE ELSE LBRACE statements RBRACE
      { span_wrap (If ($2, $4, Some $8)) }
    | LOOP LBRACE statements RBRACE
      { span_wrap (Loop $3) }
    | expr SEMICOLON
      { span_wrap (Expr $1) }

expr:
    | and_expr OR expr
      { span_wrap (Or ($1, $3)) }
    | and_expr
      { $1 }

and_expr:
    | eq_expr AND and_expr
      { span_wrap (And ($1, $3)) }
    | eq_expr 
      { $1 }

eq_expr:
    | cmp_expr DOUBLE_EQUAL eq_expr
      { span_wrap (Cmp (Equal, $1, $3)) }
    | cmp_expr NOT_EQUAL eq_expr
      { span_wrap (Cmp (NotEqual, $1, $3)) }
    | cmp_expr
      { $1 }

cmp_expr:
    | add_expr GREATER cmp_expr
      { span_wrap (Cmp (Greater, $1, $3)) }
    | add_expr GREATER_EQ cmp_expr
      { span_wrap (Cmp (GreaterEq, $1, $3)) }
    | add_expr LESS cmp_expr
      { span_wrap (Cmp (Less, $1, $3)) }
    | add_expr LESS_EQ cmp_expr
      { span_wrap (Cmp (LessEq, $1, $3)) }
    | add_expr AS ty
      { span_wrap (Cast ($1, $3)) }
    | add_expr
      { $1 }

add_expr:
    | mul_expr PLUS add_expr
      { span_wrap (Arith (Add, $1, $3)) }
    | mul_expr MINUS add_expr
      { span_wrap (Arith (Sub, $1, $3)) }
    | mul_expr
      { $1 }

mul_expr:
    | unary_expr STAR mul_expr
      { span_wrap (Arith (Mul, $1, $3)) }
    | unary_expr DIV mul_expr
      { span_wrap (Arith (Div, $1, $3)) }
    | unary_expr 
      { $1 }

unary_expr:
    | NOT unary_expr
      { span_wrap (Not $2) }
    | MINUS unary_expr
      { span_wrap (Neg $2) }
    | NEW LPAREN ty RPAREN 
      { span_wrap (New $3) }
    | NEW LPAREN ty RPAREN LBRACKET expr RBRACKET
      { span_wrap (NewArray ($6, $3)) }
    | call_expr
      { $1 }

call_expr:
    | projection_expr LPAREN comma_sep_exprs RPAREN
      { span_wrap (Call ($1, $3)) }
    | projection_expr
      { $1 }

projection_expr:
    | primary_expr DOT ident
      { span_wrap (Projection ($1, $3)) }
    | primary_expr
      { $1 }

comma_sep_exprs:
    | { [] }
    | nonempty_comma_sep_exprs { $1 }

nonempty_comma_sep_exprs:
    | expr { [$1] }
    | expr COMMA nonempty_comma_sep_exprs { $1 :: $3 }

primary_expr:
    | LPAREN expr RPAREN
      { $2 }
    | TRUE
      { span_wrap (Literal (BoolLit true)) }
    | FALSE
      { span_wrap (Literal (BoolLit false)) }
    | INT
      { span_wrap (Literal (IntLit $1)) }
    | STRING
      { span_wrap (Literal (StringLit $1)) }
    | ident
      { span_wrap (Ident $1) }

ident:
    | IDENT
    { span_wrap $1 }

ty:
    | ty LBRACKET RBRACKET
    { span_wrap (ArrayTy $1) }
    | ident
    { span_wrap (NamedTy $1) }