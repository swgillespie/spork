open Span

exception Parse_error of span * string
type ident = string spanned

type ty =
    | ArrayTy of ty spanned
    | NamedTy of ident
    | AliasedTy of ident * ty spanned

type struct_decl = {
    struct_name: ident;
    struct_fields: (ident * ty spanned) list;
}

type cmp_expr_ty =
    | Equal
    | NotEqual
    | Greater
    | GreaterEq
    | Less
    | LessEq

type arith_expr_ty =
    | Add
    | Sub
    | Mul
    | Div

type literal =
    | BoolLit of bool
    | IntLit of int
    | StringLit of string

type expr =
    | Or of expr spanned * expr spanned
    | And of expr spanned * expr spanned
    | Not of expr spanned
    | Neg of expr spanned
    | Cmp of cmp_expr_ty * expr spanned * expr spanned
    | Arith of arith_expr_ty * expr spanned * expr spanned
    | Literal of literal
    | Call of expr spanned * expr spanned list
    | Subscript of expr spanned * expr spanned
    | Projection of expr spanned * ident
    | Ident of ident
    | New of ty spanned
    | NewArray of expr spanned * ty spanned
    | Cast of expr spanned * ty spanned

type fun_decl = {
    fun_name: ident;
    fun_args: (ident * ty spanned) list;
    fun_retty: ty spanned option;
    fun_body: statement spanned list
}
and statement =
    | Return of expr spanned option
    | VarDecl of ident * expr spanned
    | Assign of expr spanned * expr spanned
    | If of expr spanned * statement spanned list * statement spanned list option
    | Loop of statement spanned list
    | Expr of expr spanned

type item =
    | TypeAlias of ident * ty spanned
    | StructDecl of struct_decl
    | FunDecl of fun_decl

type compilation_unit = item spanned list

let literal_to_string lit = 
    match lit with
    | BoolLit b -> "(bool " ^ (string_of_bool b) ^ ")" 
    | IntLit i -> "(int " ^ (string_of_int i) ^ ")"
    | StringLit s -> "(string \"" ^ s ^ "\")"

let rec ty_to_string ty = 
    match data_of ty with
    | ArrayTy t -> "(array " ^ (ty_to_string t) ^ ")"
    | NamedTy s -> "(named " ^ (data_of s) ^ ")"
    | AliasedTy (name, t) -> "(aliased " ^ (data_of name) ^ " " ^ (ty_to_string t) ^ ")" 

let rec expr_to_string_indent indent tree =
    let unindented = 
        match data_of tree with 
        | Or (lhs, rhs) -> 
            let lhs_str = expr_to_string_indent (indent + 1) lhs in
            let rhs_str = expr_to_string_indent (indent + 1) rhs in
            "(or\n" ^ lhs_str ^ "\n" ^ rhs_str ^ ")"
        | And (lhs, rhs) -> 
            let lhs_str = expr_to_string_indent (indent + 1) lhs in
            let rhs_str = expr_to_string_indent (indent + 1) rhs in
            "(and\n" ^ lhs_str ^ "\n" ^ rhs_str ^ ")"
        | Not expr ->
            "(not\n" ^ (expr_to_string_indent (indent + 1) expr) ^ ")"
        | Neg expr ->
            "(neg\n" ^ (expr_to_string_indent (indent + 1) expr) ^ ")"
        | Cmp (op, lhs, rhs) ->
            let lhs_str = expr_to_string_indent (indent + 1) lhs in
            let rhs_str = expr_to_string_indent (indent + 1) rhs in
            let op_str = 
                match op with
                | Equal -> "=="
                | NotEqual -> "!="
                | Greater -> ">"
                | GreaterEq -> ">="
                | Less -> "<"
                | LessEq -> "<="
            in
            "(" ^ op_str ^ "\n" ^ lhs_str ^ "\n" ^ rhs_str ^ ")"
        | Arith (op, lhs, rhs) -> 
            let lhs_str = expr_to_string_indent (indent + 1) lhs in
            let rhs_str = expr_to_string_indent (indent + 1) rhs in
            let op_str = 
                match op with
                | Add -> "+"
                | Sub -> "-"
                | Mul -> "*"
                | Div -> "/"
            in
            "(" ^ op_str ^ "\n" ^ lhs_str ^ "\n" ^ rhs_str ^ ")"
        | Literal lit -> literal_to_string lit
        | Call (base, args) -> 
            let base_str = expr_to_string_indent (indent + 1) base in
            let args_strs = List.map (expr_to_string_indent (indent + 1)) args in
            "(call\n" ^ base_str ^ "\n" ^ (String.concat "\n" args_strs) ^ ")"
        | Subscript (base, arg) ->
            let base_str = expr_to_string_indent (indent + 1) base in
            let arg_str = expr_to_string_indent (indent + 1) arg in
            "(subscript\n" ^ base_str ^ "\n" ^ arg_str ^ ")"
        | Projection (base, name) ->
            let base_str = expr_to_string_indent (indent + 1) base in
            "(projection\n" ^ base_str ^ "\n" ^ (String.make (indent + 1) ' ') ^ (data_of name) ^ ")"
        | Ident id -> "(ident " ^ (data_of id) ^ ")"
        | New ty -> "(new " ^ (ty_to_string ty) ^ ")"
        | NewArray (expr, ty) -> 
            let expr_str = expr_to_string_indent (indent + 1) expr in
            "(new-array " ^ (ty_to_string ty) ^ "\n" ^ expr_str ^ ")"
        | Cast (expr, ty) -> 
            let expr_str = expr_to_string_indent (indent + 1) expr in
            let ty_str = (String.make (indent + 1) ' ') ^ (ty_to_string ty) in
            "(cast " ^ expr_str ^ "\n" ^ ty_str ^ ")"
    in
    (String.make indent ' ') ^ unindented

let expr_to_string tree =
    expr_to_string_indent 0 tree

let rec statement_to_string_indent indent stmt =
    let unindented = 
        match data_of stmt with
        | Return None -> "(return)"
        | Return Some (expr) -> "(return\n" ^ (expr_to_string_indent (indent + 1) expr) ^ ")"
        | VarDecl (name, expr) ->
            let expr_str = expr_to_string_indent (indent + 1) expr in
            "(vardecl " ^ (data_of name) ^ "\n" ^ expr_str ^ ")"
        | Assign (var, expr) ->
            let var_str = expr_to_string_indent (indent + 1) var in
            let expr_str = expr_to_string_indent (indent + 1) expr in
            "(assign\n" ^ var_str ^ "\n" ^ expr_str ^ ")"
        | If (cond, true_b, None) ->
            let cond_str = expr_to_string_indent (indent + 1) cond in
            let body_strs = List.map (statement_to_string_indent (indent + 1)) true_b in
            "(if\n" ^ cond_str ^ "\n" ^ (String.concat "\n" body_strs) ^ ")"
        | If (cond, true_b, Some(false_b)) ->
            let cond_str = expr_to_string_indent (indent + 1) cond in
            let body_strs = List.map (statement_to_string_indent (indent + 1)) true_b in
            let false_body_strs = List.map (statement_to_string_indent (indent + 1)) false_b in
            "(if\n" ^ cond_str ^ "\n" ^ (String.concat "\n" body_strs) ^ "\n" ^ (String.concat "\n" false_body_strs) ^ ")"
        | Loop body ->
            let body_strs = List.map (statement_to_string_indent (indent + 1)) body in
            "(loop\n" ^ (String.concat "\n" body_strs) ^ ")"
        | Expr expr -> expr_to_string_indent indent expr
    in
    (String.make indent ' ') ^ unindented

let statement_to_string stmt =
    statement_to_string_indent 0 stmt


let struct_decl_to_string decl =
    let field_to_string ident ty =
        let ty_str = ty_to_string ty in
        " (field " ^ (data_of ident) ^ " " ^ ty_str ^ ")"
    in
    let fields_str = List.map (Util.uncurry field_to_string) decl.struct_fields in
    "(structdecl " ^ (data_of decl.struct_name) ^ "\n" ^ (String.concat "\n" fields_str) ^ ")"

let fun_decl_to_string decl =
    let param_to_string ident ty =
        let ty_str = ty_to_string ty in
        "  (param " ^ (data_of ident) ^ " " ^ ty_str ^ ")"
    in
    let retty_to_string maybe_ty = 
        match maybe_ty with
        | Some ty -> " (some " ^ (ty_to_string ty) ^ ")"
        | None -> " (none)"
    in
    let params_str = if List.length decl.fun_args == 0 
        then "  ()" 
        else String.concat "\n" (List.map (Util.uncurry param_to_string) decl.fun_args) in
    let retty_str = retty_to_string decl.fun_retty in
    let body = List.map (statement_to_string_indent 2) decl.fun_body in
    "(fundecl " ^ (data_of decl.fun_name) 
        ^ "\n (params\n" 
        ^ params_str 
        ^ ")\n"
        ^ retty_str
        ^ "\n (body\n"
        ^ (String.concat "\n" body)
        ^ "))"

let item_to_string item =
    match data_of item with
    | TypeAlias (name, ty) -> 
        let ty_str = ty_to_string ty in
        "(typealias " ^ (data_of name) ^ " " ^ ty_str ^ ")"
    | StructDecl decl -> struct_decl_to_string decl
    | FunDecl decl -> fun_decl_to_string decl

let compilation_unit_to_string cu =
    let items = List.map (item_to_string) cu in
    String.concat "\n" items