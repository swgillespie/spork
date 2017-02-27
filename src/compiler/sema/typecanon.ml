open Ast

module TypeSet = Set.Make(
    struct
        let compare = Pervasives.compare
        type t = string
    end)

let new_type_set () =
    let ts = TypeSet.empty in
    let ts' = TypeSet.add "int" ts in
    let ts'' = TypeSet.add "bool" ts' in
    let ts''' = TypeSet.add "string" ts'' in
    ts'''

(* gather all of the type defs in this program into a set *)
let gather_defs cu =
    let rec gather_defs_loop acc = function
        | TypeAlias (name, _) :: xs -> 
            if TypeSet.mem (Span.data_of name) acc 
            then Sema.raise_error name "duplicate type definition"
            else gather_defs_loop (TypeSet.add (Span.data_of name) acc) xs
        | StructDecl decl :: xs -> 
            let name = Span.data_of (decl.Ast.struct_name) in
            if TypeSet.mem name acc 
            then Sema.raise_error decl.Ast.struct_name "duplicate type definition"
            else gather_defs_loop (TypeSet.add name acc) xs
        | _ :: xs -> gather_defs_loop acc xs
        | [] -> acc
    in
    gather_defs_loop (new_type_set ()) cu

(* every type in Spork is ultimately backed by a named type.
   this function returns it. *)
let rec get_named_type = function
    | ArrayTy ty -> get_named_type (Span.data_of ty)
    | NamedTy name -> name
    | AliasedTy (name, ty) -> get_named_type (Span.data_of ty) 

(* checks for aliases to types that do not exist *)
let check_for_invalid_aliases set cu =
    let check_single_alias set alias =
        match (Span.data_of alias) with
        | TypeAlias (name, ty) -> 
            let named_ty = get_named_type (Span.data_of ty) in
            if not (TypeSet.mem (Span.data_of named_ty) set)
            then Sema.raise_error ty "unknown type on right-hand-side of type alias"
            else ()
        | _ -> ()
    in
    List.iter (check_single_alias set) cu

let rec substitute_ty name alias ty = 
    match (Span.data_of ty) with
    | NamedTy n when Span.data_of n = name -> Span.spanned_of (AliasedTy (n, alias)) (Span.span_of n) 
    | ArrayTy t -> Span.spanned_of (ArrayTy (substitute_ty name alias t)) (Span.span_of ty)
    | AliasedTy (n, t) -> Span.spanned_of (AliasedTy (n, substitute_ty name alias t)) (Span.span_of ty)
    | _ -> ty

let rec substitute_expr name alias expr = 
    let trans = match (Span.data_of expr) with
    | Or (l, r) -> Or ((substitute_expr name alias l), (substitute_expr name alias r))
    | And (l, r) -> And ((substitute_expr name alias l), (substitute_expr name alias r))
    | Not o -> Not (substitute_expr name alias o)
    | Neg o -> Neg (substitute_expr name alias o)
    | Cmp (op, l, r) -> Cmp (op, (substitute_expr name alias l), (substitute_expr name alias r))
    | Arith (op, l, r) -> Arith (op, (substitute_expr name alias l), (substitute_expr name alias r))
    | Call (base, args) -> Call ((substitute_expr name alias base), (List.map (substitute_expr name alias) args))
    | Subscript (base, arg) -> Subscript ((substitute_expr name alias base), (substitute_expr name alias arg))
    | Projection (base, i) -> Projection ((substitute_expr name alias base), i) 
    | New ty -> New (substitute_ty name alias ty)
    | NewArray (expr, ty) -> NewArray (substitute_expr name alias expr, substitute_ty name alias ty)
    | Cast (expr, ty) -> Cast (substitute_expr name alias expr, substitute_ty name alias ty)
    | Ident _ as e -> e
    | Literal _ as e -> e 
    in
    Span.spanned_of trans (Span.span_of expr)

let rec substitute_stmt name alias stmt = 
    let trans = match (Span.data_of stmt) with
    | Return (Some e) -> Return (Some (substitute_expr name alias e))
    | VarDecl (i, e) -> VarDecl (i, substitute_expr name alias e)
    | Assign (i, e) -> Assign (i, substitute_expr name alias e)
    | If (e, tr_b, fls_b) -> 
        let cond = substitute_expr name alias e in
        let tr_b_subst = List.map (substitute_stmt name alias) tr_b in
        let fls_b_subst = match fls_b with
        | Some s -> Some (List.map (substitute_stmt name alias) s)
        | None -> None in
        If (cond, tr_b_subst, fls_b_subst)
    | Loop stmts -> Loop (List.map (substitute_stmt name alias) stmts)
    | Expr e -> Expr (substitute_expr name alias e)
    | s -> s
    in
    Span.spanned_of trans (Span.span_of stmt)

let substitute_struct_decl name alias decl =
    {
        struct_name = decl.struct_name;
        struct_fields = List.map (fun (i, ty) -> (i, substitute_ty name alias ty)) decl.struct_fields;
    }

let substitute_fun_decl name alias decl =
    {
        fun_name = decl.fun_name;
        fun_args = List.map (fun (i, ty) -> (i, substitute_ty name alias ty)) decl.fun_args;
        fun_retty = Util.opt_map (substitute_ty name alias) decl.fun_retty;
        fun_body = List.map (substitute_stmt name alias) decl.fun_body;
    }

let substitute_item name alias item =
    let trans = match (Span.data_of item) with
    | TypeAlias (i, ty) -> TypeAlias (i, substitute_ty name alias ty)
    | StructDecl decl -> StructDecl (substitute_struct_decl name alias decl)
    | FunDecl decl -> FunDecl (substitute_fun_decl name alias decl)
    in
    Span.spanned_of trans (Span.span_of item)

(* perform the substitution of the candidate alias into the rest of the program,
   after doing a cycle check. *)
let run_single_step candidate cu = 
    let (name, ty) = match candidate with
    | TypeAlias (n, t) -> (n, t)
    | _ -> Util.raise_bug "run_single_step candidate not a TypeAlias"
    in
    let target_name = get_named_type (Span.data_of ty) in
    (* this produces a pair of strings, name and target_name, that
       represent the core of the substitution that is going to occur.
       If we are ever in a situation where target_name and name are
       the same, we have a cycle in our type aliases. *)
    if (Span.data_of name) = (Span.data_of target_name)
    then Sema.raise_error name "invalid cyclical type alias"
    (* perform the type substitution. *)
    else List.map (substitute_item (Span.data_of name) ty) cu

(* to resolve all aliases, we'll repeatedly take a type alias
   out of the compilation unit and perform the type substitution. *)
let resolve_aliases cu = 
    (* splits a compilation unit into an alias and the rest of the CU.
       if an alias was found, the substitution is performed. This continues
       until there are no more aliases *)
    let rec split_by_alias cu acc =
        match cu with
        | [] -> (None, acc)
        | x :: xs -> 
            match (Span.data_of x) with
            | TypeAlias (_, _) as alias -> (Some alias, acc @ xs)
            | _ -> split_by_alias xs (x :: acc)        
    in
    let rec loop cu =
        match split_by_alias cu [] with
        | (Some alias, xs) -> 
            let cu' = run_single_step alias xs in
            loop cu'
        | (None, xs) -> xs in
    loop cu

let assert_no_aliases cu =
    let assert_not_alias item =
        match (Span.data_of item) with
        | TypeAlias (i, _) -> Util.raise_bug_spanned i "Typecanon failed to remove a type alias"
        | _ -> ()
    in
    List.iter assert_not_alias cu 

let run _ cu = 
    let defs = gather_defs (List.map Span.data_of cu) in
    (* raise an error if any types refer to nonexistent types *)
    check_for_invalid_aliases defs cu;
    (* perform type alias substitution *)
    let result = resolve_aliases cu in
    (* assert we removed all type aliases *)
    assert_no_aliases result;
    result
