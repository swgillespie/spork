module TypecheckEnv : sig
    type t
    
    val create : Sema.State.t -> t
    val sema_state : t -> Sema.State.t
    val add_type_def : t -> string -> Sema.ty -> unit
    val update_type_def : t -> string -> Sema.ty -> unit
    val query_type : t -> Ast.ident -> Sema.ty

    val enter_scope : t -> unit
    val exit_scope : t -> unit
    val add_value_def : t -> string -> Sema.ty -> unit
    val has_value_def : t -> Ast.ident -> bool
    val query_value : t -> Ast.ident -> Sema.ty

    val set_current_function_return_ty : t -> Sema.ty -> unit
    val current_function_return_ty : t -> Sema.ty

    val type_env_to_string : t -> string
end = struct
    type t = {
        type_env: (string, Sema.ty) Hashtbl.t;
        value_env: (string, Sema.ty) Hashtbl.t list ref;
        state: Sema.State.t;
        curr_fn_type: Sema.ty ref;
    }

    let type_env_to_string state =
        Hashtbl.fold (fun k v acc -> "(" ^ k ^ "," ^ Sema.ty_to_string v ^ ")" ^ acc) state.type_env ""

    let create sema_state = {
        type_env = Hashtbl.create 20;
        value_env = ref [Hashtbl.create 20];
        state = sema_state;
        curr_fn_type = ref Sema.VoidTy
    }

    let sema_state t = t.state

    let add_type_def state s t = 
        Hashtbl.add state.type_env s t

    let update_type_def state s t =
        Hashtbl.remove state.type_env s;
        Hashtbl.add state.type_env s t

    let query_type state s = 
        try Hashtbl.find state.type_env (Span.data_of s) with
        | Not_found -> Sema.raise_error s "unbound type identifier"

    let enter_scope state = 
        state.value_env := Hashtbl.create 20 :: !(state.value_env)

    let exit_scope state = 
        state.value_env := List.tl !(state.value_env)

    let add_value_def state s t = 
        Hashtbl.add (List.hd !(state.value_env)) s t

    let has_value_def state s =
        let rec find h s =
            match h with
            | [] -> false
            | x :: xs -> Hashtbl.mem x (Span.data_of s) || find xs s in
        find !(state.value_env) s

    let query_value state s =
        let rec find h s =
            match h with
            | [] -> Sema.raise_error s "unbound identifier"
            | x :: xs -> try Hashtbl.find x (Span.data_of s) with Not_found -> find xs s in
        find !(state.value_env) s

    let set_current_function_return_ty state ty = 
        state.curr_fn_type := ty

    let current_function_return_ty state = !(state.curr_fn_type)
end

(* 
    An aside:

    The Spork compiler is a multi-pass compiler, which means that it
    attempts to view the program as a whole by performing multiple passes
    over the source program instead of just one. This maniests most clearly
    during the semantic analysis phase, which is performed in three passes. 
    The fact that we are compiling in multiple passes means that we have 
    the ability to consider items /independant from the order in which they 
    were declared/, unlike languages like C, C++, or Pascal.

    Semantic analysis in the Spork compiler is done in three passes:
      Pass 1: The compiler looks at all struct definitions and makes note
              of the names of the structs that are declared.
      Pass 2: The compiler looks at all of the fields in each struct definition
              and ensures that each type referenced by a field exists. The compiler
              also looks at every function signature and ensures that every type
              (argument types and return type) exists. The compiler makes note of
              the names and types of all functions.
      Pass 3: The compiler assigns types to all expressions in the program.

    Passes 2 and 3 will raise errors if it observes something that does not
    type check. For Pass 2, the only errors that are thrown are when a type
    is referenced that does not exist. Pass 3 will enforce all other typing rules.
*)

(* pass 1 - gather the defs of all structs and insert them into
   the type environment. *)
let gather_item_def_struct state decl = 
    (* only record the name now, in the first pass - we'll fill in 
       the fields later. *)
    let name = Span.data_of decl.Ast.struct_name in
    TypecheckEnv.add_type_def state name (Sema.AggregateTy name);;

let gather_item_def state item =
    match (Span.data_of item) with
    | Ast.StructDecl decl -> gather_item_def_struct state decl
    | Ast.FunDecl decl -> ()
    | Ast.TypeAlias _ -> Util.raise_bug_spanned item "failed to eliminate type alias"

let pass_1_gather_defs state cu = List.iter (gather_item_def state) cu
(* -- end pass 1 -- *)


(* pass 2 - gather all function types, fill in the bodies of all structs *)
let rec ast_ty_to_sema_ty state ty =
    (* TODO better error message for Aliased types *)
    match (Span.data_of ty) with
    | Ast.ArrayTy t -> Sema.ArrayTy (ast_ty_to_sema_ty state t)
    | Ast.AliasedTy (_, t) -> ast_ty_to_sema_ty state t
    | Ast.NamedTy n -> TypecheckEnv.query_type state n


let fill_struct_body state decl =
    let convert_struct_field state (id, ty) =
        (Span.data_of id, ast_ty_to_sema_ty state ty) in
    (* we can replace the struct's body now with its fields. 
       this is the first place we will raise a type error. *)
    let fields = List.map (convert_struct_field state) decl.Ast.struct_fields in
    let name = Span.data_of decl.Ast.struct_name in
    Sema.State.set_struct_fields (TypecheckEnv.sema_state state) name fields;;

let record_function_signature state decl =
    let record_argument state (_, ty) =
       ast_ty_to_sema_ty state ty in

    let args = List.map (record_argument state) decl.Ast.fun_args in
    let actual_ty = 
        match decl.Ast.fun_retty with
        | Some ty -> ast_ty_to_sema_ty state ty
        | None -> Sema.VoidTy in
    let name = Span.data_of decl.Ast.fun_name in
    if TypecheckEnv.has_value_def state decl.Ast.fun_name 
    then Sema.raise_error (decl.Ast.fun_name) "duplicate function definitions";
    TypecheckEnv.add_value_def state name (Sema.FunctionTy (args, actual_ty));;

let pass_2_visit_item state item =
    match (Span.data_of item) with
    | Ast.StructDecl decl -> fill_struct_body state decl
    | Ast.FunDecl decl -> record_function_signature state decl
    | Ast.TypeAlias _ -> Util.raise_bug_spanned item "failed to eliminate type alias" 

let pass_2_gather_defs state cu = List.iter (pass_2_visit_item state) cu
(* -- end pass 2 -- *)

let type_of state expr =
    Sema.State.get_expr_type (TypecheckEnv.sema_state state) (Span.data_of expr)

let set_type state expr ty =
    Sema.State.set_expr_type (TypecheckEnv.sema_state state) (Span.data_of expr) ty

let check_types state expr expected_ty =
    if (type_of state expr) <> expected_ty 
    then Sema.raise_error expr (Printf.sprintf 
        "mismatched types: expected type `%s`, got type `%s`" 
        (Sema.ty_to_string expected_ty) 
        (Sema.ty_to_string (type_of state expr)))

let check_not_void state expr =
    if Sema.ty_is_void (type_of state expr)
    then Sema.raise_error expr "this expression has type `void`, which is not assignable"

let find_field_by_name state ty_name name =
    let fields = Sema.State.get_struct_fields (TypecheckEnv.sema_state state) ty_name in
    try List.assoc (Span.data_of name) fields with
    | Not_found -> Sema.raise_error name ("no field of name `" ^ (Span.data_of name) ^ "` on type `struct " ^ ty_name ^ "`")

let check_assignment state lvalue rvalue =
    match (Span.data_of lvalue) with
    | Ast.Projection (_, _)
    | Ast.Subscript (_, _) ->
      (* the type of values assignable to an lvalue matchs the type
         of the value obtained when using this lvalue as an rvalue,
         so we can do this here *)
      let desired_type = type_of state lvalue in
      check_types state rvalue desired_type;
    | Ast.Ident ident ->
      let ty = TypecheckEnv.query_type state ident in
      check_types state rvalue ty;
    | _ -> Sema.raise_error lvalue "invalid expression on left-hand-side of assignment"

let rec typecheck_expr state expr = 
    match (Span.data_of expr) with
    | Ast.Or (lhs, rhs) | Ast.And (lhs, rhs) ->
        typecheck_expr state lhs;
        typecheck_expr state rhs;
        check_types state lhs Sema.BoolTy;
        check_types state rhs Sema.BoolTy;
        set_type state expr Sema.BoolTy;
    | Ast.Not e -> 
        typecheck_expr state e;
        check_types state e Sema.BoolTy;
        set_type state expr Sema.BoolTy;
    | Ast.Neg e ->
        typecheck_expr state e;
        check_types state e Sema.IntTy;
        set_type state expr Sema.IntTy;
    | Ast.Cmp (Ast.Equal, lhs, rhs) | Ast.Cmp (Ast.NotEqual, lhs, rhs) ->
        (* equality can be between /any/ two types, 
           as long as they are the same type *)
        typecheck_expr state lhs;
        typecheck_expr state rhs;
        check_types state lhs (type_of state rhs);
        check_types state rhs (type_of state lhs);
        set_type state expr Sema.BoolTy;
    | Ast.Cmp (_, lhs, rhs) ->
        (* comparison and arithmetic ops are only for ints *)
        typecheck_expr state lhs;
        typecheck_expr state rhs;
        check_types state lhs Sema.IntTy;
        check_types state rhs Sema.IntTy;
        set_type state expr Sema.BoolTy;
    | Ast.Arith (_, lhs, rhs) ->
        typecheck_expr state lhs;
        typecheck_expr state rhs;
        check_types state lhs Sema.IntTy;
        check_types state rhs Sema.IntTy;
        set_type state expr Sema.IntTy;
    | Ast.Literal (Ast.BoolLit _) ->
        set_type state expr Sema.BoolTy;
    | Ast.Literal (Ast.IntLit _) ->
        set_type state expr Sema.IntTy;
    | Ast.Literal (Ast.StringLit _) ->
        set_type state expr Sema.StringTy;
    | Ast.Call (base, args) ->
        let check_argument state (expr, expected_ty) =
            check_types state expr expected_ty;
        in
        typecheck_expr state base;
        List.iter (typecheck_expr state) args;
        let (arg_tys, ret_ty) = 
            match (type_of state base) with
            | Sema.FunctionTy (a, t) -> (a, t)
            | _ -> Sema.raise_error base "called value is not a function"
        in
        (* all argument types must match the function type
           being called *)
        let args = List.combine args arg_tys in
        List.iter (check_argument state) args;
        (* then the result of this expression is the result
           of the call *)
        set_type state expr ret_ty;
    | Ast.Subscript (base, idx) ->
        typecheck_expr state base;
        typecheck_expr state idx;
        check_types state idx Sema.IntTy;
        let array_elem_ty = match (type_of state base) with
        | Sema.ArrayTy ty -> ty
        | _ -> Sema.raise_error base "subscripted value is not an array" in
        set_type state expr array_elem_ty;
    | Ast.Projection (base, name) ->
        typecheck_expr state base;
        let agg_ty = match (type_of state base) with
        | Sema.AggregateTy ty_name -> find_field_by_name state ty_name name
        | _ -> Sema.raise_error base "base of projection not of aggregate type" in
        set_type state expr agg_ty;
    | Ast.Ident name ->
        set_type state expr (TypecheckEnv.query_value state name)
    | Ast.New ty -> 
        let lower_ty = ast_ty_to_sema_ty state ty in
        if not (Sema.ty_is_aggregate lower_ty)
        then Sema.raise_error ty "non-struct types cannot be used as the type of a `new` expression";
        set_type state expr lower_ty;
    | Ast.NewArray (count, ty) ->
        typecheck_expr state count;
        check_types state count Sema.IntTy;
        let lower_ty = ast_ty_to_sema_ty state ty in
        if Sema.ty_is_void lower_ty
        then Sema.raise_error ty "`void` cannot be used as the type of a `new` expression";
        set_type state expr (Sema.ArrayTy lower_ty);
    | Ast.Cast (_, _) -> Util.nyi "casting"

and typecheck_stmt state stmt = 
    match (Span.data_of stmt) with
    | Ast.Return None -> 
        (* bare returns are only permitted when the return
           type is void *)
        if not (Sema.ty_is_void (TypecheckEnv.current_function_return_ty state))
        then Sema.raise_error stmt "bare return in non-void function"
    | Ast.Return (Some expr) ->
        (* the expression given in Return position must be the same type
           as the return type. *)
        typecheck_expr state expr;
        check_types state expr (TypecheckEnv.current_function_return_ty state);
    | Ast.VarDecl (name, binding) ->
        typecheck_expr state binding;
        check_not_void state binding;
        TypecheckEnv.add_value_def state (Span.data_of name) (type_of state binding);
    | Ast.Assign (name, binding) ->
        typecheck_expr state name;
        typecheck_expr state binding;
        check_assignment state name binding;
    | Ast.If (cond, t_b, f_b) ->
        typecheck_expr state cond;
        TypecheckEnv.enter_scope state;
        typecheck_body state t_b;
        TypecheckEnv.exit_scope state;
        TypecheckEnv.enter_scope state;
        Util.opt_iter (typecheck_body state) f_b;
        TypecheckEnv.exit_scope state;
        (* condition must have type bool *)
        check_types state cond Sema.BoolTy;
    | Ast.Loop body ->
        TypecheckEnv.enter_scope state;
        typecheck_body state body;
        TypecheckEnv.exit_scope state;
    | Ast.Expr expr ->
        typecheck_expr state expr;

and typecheck_body state body = List.iter (typecheck_stmt state) body

let typecheck_fun state decl =
    let add_argument_to_env state (ty, (ident, _)) =
        TypecheckEnv.add_value_def state (Span.data_of ident) ty in

    let fun_ty = TypecheckEnv.query_value state decl.Ast.fun_name in
    (* record the return type in the state. This is used to typecheck
       Return statements *)
    let (args_tys, ret_ty) =
        match fun_ty with
        | Sema.FunctionTy (a, r) -> (a, r)
        | _ -> Util.raise_bug "function assigned non-function type" in
    TypecheckEnv.set_current_function_return_ty state ret_ty;
    (* add all of the fields as identifiers in child scope,
       with the given type assigned to them *)
    TypecheckEnv.enter_scope state;
    let args = List.combine args_tys decl.Ast.fun_args in
    List.iter (add_argument_to_env state) args;
    (* typecheck the body *)
    typecheck_body state decl.Ast.fun_body;
    (* exit the new scope *)
    TypecheckEnv.exit_scope state;;


let pass_3_typecheck state cu = 
    let typecheck_single_item state item =
        match (Span.data_of item) with
        | Ast.FunDecl decl -> typecheck_fun state decl
        | _ -> ()
    in
    List.iter (typecheck_single_item state) cu
(* -- end pass 3 --*)

let run state cu = 
    let tce = TypecheckEnv.create state in
    (* load up our builtin types *)
    TypecheckEnv.add_type_def tce "int" Sema.IntTy;
    TypecheckEnv.add_type_def tce "bool" Sema.BoolTy;
    TypecheckEnv.add_type_def tce "string" Sema.StringTy;
    pass_1_gather_defs tce cu;
    pass_2_gather_defs tce cu;
    pass_3_typecheck tce cu;
    cu