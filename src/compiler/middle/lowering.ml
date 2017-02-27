open Trans

module TranslateEnv (F: Trans.Frame) : sig
    type t

    val create : Sema.State.t -> t
    val sema_state : t -> Sema.State.t

    val size_of : t -> Sema.ty -> int
    val get_field_offset : t -> Sema.ty -> string -> int
    val calculate_layout : t -> Ast.struct_decl -> unit

    val enter_scope : t -> unit
    val exit_scope : t -> unit
    val add_value : t -> string -> F.access -> unit
    val has_value : t -> string -> bool
    val get_value : t -> string -> F.access

    val add_fragment : t -> F.fragment -> unit
    val fragments : t -> F.fragment list

    val get_return_reg : t -> Temp.reg
    val set_return_reg : t -> Temp.reg -> unit

    val get_return_label : t -> Temp.label
val set_return_label : t -> Temp.label -> unit
end = struct
    type layout = {
        field_map: (string, int) Hashtbl.t;
        size: int
    }

    type t = {
        layout_env: (string, layout) Hashtbl.t;
        value_env: (string, F.access) Hashtbl.t list ref;
        sema_state: Sema.State.t;
        fragments: F.fragment list ref;
        return_reg: Temp.reg ref;
        return_lbl: Temp.label ref;
    }

    let create state = {
        layout_env = Hashtbl.create 20;
        value_env = ref [Hashtbl.create 20];
        sema_state = state;
        fragments = ref [];
        return_reg = ref (Temp.new_reg ());
        return_lbl = ref (Temp.new_label ());
    }

    let sema_state state = state.sema_state

    let size_of state ty = 
        match ty with
        | Sema.AggregateTy name -> 
            let layout = Hashtbl.find state.layout_env name in
            layout.size
        | _ -> F.word_size

    let get_field_offset state ty name = 
        let layout = match ty with
        | Sema.AggregateTy name -> Hashtbl.find state.layout_env name
        | _ -> Util.raise_bug "get_field_offset called on non-struct type" in
        try Hashtbl.find layout.field_map name 
        with Not_found -> Util.raise_bug "get_field_offset called with invalid field"

    let calculate_layout state decl = 
        (* 
           by default, /all/ types have pointer alignment. therefore, 
           calculating layout is easy for us - we just sum up the number
           of fields.
           
           this task would be considerably more difficult if we had types
           of differing sizes, but this is an educational compiler and we're
           going to keep things simple 
        *)
        let offset = ref 0 in
        let calculate_single_field state map (name, ty) = 
            Hashtbl.add map name !offset;
            let size = size_of state ty in
            offset := size + !offset;
        in

        let layout = Hashtbl.create 20 in
        let name = Span.data_of (decl.Ast.struct_name) in
        List.iter (calculate_single_field state layout) (Sema.State.get_struct_fields state.sema_state name);
        Hashtbl.add state.layout_env name { field_map = layout; size = !offset; }

    let enter_scope state =
        state.value_env := Hashtbl.create 20 :: !(state.value_env)

    let exit_scope state = 
        state.value_env := List.tl !(state.value_env)

    let add_value state name access =
        Hashtbl.add (List.hd !(state.value_env)) name access

    let has_value state name =
        let rec find h s =
            match h with
            | [] -> false
            | x :: xs -> Hashtbl.mem x s || find xs s
        in
        find !(state.value_env) name

    let get_value state name = 
        let rec find h s =
            match h with
            | [] -> Util.raise_bug ("unbound identifier in lowering: " ^ s)
            | x :: xs -> try Hashtbl.find x s with Not_found -> find xs s in
        find !(state.value_env) name

    let add_fragment t frag =
        t.fragments := frag :: !(t.fragments)

    let fragments t = !(t.fragments)

    let get_return_reg t = !(t.return_reg)

    let set_return_reg t r = 
        t.return_reg := r

    let get_return_label t = !(t.return_lbl)
    let set_return_label t l = 
        t.return_lbl := l
end

module Translate (F : Trans.Frame) = struct
    module Env = TranslateEnv(F)

    let type_of state expr =
        Sema.State.get_expr_type (Env.sema_state state) (Span.data_of expr)

    let pass_1_type_layouts state cu =
        let calculate_layout state item = 
            match (Span.data_of item) with
            | Ast.StructDecl decl -> Env.calculate_layout state decl
            | _ -> () in
        List.iter (calculate_layout state) cu

    let array_size arr_ir = Ir.Mem arr_ir
    let array_data arr_ir = Ir.Mem (Ir.Binop (Ir.Plus, Ir.ConstInt F.word_size, arr_ir))

    let rec trans_aggregate_equality state frame lhs rhs =
        let lhs_ir = Ir.unwrap_ex (trans_expr state frame lhs) in
        let rhs_ir = Ir.unwrap_ex (trans_expr state frame rhs) in 
        let size = Env.size_of state (type_of state lhs) in
        let memcmp_lbl = Temp.new_named_label "spork_memcmp" in
        let call = Ir.Call (Ir.Name memcmp_lbl, [lhs_ir; rhs_ir; Ir.ConstInt size]) in
        Ir.Cx (fun (true_b, false_b) ->
            (* memcmp returns zero if the strings are equal *)
            Ir.CJump (Ir.Eq, Ir.ConstInt 0, call, true_b, false_b)
        )

    and trans_array_equality state frame lhs rhs = 
        let lhs_ir = Ir.unwrap_ex (trans_expr state frame lhs) in
        let rhs_ir = Ir.unwrap_ex (trans_expr state frame rhs) in
        let next_label = Temp.new_label () in
        let size_reg = Temp.new_reg () in
        let memcmp_lbl = Temp.new_named_label "spork_memcmp" in
        let call = fun size -> Ir.Call (Ir.Name memcmp_lbl, [array_data lhs_ir; array_data rhs_ir; size]) in
        Ir.Cx (fun (true_b, false_b) ->
            Ir.seq [
                Ir.Move (Ir.Temp size_reg, array_size lhs_ir);
                Ir.CJump (Ir.Eq, Ir.Temp size_reg, array_size rhs_ir, next_label, false_b);
                Ir.Label next_label;
                Ir.CJump (Ir.Eq, Ir.ConstInt 0, call (Ir.Temp size_reg), true_b, false_b)
            ]
        )

    and trans_string_equality state frame lhs rhs = Util.nyi "string equality"
    
    and trans_equality state frame lhs rhs = 
        (* equality is defined for any type. it is here that
            we have to decide /which kind/ of equality we want. *)
        match (type_of state lhs) with
        | Sema.AggregateTy _ -> trans_aggregate_equality state frame lhs rhs
        | Sema.ArrayTy _ -> trans_array_equality state frame lhs rhs
        | Sema.StringTy -> trans_string_equality state frame lhs rhs
        | _ -> 
            (* everything else is word-sized and can be compared directly *)
            let lhs_ir = Ir.unwrap_ex (trans_expr state frame lhs) in
            let rhs_ir = Ir.unwrap_ex (trans_expr state frame rhs) in
            Ir.Cx (fun (true_b, false_b) ->
                Ir.CJump (Ir.Eq, lhs_ir, rhs_ir, true_b, false_b)
            )

    and trans_expr state frame expr =
        match (Span.data_of expr) with
        | Ast.Or (lhs, rhs) ->
            let lhs_ir = Ir.unwrap_cx (trans_expr state frame lhs) in
            let rhs_ir = Ir.unwrap_cx (trans_expr state frame rhs) in
            let next_label = Temp.new_label () in
            Ir.Cx (fun (true_b, false_b) ->
                Ir.seq [
                    lhs_ir (true_b, next_label);
                    Ir.Label next_label;
                    rhs_ir (true_b, false_b);
                ]
            )
        | Ast.And (lhs, rhs) ->
            let lhs_ir = Ir.unwrap_cx (trans_expr state frame lhs) in
            let rhs_ir = Ir.unwrap_cx (trans_expr state frame rhs) in
            let next_label = Temp.new_label () in
            Ir.Cx (fun (true_b, false_b) ->
                Ir.seq [
                    lhs_ir (next_label, false_b);
                    Ir.Label next_label;
                    rhs_ir (true_b, false_b)
                ]
            )
        | Ast.Not e ->
            let e_ir = Ir.unwrap_cx (trans_expr state frame e) in
            Ir.Cx (fun (true_b, false_b) ->
                e_ir (false_b, true_b)
            )
        | Ast.Neg e ->
            let e_ir = Ir.unwrap_ex (trans_expr state frame e) in
            Ir.Ex (Ir.Binop (Ir.Minus, Ir.ConstInt 0, e_ir))
        | Ast.Cmp (Ast.Equal, lhs, rhs) -> trans_equality state frame lhs rhs
        | Ast.Cmp (Ast.NotEqual, lhs, rhs) ->
            let eq_ir = Ir.unwrap_cx (trans_equality state frame lhs rhs) in
            Ir.Cx (fun (true_b, false_b) -> eq_ir (false_b, true_b))
        | Ast.Cmp (op, lhs, rhs) -> 
            let ir_op = 
                match op with
                | Ast.Greater -> Ir.Gt
                | Ast.GreaterEq -> Ir.GtEq
                | Ast.Less -> Ir.Lt
                | Ast.LessEq -> Ir.LtEq
                | _ -> Util.raise_bug "unexpected comparison operation" in
            let lhs_ir = Ir.unwrap_ex (trans_expr state frame lhs) in
            let rhs_ir = Ir.unwrap_ex (trans_expr state frame rhs) in
            Ir.Cx (fun (true_b, false_b) -> 
                Ir.CJump (ir_op, lhs_ir, rhs_ir, true_b, false_b)
            )
        | Ast.Arith (op, lhs, rhs) ->
            let ir_op =
                match op with
                | Ast.Add -> Ir.Plus
                | Ast.Sub -> Ir.Minus
                | Ast.Mul -> Ir.Mul
                | Ast.Div -> Ir.Div in
            let lhs_ir = Ir.unwrap_ex (trans_expr state frame lhs) in
            let rhs_ir = Ir.unwrap_ex (trans_expr state frame rhs) in
            Ir.Ex (Ir.Binop (ir_op, lhs_ir, rhs_ir))
        | Ast.Literal (Ast.BoolLit true) -> Ir.Ex (Ir.ConstInt 1)
        | Ast.Literal (Ast.BoolLit false) -> Ir.Ex (Ir.ConstInt 0)
        | Ast.Literal (Ast.IntLit i) -> Ir.Ex (Ir.ConstInt i)
        | Ast.Literal (Ast.StringLit s) ->
            let str_label = Temp.new_label () in
            Env.add_fragment state (F.String (str_label, s));
            Ir.Ex (Ir.Name str_label)
        | Ast.Call (base, args) ->
            let base_ir = Ir.unwrap_ex (trans_expr state frame base) in
            let args_ir = List.map (trans_expr state frame) args in
            Ir.Ex (Ir.Call (base_ir, List.map (Ir.unwrap_ex) args_ir))
        | Ast.Subscript (base, idx) ->
            let base_ir = Ir.unwrap_ex (trans_expr state frame base) in
            let idx_ir = Ir.unwrap_ex (trans_expr state frame idx) in
            let base_ty = Sema.get_base_ty (type_of state base) in
            let multiplier = Ir.ConstInt (Env.size_of state base_ty) in
            (* idx refers to the "i'th element" of the array, so we need
               to do base + (idx * size of array element)

               a quick digression about the memory layout of arrays:
               in spork, arrays are variably-sized structures always
               used behind a pointer. The layout of the VSS is this:
               struct array {
                   int length:
                   void[] data;
               }

               that is, the length is the first word of the structure and
               the data is the rest. Here, since we are indexing into
               the array, we need to do our pointer arithmetic on the
               second field, one word past the start of the array. *)
            Ir.Ex (Ir.Mem (Ir.Binop (Ir.Plus, array_data base_ir, Ir.Binop (Ir.Mul, idx_ir, multiplier))))
        | Ast.Projection (base, name) ->
            let base_ir = Ir.unwrap_ex (trans_expr state frame base) in
            let offset = Env.get_field_offset state (type_of state base) (Span.data_of name) in
            Ir.Ex (Ir.Mem (Ir.Binop (Ir.Plus, base_ir, Ir.ConstInt offset)))
        | Ast.Ident i ->
            if Env.has_value state (Span.data_of i) 
            then
                let access = Env.get_value state (Span.data_of i) in
                Ir.Ex (F.expr_of_access access)
            else
                (* it must be a function. *)
                Ir.Ex (Ir.Name (Temp.new_named_label (Span.data_of i)))
        | Ast.New ty ->
            let actual_ty = type_of state expr in
            let size = Env.size_of state actual_ty in
            let alloc_fun = Temp.new_named_label "spork_malloc" in
            Ir.Ex (Ir.Call (Ir.Name alloc_fun, [Ir.ConstInt size]))
        | Ast.NewArray (num, ty) ->
            let actual_ty = Sema.get_base_ty (type_of state expr) in
            let size = Env.size_of state actual_ty in
            let num_ir = Ir.unwrap_ex (trans_expr state frame num) in
            let alloc_fun = Temp.new_named_label "spork_array_malloc" in
            Ir.Ex (Ir.Call (Ir.Name alloc_fun, [num_ir; Ir.ConstInt size]))
        | Ast.Cast _ -> Util.nyi "casting"

    let rec trans_statement state frame stmt = 
        match (Span.data_of stmt) with
        | Ast.Return (Some expr) ->
            let expr_ir = trans_expr state frame expr in
            let ret_reg = Env.get_return_reg state in
            let ret_lbl = Env.get_return_label state in
            Ir.seq [
                Ir.Move (Ir.Temp ret_reg, Ir.unwrap_ex expr_ir);
                Ir.Jump (Ir.Name ret_lbl, [ret_lbl]);
            ]
        | Ast.Return None ->
            let ret_lbl = Env.get_return_label state in
            Ir.Jump (Ir.Name ret_lbl, [ret_lbl])
        | Ast.VarDecl (ident, expr) ->
            let alloca = F.alloc_local frame in
            Env.add_value state (Span.data_of ident) alloca;
            let expr_ir = trans_expr state frame expr in
            Ir.Move (F.expr_of_access alloca, Ir.unwrap_ex expr_ir)
        | Ast.Assign (lvalue, rvalue) ->
            let lvalue_ir = trans_expr state frame lvalue in
            let rvalue_ir = trans_expr state frame rvalue in
            Ir.Move (Ir.unwrap_ex lvalue_ir, Ir.unwrap_ex rvalue_ir)
        | Ast.If (cond, t_branch, None) ->
            let cond_ir = Ir.unwrap_cx (trans_expr state frame cond) in
            let true_label = Temp.new_label () in
            let false_label = Temp.new_label () in
            let true_branch = trans_statement_list state frame t_branch in 
            Ir.seq [
                cond_ir (true_label, false_label);
                Ir.Label true_label;
                true_branch;
                Ir.Label false_label;
            ]
        | Ast.If (cond, t_branch, Some f_branch) ->
            let cond_ir = Ir.unwrap_cx (trans_expr state frame cond) in
            let true_label = Temp.new_label () in
            let false_label = Temp.new_label () in
            let done_label = Temp.new_label () in
            let true_branch = trans_statement_list state frame t_branch in 
            let false_branch = trans_statement_list state frame f_branch in
            Ir.seq [
                cond_ir (true_label, false_label);
                Ir.Label false_label;
                false_branch;
                Ir.Jump (Ir.Name done_label, [done_label]);
                Ir.Label true_label;
                true_branch;
                Ir.Label done_label;
            ]
        | Ast.Loop body ->
            let body_ir = trans_statement_list state frame body in
            let loop_label = Temp.new_label () in
            Ir.seq [
                Ir.Label loop_label;
                body_ir;
                Ir.Jump (Ir.Name loop_label, [loop_label])
            ]
        | Ast.Expr e -> Ir.unwrap_nx (trans_expr state frame e)

    and trans_statement_list state frame stmts = 
        let stmts_ir = List.map (trans_statement state frame) stmts in
        Ir.seq stmts_ir

    let trans_fun state decl =
        let add_formals state frame decl =
            let args = List.map (fun (name, _) -> Span.data_of name) decl.Ast.fun_args in
            let formals = F.formals frame in
            let combined = List.combine args formals in
            List.iter (fun (ident, value) -> Env.add_value state ident value) combined in 

        let frame = F.create (Span.data_of decl.Ast.fun_name) (List.length decl.Ast.fun_args) in
        (* enter a new scope, add the accesses for our formal parameters
           into our environment *)
        Env.enter_scope state;
        add_formals state frame decl;
        let return_label = Temp.new_label () in
        let return_reg = Temp.new_reg () in
        Env.set_return_label state return_label;
        Env.set_return_reg state return_reg;
        let proc_ir = trans_statement_list state frame decl.Ast.fun_body in
        Env.exit_scope state;

        let fun_ir = 
            if decl.Ast.fun_retty = None 
            then
                (* void return type means we can omit the register move
                   to the target's return register *)
                Ir.seq [
                    proc_ir;
                    Ir.Label return_label;
                ]
             else
                Ir.seq [
                    proc_ir;
                    Ir.Label return_label;
                    Ir.Move (Ir.Temp F.return_value, Ir.Temp return_reg)
                ]
        in
        let proc_fragment = F.Proc (fun_ir, frame) in
        Env.add_fragment state proc_fragment;;

    (* given an item, produce some number of fragments from it. *)
    let trans_item state item =
        match (Span.data_of item) with
        | Ast.FunDecl decl -> trans_fun state decl
        | _ -> ()

    let pass_2_ir_trans state cu =
        List.iter (trans_item state) cu

    let run state cu = 
        let env = Env.create state in
        (* calculate all type layouts before generating IR *)
        pass_1_type_layouts env cu;
        pass_2_ir_trans env cu;
        Env.fragments env
end