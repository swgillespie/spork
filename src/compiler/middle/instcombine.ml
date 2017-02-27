open Trans

(* InstCombine contains some very basic constant folding optimizations
   that we use to prevent our generated code from looking really silly. *)
module InstCombine : sig 
    val run : Ir.stmt -> Ir.stmt
end = struct
    let rec run_expr e =
        match e with
        | Ir.Binop (op, lhs, rhs) ->
            let eval_lhs = run_expr lhs in
            let eval_rhs = run_expr rhs in
            (match op, eval_lhs, eval_rhs with
            | Ir.Plus, Ir.ConstInt l, Ir.ConstInt r -> Ir.ConstInt (l + r)
            | Ir.Plus, e, Ir.ConstInt 0 
            | Ir.Plus, Ir.ConstInt 0, e -> e
            | Ir.Minus, Ir.ConstInt l, Ir.ConstInt r -> Ir.ConstInt (l - r)
            | Ir.Minus, e, Ir.ConstInt 0 -> e
            | Ir.Mul, Ir.ConstInt l, Ir.ConstInt r -> Ir.ConstInt (l * r)
            | Ir.Mul, Ir.ConstInt 1, e
            | Ir.Mul, e, Ir.ConstInt 1 -> e
            (* This optimization is valid because it's run only on canonical trees, 
               where call nodes must be children of a Move or Exp statement node. *)
            | Ir.Mul, Ir.ConstInt 0, _
            | Ir.Mul, _, Ir.ConstInt 0 -> Ir.ConstInt 0
            (* Dividing by zero will trap at runtime, so leave it be *)
            | Ir.Div, Ir.ConstInt l, Ir.ConstInt r when r <> 0 -> Ir.ConstInt (l / r)
            | _ -> Ir.Binop (op, eval_lhs, eval_rhs))
        | Ir.Mem e -> Ir.Mem (run_expr e)
        | Ir.Call (base, args) -> Ir.Call (run_expr base, List.map run_expr args)
        | Ir.ESeq (s, e) -> Util.raise_bug "ESeq not eliminated by canonicalization"
        | _ -> e

    and run_stmt stmt =
        match stmt with
        | Ir.Move (e, t) -> Ir.Move (run_expr e, run_expr t)
        | Ir.Exp e -> Ir.Exp (run_expr e)
        | Ir.Jump (e, targets) -> Ir.Jump (run_expr e, targets)
        | Ir.CJump (op, lhs, rhs, t, f) ->
            let eval_lhs = run_expr lhs in
            let eval_rhs = run_expr rhs in
            (match op, eval_lhs, eval_rhs with
            (* Trivially true branches *)
            | Ir.Eq, Ir.ConstInt i, Ir.ConstInt j when i = j     -> Ir.Jump (Ir.Name t, [t])
            | Ir.NotEq, Ir.ConstInt i, Ir.ConstInt j when i <> j -> Ir.Jump (Ir.Name t, [t])
            | Ir.Gt, Ir.ConstInt i, Ir.ConstInt j when i > j     -> Ir.Jump (Ir.Name t, [t])
            | Ir.GtEq, Ir.ConstInt i, Ir.ConstInt j when i >= j  -> Ir.Jump (Ir.Name t, [t])
            | Ir.Lt, Ir.ConstInt i, Ir.ConstInt j when i < j     -> Ir.Jump (Ir.Name t, [t])
            | Ir.LtEq, Ir.ConstInt i, Ir.ConstInt j when i <= j  -> Ir.Jump (Ir.Name t, [t])
            (* Trivially false branches *)
            | Ir.Eq, Ir.ConstInt i, Ir.ConstInt j     -> Ir.Jump (Ir.Name f, [f])
            | Ir.NotEq, Ir.ConstInt i, Ir.ConstInt j  -> Ir.Jump (Ir.Name f, [f])
            | Ir.Gt, Ir.ConstInt i, Ir.ConstInt j     -> Ir.Jump (Ir.Name f, [f])
            | Ir.GtEq, Ir.ConstInt i, Ir.ConstInt j   -> Ir.Jump (Ir.Name f, [f])
            | Ir.Lt, Ir.ConstInt i, Ir.ConstInt j     -> Ir.Jump (Ir.Name f, [f])
            | Ir.LtEq, Ir.ConstInt i, Ir.ConstInt j   -> Ir.Jump (Ir.Name f, [f])
            (* everything else has to stay *)
            | _ -> Ir.CJump (op, eval_lhs, eval_rhs, t, f))
        | Ir.Seq (s1, s2) -> Util.raise_bug "Seq not eliminated by canonicalization"
        | _ -> stmt

    let run = run_stmt
end