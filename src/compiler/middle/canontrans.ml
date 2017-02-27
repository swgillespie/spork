open Trans

(* The Canon module is responsible for turning our tree-like intermediate
   language into a sequence of statements more akin to machine code. It
   makes several stops along the way:
     1. The `linearize` function is responsible for transforming an IR tree
        into a "canonical tree" with the following restrictions: there are no
        SEQ nodes, there are no ESEQ nodes, and the parent of every CALL node
        is either an EXP node or a MOVE(TEMP, ...) node.
     2. The `create_basic_blocks` function is responsible for turning a list
        of statements into "basic blocks", groups of statements that always
        execute together.
     3. The `trace_schedule` function is responsible for "scheduling" basic
        blocks by ordering the list of basic blocks such that every CJUMP is
        followed by its "false" label.
*) 
module Canon : sig
    val linearize : Ir.stmt -> Ir.stmt list

    val create_basic_blocks : Ir.stmt list -> BasicBlock.t list

    val trace_schedule : BasicBlock.t list -> BasicBlock.t list

    val flatten : BasicBlock.t list -> Ir.stmt list
end = struct
    (* this is EXTREMELY conservative and doesn't attempt to determine
       whether or not expressions have side-effects. *)
    let commute s e = 
        match s, e with
        | Ir.Exp (Ir.ConstInt _), _ -> true
        | _, Ir.Name _ -> true
        | _, Ir.ConstInt _ -> true
        | _, _ -> false

    (* Sequences two statement so that the result is a statement that
       does the first statement and then the second, i.e. a seq. 
       Nops are discarded. *)
    let combine s1 s2 =
        match s1, s2 with
        | Ir.Exp (Ir.ConstInt _), s
        | s, Ir.Exp (Ir.ConstInt _) -> s
        | s1, s2 -> Ir.Seq (s1, s2)

    let nop = Ir.Exp (Ir.ConstInt 0)

    let rec reorder exprs =
        match exprs with
        | Ir.Call (_, _) as call :: rest ->
          let temp = Temp.new_reg () in
          let rewrite = Ir.ESeq (Ir.Move (Ir.Temp temp, call), Ir.Temp temp) in
          reorder (rewrite :: rest)
        | expr :: rest ->
          let (stmts, e) = do_expr expr in
          let (stmts', er) = reorder rest in
          (* if we can get away with it, we'd like to swap the execution
             order of e and stmts'. In this way we can avoid allocating
             a temp register and doing a move. We can only actually do this if we can be sure
             that no side-effecting operations get swapped. Our estimate of
             whether or not this is true is extremely conservative and generally
             will only do this if the expression is a known constant, or the statement
             is a no-op. *)
          if commute stmts' e
          then ((combine stmts stmts'), e :: er) 
          else 
            let reg = Temp.new_reg () in
            let combined = combine stmts (combine (Ir.Move (Ir.Temp reg, e)) stmts') in
            (combined, Ir.Temp reg :: er)
        | [] -> (nop, [])
    
    and reorder_stmt exprs f = 
        let (stmts, expr) = reorder exprs in
        combine stmts (f expr)

    and reorder_expr exprs f = 
        let (stmts, expr) = reorder exprs in
        (stmts, f expr)

    and do_stmt stmt =
        match stmt with
        (* 
           The Move cases are handled specifically here because 
           the destination expression is special:
             1. it is one of two nodes (the other being Exp) that allows for Call
                nodes to be subtrees
             2. The destination expression must be either Temp or Mem. If it is an ESeq,
                it must be eliminated by transforming into a Seq and a Move. 
        *)
        | Ir.Move (Ir.Temp i, Ir.Call (base, args)) -> reorder_stmt (base :: args) (fun l -> Ir.Move (Ir.Temp i, Ir.Call (List.hd l, List.tl l)))
        | Ir.Move (Ir.Temp i, e) -> reorder_stmt [e] (fun l -> Ir.Move (Ir.Temp i, List.hd l))
        | Ir.Move (Ir.Mem e, t) -> reorder_stmt [e; t] (fun l -> Ir.Move (Ir.Mem (List.hd l), List.nth l 1))
        | Ir.Move (Ir.ESeq (s, e1), e2) -> do_stmt (Ir.Seq (s, Ir.Move (e1, e2)))
        | Ir.Exp (Ir.Call (base, args)) -> reorder_stmt (base :: args) (fun l -> Ir.Exp (Ir.Call (List.hd l, List.tl l)))
        | Ir.Exp e -> reorder_stmt [e] (fun l -> Ir.Exp (List.hd l))
        | Ir.Jump (e, targets) -> reorder_stmt [e] (fun l -> Ir.Jump (List.hd l, targets))
        | Ir.CJump (p, a, b, t, f) -> reorder_stmt [a; b] (fun l -> Ir.CJump (p, List.hd l, List.nth l 1, t, f))
        | Ir.Seq (s1, s2) -> combine (do_stmt s1) (do_stmt s2)
        | s -> reorder_stmt [] (fun _ -> s)

    and do_expr expr =
        match expr with
        | Ir.Binop (op, e1, e2) -> reorder_expr [e1; e2] (fun l -> Ir.Binop (op, List.hd l, List.nth l 1))
        | Ir.Mem e -> reorder_expr [e] (fun l -> Ir.Mem (List.hd l))
        | Ir.ESeq (s, e) -> 
          let stmts = do_stmt s in
          let (stmts', e') = do_expr e in
          ((combine stmts stmts'), e')
        | Ir.Call (base, args) -> reorder_expr (base :: args) (fun l -> Ir.Call (List.hd l, List.tl l))
        | e -> reorder_expr [] (fun _ -> e)

    let linearize s = 
        let rec linear_helper s c =
            match s with
            | Ir.Seq (a, b) -> linear_helper a (linear_helper b c)
            | _ -> s :: c in
        linear_helper (do_stmt s) []

    let create_basic_blocks l = 
        let exit_block = Temp.new_named_label "exit" in
        let rec do_block stmts block_list =
            let end_block stmts block =
                do_block stmts ((BasicBlock.construct (List.rev block)) :: block_list) in

            let rec next_stmt stmts block =
                match stmts with
                | ((Ir.Jump _ as stmt) :: rest)
                | ((Ir.CJump (_, _, _, _, _) as stmt) :: rest) -> end_block rest (stmt :: block)
                | ((Ir.Label label) :: _ as stmts) ->
                  next_stmt ((Ir.Jump ((Ir.Name label), [label])) :: stmts) block
                | stmt :: rest -> next_stmt rest (stmt :: block)
                | [] -> next_stmt ([Ir.Jump ((Ir.Name exit_block), [exit_block])]) block in

            match stmts with
            | (Ir.Label _ as label) :: tail -> next_stmt tail [label]
            | _ :: _ -> do_block ((Ir.Label (Temp.new_label ())) :: stmts) block_list
            | [] -> List.rev block_list in
        do_block l []

    module BlockSet = Set.Make(struct
        let compare = compare
        type t = Temp.label
    end)

    let trace_schedule blocks = 
        let rec block_with_label blocks label =
            match blocks with
            | b :: rest ->
              let block_label = BasicBlock.label b in
              if label = block_label 
              then b
              else block_with_label rest label
            | [] -> Util.raise_bug "block_with_label failed to find a block" in

        let rec visit_block b visited trace =
            (* visit this block by appending it to the trace
               we are building *)
            let new_trace = b :: trace in
            let new_visited = BlockSet.add (BasicBlock.label b) visited in
            match BasicBlock.terminator b with
            | Ir.Jump (_, targets) -> 
              (* the jump IR statement is flexible enough to express jump
                 tables, but for now unconditional jumps only have one target *)
              let target = List.hd targets in
              if not (BlockSet.mem target new_visited) 
              then visit_block (block_with_label blocks target) new_visited new_trace
              else (new_trace, new_visited)
            | Ir.CJump (_, _, _, t, f) ->
              (* One of our objectives in trace generation is to ensure that all
                 blocks terminated by conditional jumps are immediately followed
                 by their false branches. *)
              let (false_trace, false_visited) = 
                  if (BlockSet.mem f new_visited) 
                  then ([], new_visited)
                  else visit_block (block_with_label blocks f) new_visited new_trace in
              let (true_trace, true_visited) =
                  if (BlockSet.mem t false_visited)
                  then (false_trace, false_visited)
                  else visit_block (block_with_label blocks t) false_visited false_trace in
              (true_trace, true_visited)
            | _ -> Util.raise_bug "unknown block terminator" in

        let (trace, _) = visit_block (List.hd blocks) (BlockSet.singleton (Temp.new_named_label "exit")) [] in
        List.rev trace

    let rec flatten bb =
        match bb with
        | x :: xs -> (BasicBlock.statements x) @ flatten xs
        | [] -> []
end