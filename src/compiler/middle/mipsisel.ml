open Trans
open Backend

module InstructionSelector = struct
    let run stmts =
        let instrs = ref [] in

        let emit instr =
            instrs := instr :: !instrs in

        let emit_move s_instr dst src =
            emit (Assembly.Move (s_instr, dst, src)) in

        let emit_op s_instr dsts srcs targets =
            emit (Assembly.Op (s_instr, dsts, srcs, targets)) in


        let rec munch_exp expr = Util.nyi "asdf" in

        let rec munch_stmt stmt = 
            match stmt with
            | Ir.Seq (s1, s2) -> 
              munch_stmt s1;
              munch_stmt s2;
            | Ir.Move (Ir.Mem (Ir.Binop (Ir.Plus, Ir.ConstInt i, e1)), e2)
            | Ir.Move (Ir.Mem (Ir.Binop (Ir.Plus, e1, Ir.ConstInt i)), e2) ->
              (* M[e1 + C] <- e2 gets transformed into a sw + offset *)
              let dest = munch_exp e2 in
              let ptr_base = munch_exp e1 in
              emit_move ("sw `d0, " ^ (string_of_int i) ^ "(`s0)") ptr_base dest;
            | Ir.Move (Ir.Mem e1, e2) ->
              let src = munch_exp e2 in
              let dst_ptr = munch_exp e1 in
              emit_move "sw `s0, `d0" dst_ptr src;
            | Ir.Move (Ir.Temp i, Ir.Temp j) ->
              emit_move "move `d0, `s0" i j;
            | Ir.Move (Ir.Temp i, e2) ->
              let src = munch_exp e2 in
              emit_move "move `d0, `s0" i src;
            | Ir.Exp (Ir.Call _) -> Util.nyi "calls"
            | Ir.Jump ((Ir.Name target), targets) ->
              emit_op ("j " ^ (Temp.string_of_label target)) [] [] (Some targets);
        in
        List.iter munch_stmt stmts;
        List.rev !instrs
end