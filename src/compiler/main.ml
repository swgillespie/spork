let print_fragments fragments =
    let print_fragment fragment =
        match fragment with
        | Mipsframe.MipsFrame.String (label, value) ->
            print_endline ((Trans.Temp.string_of_label label) ^ ":");
            print_endline ("  str \"" ^ value ^ "\"");
            print_newline ();
        | Mipsframe.MipsFrame.Proc (body, frame) ->
            let name = Mipsframe.MipsFrame.name frame in
            print_endline (name ^ ":");
            print_endline (Trans.Ir.string_of_stmt body);
            print_newline ();
    in
    List.iter print_fragment fragments;;

let linearize_fragments fragments =
    let linearize_fragment fragment =
        match fragment with
        | Mipsframe.MipsFrame.String (label, value) ->
            print_endline ((Trans.Temp.string_of_label label) ^ ":");
            print_endline ("  str \"" ^ value ^ "\"");
            print_newline ();
        | Mipsframe.MipsFrame.Proc (body, frame) ->
            let name = Mipsframe.MipsFrame.name frame in
            let linear = Canontrans.Canon.linearize body in
            let linear = List.map Instcombine.InstCombine.run linear in
            let blocks = Canontrans.Canon.create_basic_blocks linear in
            let trace = Canontrans.Canon.trace_schedule blocks in
            let stmt_list = Canontrans.Canon.flatten trace in
            print_endline (name ^ ":");
            List.iter (fun b -> print_endline (Trans.Ir.string_of_stmt b)) stmt_list;
            print_newline ();
    in
    List.iter linearize_fragment fragments;;

let parse_and_typecheck filename channel =
    let lexbuf = Lexing.from_channel channel in
    lexbuf.Lexing.lex_curr_p <- { 
        Lexing.pos_fname = filename;
        Lexing.pos_lnum = 1;
        Lexing.pos_cnum = 0;
        Lexing.pos_bol = 0;
    };
    let ast = Parser.compilation_unit Lexer.token lexbuf in
    let state = Sema.State.empty () in
    let fragments = Typecanon.run state ast
        |> Finitetypecheck.run state
        |> Typecheck.run state 
        |> Mipsframe.MipsTranslate.run state in
    print_endline "pre-canon:";
    print_fragments fragments;
    print_endline "post-canon:";
    linearize_fragments fragments;;

let print_error span msg =
    let (start, stop) = span in
    let filename = start.Lexing.pos_fname in
    let (start_line, start_col) = start.Lexing.pos_lnum, (start.Lexing.pos_cnum - start.Lexing.pos_bol + 1) in
    let (stop_line, stop_col) = stop.Lexing.pos_lnum, (stop.Lexing.pos_cnum - stop.Lexing.pos_bol + 1) in
    Printf.printf "file `%s` (%d, %d):(%d, %d) - %s\n" filename start_line start_col stop_line stop_col msg

let main () =
    Printexc.record_backtrace true;
    if Array.length Sys.argv <> 2 then begin
        print_string "error: no input file\n";
        exit 1;
    end;

    let chan = 
        try open_in Sys.argv.(1) with
        | Sys_error msg -> 
            print_string ("error: " ^ msg ^ "\n");
            exit 1;
    in
    try parse_and_typecheck Sys.argv.(1) chan with 
        | Ast.Parse_error (span, msg) -> print_error span msg
        | Sema.Error (span, msg) -> print_error span msg
        | Util.Internal_compiler_error msg ->
            Printf.printf "internal compiler error: %s\n" msg;
            Printexc.print_backtrace stdout;
        | _ -> 
            print_endline "internal compiler error: unexpected fatal exception";
            Printexc.print_backtrace stdout;;

            


main ()