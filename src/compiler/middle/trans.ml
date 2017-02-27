(* The Temp module encapsulates the creation of temporary labels
   and registers. *)
module Temp : sig
    type label
    type reg

    val new_label : unit -> label
    val new_named_label : string -> label
    val new_reg : unit -> reg
    val string_of_reg : reg -> string
    val string_of_label : label -> string
end = struct
    type label = string
    type reg = int

    let reg_count = ref 0
    let label_count = ref 0

    let next_reg () = 
        let reg = !reg_count in
        reg_count := !reg_count + 1;
        reg

    let next_label () =
        let lbl = !label_count in
        label_count := !label_count + 1;
        "L" ^ (string_of_int lbl)

    let new_label = next_label
    let new_named_label name = name
    let new_reg = next_reg

    let string_of_reg r = "%" ^ string_of_int r
    let string_of_label s = s
end

module Ir = struct
    type binop =
        | Plus
        | Minus
        | Div
        | Mul

    type relop =
        | Eq
        | NotEq
        | Gt
        | GtEq
        | Lt
        | LtEq

    type expr =
        (* Constant expression values *)
        | ConstInt of int
        (* A symbolic constant with the given name, representing
        an assembly language label. *)
        | Name of Temp.label
        (* A temporary value in our intermediate representation *)
        | Temp of Temp.reg
        (* The application of a binary operator to two operands. There
        are no logical operators at this level - no expressions
        will short-cirucit. *)
        | Binop of binop * expr * expr
        (* Pointer dereference - yields a word of memory starting at the
        memory address pointed to by the argument. When on the left hand
        side of a Move statement, this is a store - i.e. this expr can be
        an lvalue. *)
        | Mem of expr
        (* Calls a function with the given arguments. *)
        | Call of expr * expr list
        (* Executes a statement, executes an expression, and then yields the value
        of the expression. *)
        | ESeq of stmt * expr
    and stmt =
        (* Moves the rvalue obtained by evaluating the second expr into
        the lvalue produced by the first expr. *)
        | Move of expr * expr
        (* Executes an expression and discards the result, purely for side
        effects. *)
        | Exp of expr
        (* Evaluates the given expr and jumps to one of the given labels based
        on the value of the expr. If the expr is a Name, this is an unconditional
        jump. *)
        | Jump of expr * Temp.label list
        (* Conditionally jumps to one of two target labels by applying a binary
        comparison operator to the two given expressions *)
        | CJump of relop * expr * expr * Temp.label * Temp.label
        (* Executes one statement, followed by the second statement. *)
        | Seq of stmt * stmt
        (* A label, used as the target of jumps. *)
        | Label of Temp.label

    (* An "IR Tree" is a utility representation of IR that consists of things
    that can be freely converted between three different forms:
        1) Ex, or "expression", the type of expressions (the type of computations
            that produce a value),
        2) Nx, or "no-result", the type of statements (the type of computations that
            do not produce a value),
        3) Cx, or "conditional", expressions with conditional execution that will
            jump to another location. *) 
    type tree = 
        | Ex of expr
        | Nx of stmt
        | Cx of (Temp.label * Temp.label -> stmt)
    (* A utility function that turns a list of statements into a 
    tree of Seq-connected statements *)
    let rec seq = function
        | [] -> Util.raise_bug "empty list passed to seq"
        | x :: [] -> x
        | x :: xs -> Seq (x, seq xs) 

    (* unwrap_ex takes an IR tree and converts it to an expression. *)
    let unwrap_ex = function
        (* unwrapping an expression to an expression does nothing *)
        | Ex e -> e
        | Cx stmt_fn ->
            (* 
                This scenario is for when we are converting the result of a 
                short-circuiting logical expression to an expression, 
                i.e. let some_bool = a < b and c < d. 
                
                The idea is to create a temporary variable, store 1 one it, invoke
                the given function (which will produce a statement that, when truthy,
                will jump to the first label argument and, when falsey, will jump
                to the second label argument), set up our false branch label that
                stores 0 to the temporary variable, set up our true label and return
                the value of the temporary variable (which will be either 1 or 0).
            *)
            let cond = Temp.new_reg () in
            let true_branch = Temp.new_label () in
            let false_branch = Temp.new_label () in
            ESeq(
                seq [
                    Move(Temp cond, ConstInt 1);
                    (* do something - jump to one of these branches depending
                    on the truthiness of whatever this statement does *)
                    stmt_fn (true_branch, false_branch);
                    Label false_branch;
                    Move(Temp cond, ConstInt 0);
                    Label true_branch;
                ],
                Temp cond
            )
        (* Here we define in our IR that taking the value of a statement produces
        the number 0. This generally shouldn't happen (our frontend should raise
        errors) *)
        (* it's EXTREMELY tempting to add an "undef" node in the IR here... *)
        | Nx stmt -> ESeq(stmt, ConstInt 0)

    (* unwrap_nx takes an IR tree and converts it into a statement. *)
    let unwrap_nx = function
        (* unwrapping a statement to a statement does nothing *)
        | Nx stmt -> stmt
        (* unwrapping an expression to a statement produces an Exp *)
        | Ex e -> Exp e
        | Cx stmt_fn as cx ->
            (* this is silly but it can have side effects *) 
            let exp = unwrap_ex cx in
            Exp exp

    (* unwrap_cx takes an IR tree and converts it into a function that,
    when passed a true-label and a false-label, will produce a statement
    that evaluates some conditionals and jumps to one of the two labels. *)
    let unwrap_cx = function
        (* unwrapping a conditional expr to a conditional expr does nothing *)
        | Cx stmt_fn -> stmt_fn
        | Nx _ -> Util.raise_bug "type-checking failed to prevent branching on void"
        (* turn trivially constant conditional branches into unconditional jumps *)
        | Ex (ConstInt 0) -> fun (t, f) -> Jump (Name f, [f])
        | Ex (ConstInt _) -> fun (t, f) -> Jump (Name t, [t])
        (* false is ConstInt 0 and true is not ConstInt 0 *)
        | Ex expr -> fun (t, f) -> CJump (NotEq, expr, ConstInt 0, t, f)

    let rec string_of_expr expr = 
        match expr with
        | ConstInt i -> "(const-int " ^ (string_of_int i) ^ ")"
        | Name label -> Temp.string_of_label label
        | Temp reg -> Temp.string_of_reg reg
        | Binop (op, lhs, rhs) ->
            let lhs_str = string_of_expr lhs in
            let rhs_str = string_of_expr rhs in
            let op_str = 
                match op with
                | Plus -> "plus"
                | Minus -> "minus"
                | Div -> "div"
                | Mul -> "mul" in
            "(" ^ op_str ^ " " ^ lhs_str ^ " " ^ rhs_str ^ ")"
        | Mem e -> "mem[" ^ (string_of_expr e) ^ "]"
        | Call (base, args) ->
            let base_str = string_of_expr base in
            let args_str = String.concat ", " (List.map string_of_expr args) in
            "(call " ^ base_str ^ " [" ^ args_str ^ "])" 
        | ESeq (stmt, e) ->
            let stmt_str = string_of_stmt stmt in
            let e_str = string_of_expr e in
            "(eseq\n" ^ stmt_str ^ "\n" ^ e_str ^ ")" 

    and string_of_stmt stmt =
        match stmt with
        | Move (e1, e2) -> "  " ^ (string_of_expr e1) ^ " <- " ^ (string_of_expr e2)
        | Exp e -> "  ignore " ^ (string_of_expr e)
        | Jump (e, targets) -> 
            let label_strs = String.concat ", " (List.map Temp.string_of_label targets) in
            "  jump " ^ (string_of_expr e) ^ " [" ^ label_strs ^ "]"
        | CJump (op, lhs, rhs, true_b, false_b) ->
            let op_str = 
                match op with
                | Eq -> "eq"
                | NotEq -> "neq"
                | Gt -> "gt"
                | GtEq -> "gteq"
                | Lt -> "lt"
                | LtEq -> "lteq" in
            let lhs_str = string_of_expr lhs in
            let rhs_str = string_of_expr rhs in
            "  cjump " ^ op_str ^ " " ^ lhs_str ^ ", " 
                ^ rhs_str ^ " [true: " ^ (Temp.string_of_label true_b) 
                ^ ", false: " ^ (Temp.string_of_label false_b) ^ "]"
        | Seq (s1, s2) ->
            let s1_str = string_of_stmt s1 in
            let s2_str = string_of_stmt s2 in
            s1_str ^ "\n" ^ s2_str
        | Label l -> (Temp.string_of_label l) ^ ":"
end

(* The Frame module type is the set of information that must be
   provided regarding the target architecture for IR translation. *)
module type Frame = sig
    (* the type of types that implement this module type *)
    type t

    (* the type of "frame accesses", or an abstraction for the
       location of locals allocated within a frame *)
    type access

    (* A fragment is an artifact that needs to be emitted into the
       assembly file at the end of compilation *)
    type fragment = 
        (* A proc is a procedure that will be emitted as machine code. *)
        | Proc of Ir.stmt * t
        (* A string is a string that will be emitted as data in assembly *)
        | String of Temp.label * string

    (* the frame pointer of the target architecture *)
    val frame_pointer : Temp.reg

    (* the return value register of the target architecture *)
    val return_value : Temp.reg

    (* the word size of the target architecture *)
    val word_size : int

    (* The "name" of this frame *)
    val name : t -> string

    (* Creates a new frame with the given name
       and number of formal arguments  *)
    val create : string -> int -> t

    (* Allocates a local in this stack frame *)
    val alloc_local : t -> access

    (* Retrieves the formal parameters associated with this frame *)
    val formals : t -> access list

    (* Turns an access into an expression that yields an lvalue
       for the given local *)
val expr_of_access : access -> Ir.expr
end

module BasicBlock : sig
    type t

    val construct : Ir.stmt list -> t
    val statements : t -> Ir.stmt list
    val string_of_basic_block : t -> string
    val terminator : t -> Ir.stmt
    val label : t -> Temp.label
end = struct
    type t = Ir.stmt list

    let construct t = t
    let statements t = t

    let string_of_basic_block bb =
        (String.concat "\n" (List.map (Ir.string_of_stmt) bb)) ^ "\n"

    let terminator t = List.hd (List.rev t)

    let label t =
        match List.hd t with
        | Ir.Label name -> name
        | _ -> Util.raise_bug "block started with non-label statement"
end