open Trans

module MipsFrame : Trans.Frame = struct
    (* A note about this abstraction -
       Currently, the Spork compiler has no need to allocate
       things on the stack. This is because it does not yet have
       the feature of nested functions, which the Tiger compiler
       does. If we choose to add nested functions, this abstraction
       will come in handy. *)
    type access = 
        | InFrame of int
        | InReg of Temp.reg

    type t = {
        name: string;
        formals: access list ref;
    }

    type fragment = 
        | Proc of Ir.stmt * t
        | String of Temp.label * string

    let frame_pointer = Temp.new_reg ()
    let return_value = Temp.new_reg ()
    let word_size = 4

    let name frame = frame.name

    let alloc_local frame = 
        InReg (Temp.new_reg ())

    let create name num_formals = 
        let rec loop frame i =
            match i with
            | 0 -> []
            | i -> alloc_local frame :: loop frame (i - 1) 
        in

        let frame = {
            name = name;
            formals = ref []
        } in

        frame.formals := loop frame num_formals;
        frame

    let formals frame = !(frame.formals)
    let expr_of_access access = 
        match access with
        | InFrame _ -> Util.nyi "in-frame locals"
        | InReg r -> Ir.Temp r
end

module MipsTranslate = Lowering.Translate(MipsFrame)