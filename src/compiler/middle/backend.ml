open Trans

module Assembly = struct
    type instr =
        | Move of string * Temp.reg * Temp.reg
        | Label of string * Temp.label
        | Op of string * Temp.reg list * Temp.reg list * Temp.label list option

    let format f instr =
        match instr with
        | Move (s, r1, r2) -> s ^ " " ^ (f r1) ^ " " ^ (f r2)
        | Label (s, _) -> s ^ ":"
        | Op (s, r1, r2, _) -> 
          let defs = List.map f r1 in
          let src = List.map f r2 in
          s ^ "[dsts: " ^ (String.concat "," defs) ^ "]"
            ^ "[src " ^ (String.concat "," src) ^ "]" 
end