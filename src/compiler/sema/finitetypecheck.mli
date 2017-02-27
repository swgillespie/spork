(*
    The objective of this pass is to ensure that all of our types 
    have a finite size. Infinitely-sized types can occur when a struct
    is embedded as a field within itself.
*)
val run : Sema.State.t -> Ast.compilation_unit -> Ast.compilation_unit