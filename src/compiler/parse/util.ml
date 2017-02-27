exception Internal_compiler_error of string

let uncurry f (x, y) = f x y
let curry f x y = f (x, y)

let opt_map f = function
    | Some x -> Some (f x)
    | None -> None

let opt_iter f = function
    | Some x -> f x
    | None -> ()

(* Raises an internal compiler error *)
let raise_bug msg =
    raise (Internal_compiler_error msg)

(* Raises an internal compiler error on a spanned element *)
let raise_bug_spanned spanned msg =
    raise (Internal_compiler_error msg)

let nyi msg = raise_bug ("not yet implemented: " ^ msg)