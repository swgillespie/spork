open Ast

let rec ty_has_name name ty =
    match (Span.data_of ty) with
    | AliasedTy (_, t) -> ty_has_name name t
    | NamedTy i -> (Span.data_of i) = name
    | _ -> false

let check_struct decl = 
    let check_single_field name (id, ty) =
        if ty_has_name (Span.data_of name) ty
        then Sema.raise_error name "type has infinite size"
        else ()
    in
    List.iter (check_single_field decl.struct_name) decl.struct_fields

let check_items items = 
    let check_single_item item =
        match (Span.data_of item) with
        | StructDecl decl -> check_struct decl
        | _ -> ()
    in
    List.iter check_single_item items

let run _ cu = 
    check_items cu;
    cu
