(* 
   The objective of the "type canonicalization pass" is to resolve
   all type aliases. Type aliases are problematic and uninteresting
   for the rest of the compiler, so eliminating them is the first thing
   that we do, before even inspecting the types themselves.

   There are several invariants that are enforced here:
     1) A type alias is declared to a non-declared type. This is simple,
        we don't allow aliases to refer to types that don't exist.
     2) A type alias cannot be cyclic. This one is more tricky to
        enforce, as it forces us (the compiler) to remember the
        alias substitutions that we have done.
     3) Two types cannot have the same name.

   At the end of the pass, the AST will remain structurally the same,
   but all "type alias" top-level items will be removed and all types
   throughout the tree /may/ have been transformed to the "AliasedTy"
   variant, which is functionally identical to the other types but
   indicates that this type has been aliased from another type (i.e. for
   better error type error messages down the road.)
*)
val run : Sema.State.t -> Ast.compilation_unit -> Ast.compilation_unit