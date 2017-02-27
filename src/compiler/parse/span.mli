type span = Lexing.position * Lexing.position
type 'a spanned

val data_of : 'a spanned -> 'a
val span_of : 'a spanned -> span
val spanned_of : 'a -> span -> 'a spanned
val dummy : span