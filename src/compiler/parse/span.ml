type span = Lexing.position * Lexing.position
type 'a spanned = 'a * span

let data_of (data, _) = data
let span_of (_, span) = span
let spanned_of data span = (data, span)
let dummy = (Lexing.dummy_pos, Lexing.dummy_pos)