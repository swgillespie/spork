{
    open Lexing
    open Parser

    exception Lexer_error
}

let ident = ['a' - 'z' 'A' - 'Z' '_']['a' - 'z' 'A' - 'Z' '_' '0' - '9']*
let integer_lit = ['0' - '9']+
let float_lit = ['0' - '9']+'.'['0' - '9']+
let comment = '/' '/'[^'\n']*'\n'

rule token = parse
    | [' ' '\t'] { token lexbuf }
    | ['\n' '\r'] { Lexing.new_line lexbuf; token lexbuf }
    | comment     { Lexing.new_line lexbuf; token lexbuf }
    | "fun" { FUN }
    | "let" { LET }
    | "if" { IF }
    | "else" { ELSE }
    | "loop" { LOOP }
    | "true" { TRUE }
    | "false" { FALSE }
    | "and" { AND }
    | "or"  { OR }
    | "not" { NOT }
    | "return" { RETURN }
    | "struct" { STRUCT }
    | "as" { AS }
    | "type" { TYPE }
    | "new" { NEW }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '{' { LBRACE }
    | '}' { RBRACE }
    | '[' { LBRACKET }
    | ']' { RBRACKET }
    | ';' { SEMICOLON }
    | ':' { COLON }
    | "->" { ARROW }
    | ',' { COMMA }
    | '.' { DOT }
    | '=' { EQUAL }
    | '^' { CARAT }
    | "==" { DOUBLE_EQUAL }
    | "!=" { NOT_EQUAL }
    | ">=" { GREATER_EQ }
    | ">"  { GREATER }
    | "<=" { LESS_EQ }
    | "<"  { LESS }
    | "+"  { PLUS }
    | "-"  { MINUS }
    | "/"  { DIV }
    | "*"  { STAR }
    | eof  { EOF }
    | "\"" { read_string (Buffer.create 20) lexbuf }
    | ident { IDENT (Lexing.lexeme lexbuf) }
    | integer_lit { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | _    { raise Lexer_error }

and read_string buf = parse
                      | '"'       { STRING (Buffer.contents buf) }
                      | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
                      | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
                      | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
                      | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
                      | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
                      | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
                      | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
                      | [^ '"' '\\']+
                        { Buffer.add_string buf (Lexing.lexeme lexbuf);
                          read_string buf lexbuf
                        }
                      | _ { raise Lexer_error }
                      | eof { raise Lexer_error }
