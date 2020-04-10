{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read = 
  parse
  | white { read lexbuf }
  | "true" { TRUE }
  | "false" { FALSE }
  | "Left" { LEFT }
  | "Right" { RIGHT }
  | "<>" { NEQ }
  | "<=" { LEQ }
  | "<" { LT }
  | ">=" { GEQ }
  | ">" { GT }
  | "/" { DIVIDE }
  | "*" { TIMES }
  | "-" { MINUS }
  | "+" { PLUS }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LPAREN }
  | "]" { RPAREN }
  | "{" { LPAREN }
  | "}" { RPAREN }
  | "let" { LET }
  | "=" { EQUALS }
  | "in" { IN }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "match" { MATCH }
  | "with" { WITH }
  | id { ID (Lexing.lexeme lexbuf) }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }