type token =
  | THESIS
  | COMMA
  | LITT of (string)
  | LPAREN
  | RPAREN
  | EOL
  | ORTH
  | TENSOR
  | PAR
  | WITH
  | PLUS
  | ONE
  | BOTTOM
  | TOP
  | ZERO
  | LOLLIPOP
  | OFCOURSE
  | WHYNOT

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Linear_logic.formula list * Linear_logic.formula list