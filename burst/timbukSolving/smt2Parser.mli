type token =
  | EOF
  | LP
  | RP
  | NAME of (string)
  | SAT
  | UNSAT
  | UNKNOWN
  | MODEL
  | DECLARE_SORT
  | DECLARE_FUN
  | DEFINE_FUN
  | FORALL
  | OR
  | EQ

val model :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Smt2.model
val result :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Smt2.result
