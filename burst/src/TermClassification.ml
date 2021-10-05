open MyStdLib

type t =
  | Introduction
  | Elimination
[@@deriving eq, hash, ord, show, sexp]
