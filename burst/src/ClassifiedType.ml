open MyStdLib

type t = Type.t * TermClassification.t
[@@deriving eq, hash, ord, show, sexp]
