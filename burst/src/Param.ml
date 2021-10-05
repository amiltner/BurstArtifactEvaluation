open MyStdLib

type t =
  Id.t * Type.t
[@@deriving eq, hash, ord]

let pp f (i,t) = Format.fprintf f "(%a:%a)" Id.pp i Type.pp t

let show = show_of_pp
