(* Module Pair *)
module type S = sig
  type elt

  type t = elt * elt

  val symmetry : t -> t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int

  val lhs : t -> elt

  val rhs : t -> elt

  val print : t -> Format.formatter -> unit
end

(* module Make (T : Term.S) = struct
  module Term = T
  module Pattern = Pattern.S (Var)

  type t = Pattern.t * Pattern.t

  let symmetry (l, r) = (r, l)

  let compare (la, ra) (lb, rb) =
    let c = Pattern.compare la lb in
    if c = 0 then Pattern.compare ra rb else c

  let equal (la, ra) (lb, rb) =
    Pattern.equal la lb && Pattern.equal ra rb

  let lhs (l, _) = l

  let rhs (_, r) = r

  let hash t = Hashtbl.hash t
end *)
