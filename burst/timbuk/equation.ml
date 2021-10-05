module type S = Pair.S

module Make (Ord : Symbol.ORDERED_FORMAT_TYPE) = struct
  type elt = Ord.t

  type t = elt * elt

  let symmetry (l, r) = (r, l)

  let compare (la, ra) (lb, rb) =
    let c = Ord.compare la lb in
    if c = 0 then Ord.compare ra rb else c

  let equal (la, ra) (lb, rb) =
    Ord.equal la lb && Ord.equal ra rb

  let hash t = Hashtbl.hash t

  let lhs (l, _) = l

  let rhs (_, r) = r

  let print (l, r) out =
    Format.fprintf out "%t = %t" (Ord.print l) (Ord.print r)
end
