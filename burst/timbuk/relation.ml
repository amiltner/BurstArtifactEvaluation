module type S = sig
  type ord
  include Set.S with type elt = ord * ord
  val of_list : elt list -> t
  val left_sides : t -> ord list
  val right_sides : t -> ord list
  val rights_of : ord -> t -> ord list
  val lefts_of : ord -> t -> ord list
  val compare : t -> t -> int
  val print : t -> Format.formatter -> unit
end

module Make (Ord : Symbol.ORDERED_FORMAT_TYPE) (Pair : Pair.S with type elt = Ord.t) = struct
  include Set.Make (Pair)

  type ord = Ord.t

  let of_list l =
    let fold set e = add e set in
    List.fold_left (fold) (empty) l

  let left_sides t =
    let left (l, _) xs = l::xs in
    fold (left) t []

  let right_sides t =
    let right (_, r) xs = r::xs in
    fold (right) t []

  let rights_of left t =
    let right (l, r) xs = if Ord.compare left l = 0 then r::xs else xs in
    fold (right) t []

  let lefts_of right t =
    let left (l, r) xs = if Ord.compare right r = 0 then l::xs else xs in
    fold (left) t []

  let print trs out =
    let print_rule rule =
      Format.fprintf out "%t\n" (Pair.print rule)
    in
    iter (print_rule) trs
end
