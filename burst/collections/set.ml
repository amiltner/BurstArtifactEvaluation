module type OrderedType = Stdlib.Set.OrderedType

module type S = sig
  include Stdlib.Set.S

  val fold_pairs: ?reflexive:bool -> (elt -> elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_pairs2: ?reflexive:bool -> (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val fold_words : int -> (elt list -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_inline_combinations : (elt list -> 'a -> 'a) -> t list -> 'a -> 'a
  val fold_random: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val update : (elt option -> unit) -> elt -> t -> t
  val search : (elt -> bool) -> t -> elt
  val search_opt : (elt -> bool) -> t -> elt option
  val fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val iter2 : (elt -> elt -> unit) -> t -> t -> unit
  val product : (elt -> elt -> elt option) -> t -> t -> t
  val hash : t -> int
  val print : (elt -> Format.formatter -> unit) -> string -> t -> Format.formatter -> unit
end

module Make (E : OrderedType) = struct
  include Stdlib.Set.Make (E)

  let fold_pairs (type accu) ?(reflexive=false) f s accu =
    let exception Continue of accu in
    fold (
      fun e accu ->
        try
          fold (
            fun e' accu ->
              if E.compare e e' = 0
              then raise (Continue (if reflexive then f e e' accu else accu))
              else f e e' accu
          ) s accu
        with
        | Continue accu -> accu
    ) s accu

  let fold_pairs2 (type accu) ?(reflexive=false) f s s' accu =
    let exception Continue of accu in
    fold (
      fun e accu ->
        try
          fold (
            fun e' accu ->
              if E.compare e e' = 0
              then raise (Continue (if reflexive then f e e' accu else accu))
              else f e e' accu
          ) s' accu
        with
        | Continue accu -> accu
    ) s accu

  let rec fold_words n f t x =
    match n with
    | 0 -> f [] x
    | _ ->
      let for_each_element e x =
        let for_each_word w x =
          f (e::w) x
        in
        fold_words (n-1) for_each_word t x
      in
      fold for_each_element t x

  let fold_inline_combinations f l x =
    let rec do_fold combination l x =
      match l with
      | [] -> f (List.rev combination) x
      | t::l ->
        fold (
          fun e x ->
            do_fold (e::combination) l x
        ) t x
    in
    do_fold [] l x

  let update f x t =
    begin match find_opt x t with
      | Some v -> f (Some v); t
      | None -> f None; add x t
    end

  (* let rec update f x = function
     | Empty ->
      f (None);
      Node{l=Empty; v=x; r=Empty; h=1}
     | Node{l; v; r; _} as t ->
      let c = E.compare x v in
      if c = 0 then begin
        f (Some v);
        t
      end else
      if c < 0 then
        let ll = update f x l in
        if l == ll then t else bal ll v r
      else
        let rr = update f x r in
        if r == rr then t else bal l v rr *)

  let search f t =
    let exception Found of elt in
    try iter (function e -> if f e then raise (Found e)) t; raise Not_found with
    | Found e -> e

  let search_opt f t =
    let exception Found of elt in
    try iter (function e -> if f e then raise (Found e)) t; None with
    | Found e -> Some e

  let fold_random f t x =
    let shuffle (d:E.t list) =
      let compare (b1, e1) (b2, e2) =
        let c = b1 - b2 in
        if c = 0 then E.compare e1 e2 else c
      in
      let nd = List.map (fun c -> (Random.bits (), c)) d in
      let sond = List.sort compare nd in
      List.map snd sond
    in
    List.fold_right f (shuffle (elements t)) x

  let fold2 f a b x =
    let fold2' ea x = fold (f ea) b x in
    fold (fold2') a x

  let iter2 f a b =
    let g a b () = f a b in
    fold2 g a b ()

  let product p a b =
    let eprod x y set =
      match (p x y) with
      | Some z -> add z set
      | None -> set
    in
    fold2 (eprod) a b empty

  let hash t = Hashtbl.hash t

  let print f sep t out =
    ignore (
      fold (
        fun x print_sep ->
          if print_sep then
            Format.fprintf out "%s" sep;
          f x out;
          true
      ) t false
    )
end

module Ext (A : S) (B : S) = struct
  let fold2 f a b x =
    let fold2' ea x = B.fold (f ea) b x in
    A.fold (fold2') a x

  let iter2 f a b =
    let g a b () = f a b in
    fold2 g a b ()

  let map f a =
    A.fold (fun x set -> B.add (f x) set) a (B.empty)
end

module Product (A : S) (B : S) (AB : S) = struct
  module Ext = Ext (A) (B)

  let product p a b =
    let eprod x y set =
      match (p x y) with
      | Some z -> AB.add z set
      | None -> set
    in
    Ext.fold2 (eprod) a b AB.empty
end
