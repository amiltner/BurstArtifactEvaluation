module type OrderedType = Stdlib.Map.OrderedType

module type S =
sig
  include Stdlib.Map.S

  val map_bindings : (key -> 'a -> key * 'b) -> ('b -> 'b -> 'b option) -> 'a t -> 'b t
  val fold_pairs: ?reflexive:bool -> (key -> 'a -> key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold2 : (key -> 'a -> key -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
  val product : (key -> 'a -> key -> 'b -> (key * 'c) option) -> 'a t -> 'b t -> 'c t
  val hash : 'a t -> int
  val fold_combinations : ('b t -> 'c -> 'c) -> 'a t -> (('b -> 'c -> 'c) -> 'a -> 'c -> 'c) -> 'c -> 'c
end

module Make (K: OrderedType) = struct
  include Stdlib.Map.Make (K)

  let fold_pairs (type accu) ?(reflexive=false) f m (accu : accu) =
    let exception Continue of accu in
    fold (
      fun key v accu ->
        try fold (
            fun key' v' accu ->
              if K.compare key key' = 0
              then raise (Continue (if reflexive then f key v key' v' accu else accu))
              else f key v key' v' accu
          ) m accu
        with
        | Continue accu -> accu
    ) m accu

  let map_bindings f union a =
    let do_update x = function
      | Some y -> union y x
      | None -> Some x
    in
    let map_binding key x map =
      let key, x = f key x in
      update key (do_update x) map
    in
    fold map_binding a empty

  let fold2 f a b x =
    let fold2' ka va x = fold (f ka va) b x in
    fold fold2' a x

  let product p a b =
    let bprod ka va kb vb map =
      match p ka va kb vb with
      | Some (k, v) -> add k v map
      | None -> map
    in
    fold2 bprod a b empty

  let hash t = Hashtbl.hash t

  let fold_combinations f t g accu =
    let rec fold l map accu =
      begin match l with
        | [] -> f map accu
        | (key, value)::l' ->
          g (
            fun value' accu ->
              fold l' (add key value' map) accu
          ) value accu
      end
    in
    fold (bindings t) empty accu
end

module Ext (A : S) (B : S) = struct
  let map f union a =
    let do_update x = function
      | Some y -> union y x
      | None -> Some x
    in
    let map_binding key x map =
      let key, x = f key x in
      B.update key (do_update x) map
    in
    A.fold map_binding a B.empty

  let fold2 f a b x =
    let fold2' ka va x = B.fold (f ka va) b x in
    A.fold fold2' a x
end

module Product (A : S) (B : S) (AB : S) = struct
  module Ext = Ext (A) (B)

  let product p a b =
    let bprod ka va kb vb map =
      match p ka va kb vb with
      | Some (k, v) -> AB.add k v map
      | None -> map
    in
    Ext.fold2 bprod a b AB.empty
end
