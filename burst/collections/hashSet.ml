module type S = sig
  type elt
  type t
  val create : int -> t
  val empty : unit -> t
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val size : t -> int
  val is_empty : t -> bool
  val contains : elt -> t -> bool
  val fold : (elt -> 'b -> 'b) -> t -> 'b -> 'b
  val fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val as_list : t -> elt list
  val iter : (elt -> unit) -> t -> unit
  val union : t -> t -> t
  val pp : (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
  val update : (elt option -> unit) -> elt -> t -> t
end

module Make (K: HashTable.HashedType) = struct
  module D = HashTable.Make(K)
  type elt = K.t
  type t = bool D.t

  let create = D.create

  let empty _ = create 2

  let add k s = D.set k true s

  let size = D.size

  let is_empty = D.is_empty

  let contains k s =
    begin match D.find_opt k s with
      | None -> false
      | Some b -> b
    end

  let remove e s =
    if contains e s then
      D.set e false s
    else
      s

  let fold f s init =
    D.fold
      (fun k b acc ->
         if b then
           f k acc
         else
           acc)
      s
      init

  let fold2 f a b x =
    let fold2' ea x = fold (f ea) b x in
    fold (fold2') a x

  let exists f s =
    fold
      (fun x acc ->
         acc || f x)
      s
      false

  let as_list s =
    fold
      (fun h acc -> h::acc)
      s
      []

  let iter f s =
    D.iter
      (fun k b ->
         if b then
           f k
         else
           ())
      s

  let union s1 s2 =
    D.union
      (fun k b1 b2 ->
         if b1 || b2 then
           Some true
         else
           None)
      s1
      s2

  let pp k_pp f s =
    Format.fprintf
      f
      "[";
    iter
      (fun k -> k_pp f k)
      s;
    Format.fprintf
      f
      "]"

    let update
        (f:elt option -> unit)
        (e:elt)
        (s:t)
      : t =
      if contains e s then
        (f (Some e); s)
      else
        (f None; add e s)
end
