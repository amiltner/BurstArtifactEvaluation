module type HashedType = sig
  include Set.OrderedType

  val equal: t -> t -> bool

  val hash: t -> int
end

module type S = sig
  type key
  type 'a t
  val create : int -> 'a t
  val empty : unit -> 'a t
  val set : key -> 'a -> 'a t -> 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val size : 'a t -> int
  val is_empty : 'a t -> bool
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val resize : int -> 'a t -> 'a t
  val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold2 : (key -> 'a -> key -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : (key -> 'a -> 'b) -> 'a t -> 'b t
  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val pp : (Format.formatter -> key -> unit) ->
    (Format.formatter -> 'a -> unit) ->
    Format.formatter ->
    'a t ->
    unit
end

module Make (K: HashedType) = struct
	type key = K.t

  type 'a bucket =
    | Empty
    | Cons of {
        key: key;
        data: 'a;
        next: 'a bucket
      }

  type 'a hashtable = {
    mutable size: int;
    data: 'a bucket array
  }

  type 'a version =
    | HashTable of 'a hashtable
    | Diff of {
        mutable size: int option;
        key: key;
        data: 'a option;
        source: 'a t
      }

  and 'a t = 'a version ref

  let create bucket_count = ref (HashTable {
      size = 0;
      data = Array.make (max bucket_count 1) Empty
    })

  let empty _ = create 100

  let key_bucket key ht =
    (K.hash key) mod (Array.length ht.data)

  (* insert the value in the bucket and return the nex bucket with the old value. *)
  let rec bucket_replace_value key value = function
    | Empty -> Cons {
        key = key;
        data = value;
        next = Empty
      }, None
    | Cons bucket when K.equal key bucket.key ->
      Cons { bucket with data = value }, Some bucket.data
    | Cons bucket ->
      let next, old_value = bucket_replace_value key value bucket.next in
      Cons { bucket with next = next }, old_value

  (* used in fold *)
  module KHashtbl = Hashtbl.Make (K)

  let fold f x t =
    let rec aux table x t =
      match !t with
      | HashTable ht ->
        let rec fold_bucket x = function
          | Empty -> x
          | Cons bucket ->
            let x = match table with
              | Some table ->
                begin
                  match KHashtbl.find_opt table bucket.key with
                  | Some () -> x
                  | None ->
                    KHashtbl.add table bucket.key ();
                    f x bucket.key bucket.data
                end
              | None -> f x bucket.key bucket.data
            in
            fold_bucket x bucket.next
        in
        Array.fold_left (fold_bucket) x ht.data
      | Diff { key = key; data = None; source = src; _ } ->
        begin
          match table with
          | Some table -> KHashtbl.add table key ();
          | None -> ()
        end;
        aux table x src
      | Diff { key = key; data = Some value; source = src; _ } ->
        let x = match table with
          | Some table ->
            begin
              match KHashtbl.find_opt table key with
              | Some () -> x
              | None ->
                KHashtbl.add table key ();
                f x key value
            end
          | None -> f x key value
        in
        aux table x src
    in
    match !t with
    | HashTable _ -> aux None x t
    | Diff d ->
      let table_size = match d.size with
        | Some size -> size
        | None -> 16
      in
      aux (Some (KHashtbl.create table_size)) x t

  let iter f t = fold (fun () key value -> f key value) () t

  let size t =
    match !t with
    | HashTable ht -> ht.size
    | Diff d ->
      begin
        match d.size with
        | Some size -> size
        | None ->
          let size = ref 0 in
          let count _ _ = size := !size + 1 in
          iter count t;
          d.size <- Some !size;
          !size
      end

  let is_empty t =
    size t = 0

  let rec capacity t =
    match !t with
    | HashTable ht -> ht.size
    | Diff d -> (capacity d.source)

  let resize n t =
    let n = min n Sys.max_array_length in
    if n != size t then begin
      let ht = {
        size = 0;
        data = Array.make n Empty
      } in
      let add key value =
        let i = key_bucket key ht in
        ht.size <- ht.size + 1;
        ht.data.(i) <- Cons { key = key; data = value; next = ht.data.(i) }
      in
      iter add t;
      ref (HashTable ht)
    end else t

  let set key value t =
    match !t with
    | HashTable ht ->
      let i = key_bucket key ht in
      let bucket, old_value = bucket_replace_value key value ht.data.(i) in
      let old_size = ht.size in
      begin
        match old_value with
        | Some _ -> ()
        | None -> ht.size <- ht.size + 1
      end;
      ht.data.(i) <- bucket;
      let new_t = ref (HashTable ht) in
      let new_t = if ht.size > (Array.length ht.data) then resize (ht.size * 2) new_t else new_t in
      t := Diff {size = Some old_size; key = key; data = old_value; source = new_t};
      new_t
    | Diff _ -> ref (Diff {size = None; key = key; data = Some value; source = t})

  let add = set

  let ht_find key ht =
    let i = key_bucket key ht in
    let rec find_in_bucket = function
      | Empty -> raise Not_found
      | Cons { key = k; data = value; next = _ } when K.equal key k -> value
      | Cons { key = _; data = _; next = next } -> find_in_bucket next
    in
    find_in_bucket ht.data.(i)

  let ht_find_opt key ht =
    let i = key_bucket key ht in
    let rec find_in_bucket = function
      | Empty -> None
      | Cons { key = k; data = value; next = _; _ } when K.equal key k -> Some value
      | Cons { key = _; data = _; next = next; _ } -> find_in_bucket next
    in
    find_in_bucket ht.data.(i)

  let rec find key t =
    match !t with
    | HashTable ht ->
      ht_find key ht
    | Diff { key = k; data = None; source = _; _ } when K.equal key k -> raise Not_found
    | Diff { key = k; data = Some value; source = _; _ } when K.equal key k -> value
    | Diff { key = _; data = _; source = src; _ } -> find key src

  let rec find_opt key t =
    match !t with
    | HashTable ht ->
      ht_find_opt key ht
    | Diff { key = k; data = value_opt; source = _; _ } when K.equal key k -> value_opt
    | Diff { key = _; data = _; source = src; _ } -> find_opt key src

  let map f t =
    let table = create (capacity t) in
    let add_binding table key value =
      set key (f key value) table
    in
    fold add_binding table t

  let union f a b =
    let t = create (max (capacity a) (capacity b)) in
    let fold_a t key x =
      match find_opt key b with
      | Some y ->
        begin match f key x y with
          | Some z -> set key z t
          | None -> t
        end
      | None -> set key x t
    in
    let t = fold fold_a t a in
    let fold_b t key y =
      match find_opt key a with
      | Some _ -> t
      | None -> set key y t
    in
    fold fold_b t b

  let as_kvp_list d =
    fold
      (fun l k v -> (k,v)::l)
      []
      d

  let fold2
      (type a)
      (type b)
      (type c)
      (f:key -> a -> key -> b -> c -> c)
      (d1:a t)
      (d2:b t)
      (acc:c)
    : c =
    let fold2' acc ka va =
      fold (fun acc kb vb ->
          f ka va kb vb acc) acc d2
    in
    fold fold2' acc d1

  let pp
      (type a)
      (k_pp:Format.formatter -> key -> unit)
      (v_pp:Format.formatter -> a -> unit)
      (f:Format.formatter)
      (d:a t)
    : unit =
    let rec pp_kvp f kvp =
      begin match kvp with
        | [] -> ()
        | [(k,v)] ->
          Format.fprintf
            f
            "(%a,%a)"
            k_pp
            k
            v_pp
            v
        | (k,v)::l ->
          Format.fprintf
            f
            "(%a,%a);%a"
            k_pp
            k
            v_pp
            v
            pp_kvp
            l

      end
    in
    let kvp = as_kvp_list d in
    Format.fprintf
      f
      "[";
    pp_kvp f kvp;
    Format.fprintf
      f
      "]"

  let fold
      (type a)
      (type b)
      (f:key -> a -> b -> b)
      (d:a t)
      (acc:b)
    : b =
    fold (fun acc k v -> f k v acc) acc d

  let fold2 f a b x =
    let fold2' ka va x = fold (f ka va) b x in
    fold fold2' a x
end
