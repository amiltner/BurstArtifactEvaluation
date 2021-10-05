type t =
  | User of string
  | Fresh of int
  | Product of t * t

let count = ref 0

let next_id () =
  let id = !count in
  count := id+1;
  id

let create () = Fresh (next_id ())

let of_string id = User id

let string_opt = function
  | User id -> Some id
  | _ -> None

let rec compare a b =
  match a, b with
  | Product (a1, a2), Product (b1, b2) ->
    let c = compare a1 b1 in
    if c = 0 then compare a2 b2 else c
  | Product (_, _), _ -> 1
  | _, Product (_, _) -> -1
  | User ida, User idb ->
    String.compare ida idb
  | User _, _ -> 1
  | _, User _ -> -1
  | Fresh a, Fresh b ->
    a - b

let rec print t out =
  match t with
  | Product (x, y) ->
    Format.fprintf out "[%t%t]" (print x) (print y)
  | User id ->
    Format.fprintf out "%s" id
  | Fresh i ->
    Format.fprintf out "#%d" i

let rec equal a b =
  match a, b with
  | User a, User b -> a = b
  | Fresh a, Fresh b -> a = b
  | Product (a1, a2), Product (b1, b2) -> equal a1 b1 && equal a2 b2
  | _, _ -> false

let product a b =
  if equal a b then
    Some a
  else
    Some (Product (a, b))

let hash =
  Hashtbl.hash

let hash_fold_t = MyStdLib__.Util.hash_fold_from_hash hash
