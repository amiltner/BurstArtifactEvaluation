type t =
	| Base of string
	| Product of t * t

let of_string id = Base id

let string_opt = function
  | Base id -> Some id
  | Product _ -> None

let product a b = Some (Product (a, b))

let rec compare a b =
	match a, b with
	| Product (a1, a2), Product (b1, b2) ->
		let c = compare a1 b1 in
		if c = 0 then compare a2 b2 else c
	| Product (_, _), _ -> 1
	| _, Product (_, _) -> -1
	| Base ida, Base idb ->
		String.compare ida idb

let rec print t out =
  match t with
  | Product (x, y) ->
    Format.fprintf out "[%t%t]" (print x) (print y)
  | Base id ->
    Format.fprintf out "%s" id

let rec equal a b =
	match a, b with
	| Base a, Base b -> a = b
	| Product (a1, a2), Product (b1, b2) -> equal a1 b1 && equal a2 b2
	| _, _ -> false

let hash =
  Hashtbl.hash

let hash_fold_t = MyStdLib__.Util.hash_fold_from_hash hash
