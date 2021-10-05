type t =
	| Fresh of int
	| Product of t * t

let count = ref 0

let next_id () =
	let id = !count in
	count := id+1;
	id

let create () = Fresh (next_id ())

let of_int i = Fresh i

let int_opt = function
  | Fresh i -> Some i
  | Product _ -> None

let product a b = Some (Product (a, b))

let rec compare a b =
	match a, b with
	| Product (a1, a2), Product (b1, b2) ->
		let c = compare a1 b1 in
		if c = 0 then compare a2 b2 else c
	| Product (_, _), _ -> 1
	| _, Product (_, _) -> -1
	| Fresh ida, Fresh idb ->
		ida - idb

let rec print t out =
  match t with
  | Product (x, y) ->
    Format.fprintf out "[%t%t]" (print x) (print y)
  | Fresh id ->
    Format.fprintf out "q%d" id

let rec equal a b =
	match a, b with
	| Fresh a, Fresh b -> a = b
	| Product (a1, a2), Product (b1, b2) -> equal a1 b1 && equal a2 b2
	| _, _ -> false

let rec hash = function
	| Fresh i -> i
	| Product (a, b) -> (hash a) lxor (hash b)

let hash_fold_t = MyStdLib__.Util.hash_fold_from_hash hash
