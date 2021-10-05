include Stdlib.List

let fold_inline_combinations f l x =
  let rec do_fold combination l x =
    match l with
    | [] -> f (rev combination) x
    | es::l ->
      fold_right (
        fun e x ->
          do_fold (e::combination) l x
      ) es x
  in
  do_fold [] l x

let fold_bool_combinations f n x =
  let rec do_fold combination n x =
    match n with
    | 0 -> f combination x
    | _ ->
      let n' = n - 1 in
      do_fold (false::combination) n' (do_fold (true::combination) n' x)
  in
  do_fold [] n x

let rec compare f la lb =
  match la, lb with
  | [], [] -> 0 (* terms are equals *)
  | a::la, b::lb ->
    let c = f a b in
    if c = 0 then compare f la lb else c
  | _::_, [] -> -1
  | _, _ -> 1

let rec equal f la lb =
  match la, lb with
  | [], [] -> true
  | a::la, b::lb ->
    f a b && equal f la lb
  | _::_, [] -> false
  | _, _ -> false

let rec map_opt f = function
  | [] -> Some []
  | e::l ->
    begin
      match map_opt f l with
      | Some l ->
        begin
          match f e with
          | Some e -> Some (e::l)
          | None -> None
        end
      | None -> None
    end

let rec map2_opt f la lb =
  match la, lb with
  | [], [] -> Some []
  | a::la, b::lb ->
    begin
      match map2_opt f la lb with
      | Some l ->
        begin
          match f a b with
          | Some c -> Some (c::l)
          | None -> None
        end
      | None -> None
    end
  | _, _ -> raise (Invalid_argument "lists must have the same length")

let transpose f ll =
  let transposed = match ll with
    | [] -> []
    | l::ll ->
      let transposed = map (function e -> [e]) l in
      fold_left (
        fun transposed l ->
          map2 (cons) l transposed
      ) transposed ll
  in
  map (function l -> f (rev l)) transposed

let inner_fold2 g k l1 l2 accu =
  let rec fold l1 l2 ll accu =
    begin match l1, l2 with
      | [], [] -> g (rev ll) accu
      | a::l1', b::l2' ->
        k (
          fun c accu ->
            fold l1' l2' (c::ll) accu
        ) a b accu
      | _ -> raise (Invalid_argument "lists must have the same length")
    end
  in
  fold l1 l2 [] accu

let rec print f sep l out =
  match l with
  | [] ->
    ()
  | x::[] ->
    f x out
  | x::l ->
    Format.fprintf out "%t%s%t" (f x) sep (print f sep l)
