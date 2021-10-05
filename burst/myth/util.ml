let rec update (m:('a * ('b list)) list)
               ((k, v):'a * 'b) : ('a * ('b list)) list =
  match m with
  | [] -> [(k, [v])]
  | (k', vs)::m -> if k = k' then (k', v::vs)::m else (k', vs)::update m (k, v)

let rec remove_first (f:'a -> bool) (l:'a list) : 'a list =
  match l with
  | [] -> []
  | x::l -> if f x then l else x::(remove_first f l)

(* Returns [0; ...; n-1] *)
let range (n:int) : int list =
  let rec f acc n =
    if n < 0 then acc else f (n :: acc) (n-1)
  in
  f [] (n-1)

(* Returns [1; ...; n] *)
let range1 (n:int) : int list =
  let rec f acc n =
    if n <= 0 then acc else f (n :: acc) (n-1)
  in
    f [] n

(* Returns [n; ...; m] *)
let rangen (n:int) (m:int) : int list =
  let rec f acc n =
    if n > m then acc else f (n :: acc) (n+1)
  in
    f [] n

let index_of (x:'a) (l:'a list) : int option =
  let rec helper n x l =
    match l with
    | []   -> None
    | y::l -> if x = y then Some n else helper (n+1) x l in
  helper 0 x l

let rec nub (l:'a list) : 'a list =
  match l with
  | [] -> []
  | x::l -> if List.mem x l then nub l else x :: nub l

let rec find (f:'a -> bool) (l:'a list) : 'a option =
  match l with
  | [] -> None
  | x::l -> if f x then Some x else find f l

let rec try_first (x:'a) (l:('a -> 'b option) list) : 'b option =
  match l with
  | [] -> None
  | f::l ->
    begin match f x with
    | Some y -> Some y
    | None -> try_first x l
    end

let rec try_first_lazy (l:'a option Lazy.t list) : 'a option =
  match l with
  | [] -> None
  | x::l ->
    begin match Lazy.force x with
    | Some v -> Some v
    | None -> try_first_lazy l
    end

let const (v:'a) : 'a -> 'a = fun _ -> v
let cons (x:'a) (l:'a list) : 'a list = x :: l

let rec replicate (n:int) (x:'a) : 'a list =
  if n <= 0 then [] else x::replicate (n-1) x

let rec find_first (f:'a -> bool) (l:'a list) : 'a option =
  match l with
  | [] -> None
  | x :: l -> if f x then Some x else find_first f l

let rec partitions (n:int) (k:int) : int list list =
  if n <= 0 || k <= 0 then
    []
  else if k == 1 then
    [[n]]
  else
    List.fold_left (fun res i ->
      List.append res @@ List.map (cons i) (partitions (n-i) (k-1)))
    [] (List.map ((+) 1) (range (n-k+1)))

type choice = MayNot | Must | May

let partitions_rel (k:int) : choice list list =
  let rec mark_part acc n c =
    if n >= k then acc else
    let ch =
      if c > 0 then May else if c = 0 then Must else MayNot
    in
      mark_part (ch :: acc) (n+1) (c-1)
  in
  List.map (mark_part [] 0) (range k |> List.rev)


let rec combinations (l:'a list list) : 'a list list =
  match l with
  | [] -> []
  | [x] -> List.map (fun n -> [n]) x
  | x :: l ->
    List.fold_left
      (fun res n -> List.append res (List.map (cons n) (combinations l)))
      [] x

let rec disjoint (l1:'a list) (l2:'a list) : bool =
  match l1 with
  | [] -> true
  | x::l1 -> if List.mem x l2 then false else disjoint l1 l2

let is_some : 'a option -> bool =
  function | Some _ -> true | None -> false

type ('a, 'b) either = Left of 'a | Right of 'b

(* Assumes p is transitive. *)
let rec all_eq (p:'a -> 'a -> bool) (l:'a list) : bool =
  match l with
  | [] -> true
  | [_] -> true
  | x::y::l -> if not (p x y) then false else all_eq p (y::l)

let one_true (f:'a -> bool) (l:'a list) : bool =
  List.fold_left (||) false (List.map f l)

let partition (n:int) (l:'a list) : 'a list * 'a * 'a list =
  let rec search pre n post =
    if n = 0 then
      (pre, List.hd post, List.tl post)
    else
      search (List.hd post :: pre) (n-1) (List.tl post)
  in
    if n < List.length l then
      search [] n l
    else
      raise @@ Invalid_argument "(partition) index out of range"

let separate ~f:(f:'a -> bool) (l:'a list) : 'a list * 'a list =
  let rec sep acc l =
    match l with
    | [] -> acc
    | x :: l ->
        let (lacc, racc) = acc in
        if f x then sep (lacc @ [x], racc) l else sep (lacc, racc @ [x]) l
  in
    sep ([], []) l

let time_action ~f:(f: unit -> 'a) : float * 'a =
  let t1  = Unix.gettimeofday () in
  let res = f () in
  let t2  = Unix.gettimeofday () in
  (t2 -. t1, res)


(***** Association lists {{{ *****)

(* Returns a value as an option if key is in the list *)
let rec lookup (k:'a) (l:('a * 'b) list) : 'b option =
  match l with
  | [] -> None
  | (k', v)::l -> if k = k' then Some v else lookup k l

(* Returns a list of keys *)
let fst_assoc (l:('a * 'b) list) : 'a list =
  List.map fst l

(* Returns a list of values *)
let snd_assoc (l:('a * 'b) list) : 'b list =
  List.map snd l

(* Zips two lists by their keys *)
let rec zip_with_keys (bs: ('a * 'b) list) (cs: ('a * 'c) list) : ('a * ('b * 'c)) list =
  if List.length bs <> List.length cs
  then raise @@ Invalid_argument "(zip_without_key) lists have length unequal lengths"
  else begin match bs with
       | [] -> []
       | (key,b) :: bs' ->
         begin match lookup key cs with
           | None -> raise Not_found
           | Some c -> (key,(b,c)) :: zip_with_keys bs' (List.remove_assoc key cs)
          end
       end

(* Zips two lists by their keys but disassociates values them from their keys *)
let rec zip_without_keys (bs: ('a * 'b) list) (cs: ('a * 'c) list) : ('b * 'c) list =
  if List.length bs <> List.length cs
  then raise @@ Invalid_argument "(zip_without_key) lists have length unequal lengths"
  else begin match bs with
       | [] -> []
       | (key,b) :: bs' ->
         begin match lookup key cs with
           | None -> raise Not_found
           | Some c -> (b,c) :: zip_without_keys bs' (List.remove_assoc key cs)
          end
       end

(* Combines a list of lists by grouping together values with equal keys *)
let combine_assoc (l: ('a * 'b) list list) : ('a * 'b list) list =
  List.fold_left (fun acc l' ->
    List.map (fun (k,v) ->
      begin match lookup k acc with
      | None -> (k,[v])
      | Some vs -> (k, v::vs)
      end
    ) l'
  ) [] l

(***** }}} *****)

module Operators = struct 
    let (>?>) (x : 'a option) (f : 'a -> 'b option) : 'b option = match x with
      | None -> None
      | Some v -> f v
  end

open Core

let sort_and_partition_with_indices ~(cmp : 'a -> 'a -> int)
    (l:'a list)
  : ('a * int) list list =
  let rec merge_grouped_things (remaining:('a * int) list)
      (currentacc:('a*int) list)
      (accacc:('a*int) list list)
    : ('a*int) list list =
    begin match remaining with
      | [] -> currentacc :: accacc
      | (h,i)::t -> let currenthd = fst (List.hd_exn currentacc)
        in match cmp h currenthd with
        | 0 -> merge_grouped_things t ((h,i)::currentacc) accacc
        | _ -> merge_grouped_things t [(h,i)] (currentacc::accacc)
    end in
  let sorted = List.sort ~compare:(fun (x,_) (y,_) -> cmp x y)
      (List.mapi ~f:(fun i x -> (x,i)) l)
  in begin match sorted with
    | [] -> []
    | h::t -> merge_grouped_things t [h] []
  end

let core_deduper
    (type a)
    ~(compare:a -> a -> int)
    ~(to_size:a -> int)
    (xs:a list)
  : a list =
  let sized_xs =
    List.map
      ~f:(fun x -> (x,to_size x))
      xs
  in
  let sorted_parititioned_i =
    sort_and_partition_with_indices
      ~cmp:(fun (e1,_) (e2,_) -> compare e1 e2)
      sized_xs
  in
  List.map
    ~f:(fun esl ->
        let ordered_by_size =
          List.sort
            ~compare:(fun ((_,s1),_) ((_,s2),_) -> Core.Int.compare s1 s2)
            esl
        in
        let ((a,_),_) = List.hd_exn ordered_by_size in
        a)
    sorted_parititioned_i
