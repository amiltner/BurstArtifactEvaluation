
module Holder = struct
  open MyStdLib
  type position =
    | Root
    | Subterm of int * position
  [@@deriving eq, hash, ord]

  type 'sym term =
    | Term of 'sym * ('sym term) list
  [@@deriving eq, hash, ord]
end
include Holder

module type S = sig
  module Sym : Symbol.S
  type 'sym abs_term = 'sym term =
    | Term of 'sym * ('sym term) list
  type t = Sym.t term
  exception MalformedTerm
  exception InvalidPosition of position * t
  val create : Sym.t -> t list -> t
  val subterm : position -> t -> t
  val subterm_opt : position -> t -> t option
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val print : t -> Format.formatter -> unit
end

module Make (S : Symbol.S) = struct
  module Sym = S

  type 'sym abs_term = 'sym term =
    | Term of 'sym * ('sym term) list

  type t = Sym.t term

  exception MalformedTerm

  exception InvalidPosition of position * t

  let create f l =
    if Sym.arity f = List.length l then
      Term (f, l)
    else raise MalformedTerm

  let rec subterm_opt pos t =
    match pos, t with
    | Subterm (i, pos), Term (_, l) ->
      (match List.nth_opt l i with Some s -> subterm_opt pos s | None -> None)
    | Root, _ -> Some t

  let subterm pos t =
    match subterm_opt pos t with
    | Some t -> t
    | None -> raise (InvalidPosition (pos, t))

  let rec compare (Term (fa, la)) (Term (fb, lb)) =
    let rec lex_order la lb = (* lexicographic order to compare subterms *)
      match la, lb with
      | [], [] -> 0 (* terms are equals *)
      | a::la, b::lb ->
        let c = compare a b in
        if c = 0 then lex_order la lb else c
      | _::_, [] -> -1
      | _, _ -> 1
    in
    let c = Sym.compare fa fb in (* first we compare the constructors... *)
    if c = 0 then lex_order la lb else c (* ...if there are equals, we compare the subterms. *)

  let rec equal (Term (fa, la)) (Term (fb, lb)) =
    Sym.equal fa fb && List.for_all2 (fun ta tb -> equal ta tb) la lb

  let hash t = Hashtbl.hash t

  let rec print (Term (f, l)) out =
    Sym.print f out;
    match l with
    | [] ->
      ()
    | _ ->
      Format.fprintf out "(%t)" (Collections.List.print print ", " l)
end
