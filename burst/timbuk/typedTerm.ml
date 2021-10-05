module type TYPE = sig
  include Pattern.VARIABLE
end

type position = Term.position

type ('sym, 'ty) typed_term = ('sym, 'ty) value * 'ty

and ('sym, 'ty) value =
  | Term of 'sym * (('sym, 'ty) typed_term) list
  | Cast of ('sym, 'ty) typed_term

module type S = sig
  module Sym : Symbol.S
  module Type : TYPE
  type ('sym, 'ty) abs_value = ('sym, 'ty) value =
    | Term of 'sym * (('sym, 'ty) typed_term) list
    | Cast of ('sym, 'ty) typed_term
  type term = Sym.t Term.term
  type t = (Sym.t, Type.t) typed_term
  exception MalformedTerm
  exception InvalidPosition of position * t
  val create : Sym.t -> t list -> Type.t -> t
  val subterm : position -> t -> t
  val subterm_opt : position -> t -> t option
  val size : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val product : t -> t -> t option
  val hash : t -> int
  val strip : t -> term
  val print : t -> Format.formatter -> unit
end

module Make (F : Symbol.S) (Type : TYPE) = struct
  module Sym = F
  module Type = Type

  type ('sym, 'ty) abs_value = ('sym, 'ty) value =
    | Term of 'sym * (('sym, 'ty) typed_term) list
    | Cast of ('sym, 'ty) typed_term

  type term = Sym.t Term.term
  type t = (Sym.t, Type.t) typed_term

  exception MalformedTerm
  exception InvalidPosition of position * t

  let create f l typ =
    if Sym.arity f = List.length l then
      Term (f, l), typ
    else raise MalformedTerm

  let rec subterm_opt pos t =
    match pos, t with
    | pos, (Cast t, _) -> subterm_opt pos t
    | Term.Subterm (i, pos), (Term (_, l), _) ->
      (match List.nth_opt l i with Some s -> subterm_opt pos s | None -> None)
    | Term.Root, _ -> Some t

  let subterm pos t =
    match subterm_opt pos t with
    | Some t -> t
    | None -> raise (InvalidPosition (pos, t))

  let rec strip = function
    | (Term (f, l), _) -> Term.Term (f, List.map (strip) l)
    | (Cast term, _) -> strip term

  let rec size = function
    | Term (_, l), _ -> List.fold_left (fun s e -> s + size e) 1 l
    | Cast term, _ -> 1 + size term

  let rec compare a b =
    match a, b with
    | (Term (fa, la), ta), (Term (fb, lb), tb) ->
      let c = Type.compare ta tb in
      if c = 0 then
        let rec lex_order la lb = (* lexicographic order to compare subterms *)
          match la, lb with
          | [], [] -> 0 (* terms are equals *)
          | a::la, b::lb ->
            let c = compare a b in
            if c = 0 then lex_order la lb else c
          | _, _ -> raise MalformedTerm
        in
        let c = Sym.compare fa fb in (* first we compare the constructors... *)
        if c = 0 then lex_order la lb else c (* ...if there are equals, we compare the subterms. *)
      else c
    | (Cast a, ta), (Cast b, tb) ->
      let c = Type.compare ta tb in
      if c = 0 then compare a b else c
    | (Cast _, _), _ -> 1
    | _, (Cast _, _) -> -1

  let rec equal a b =
    match a, b with
    | (Term (fa, la), ta), (Term (fb, lb), tb) ->
      Type.equal ta tb && Sym.equal fa fb && List.for_all2 (fun sa sb -> equal sa sb) la lb
    | (Cast a, ta), (Cast b, tb) ->
      Type.equal ta tb && equal a b
    | _, _ -> false

  let product a b =
    (* TODO make a real product using type products. *)
    if equal a b then Some a else None

  let hash t = Hashtbl.hash t

  let rec print t out =
    match t with
    | (Term (f, l), typ) ->
      Sym.print f out;
      begin
        match l with
        | [] -> ()
        | _ ->
          Format.fprintf out "(%t)" (Collections.List.print print ", " l)
      end;
      Format.fprintf out ":%t" (Type.print typ)
    | (Cast t, typ) ->
      Format.fprintf out "(%t):%t" (print t) (Type.print typ)
end
