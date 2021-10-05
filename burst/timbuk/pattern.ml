module type ORDERED_FORMAT_TYPE = Symbol.ORDERED_FORMAT_TYPE

module type VARIABLE = sig
  include ORDERED_FORMAT_TYPE

  val product : t -> t -> t option
end

type position = Term.position

module Holder = struct
  open MyStdLib
  type ('sym, 'x) pattern =
    | Cons of 'sym * (('sym, 'x) pattern) list
    | Var of 'x
  [@@deriving eq, hash, ord]
end
include Holder

module type S = sig
  module Sym : Symbol.S
  module Var : VARIABLE

  type ('sym, 'x) abs_pattern = ('sym, 'x) pattern =
    | Cons of 'sym * (('sym, 'x) pattern) list
    | Var of 'x
  type term = Sym.t Term.term
  type t_node = (Sym.t, Var.t) pattern

  type t = t_node MyStdLib.hash_consed

  exception InvalidPosition of position * t

  val create : t_node -> t
  val node : t -> t_node
  val of_term : term -> t
  val of_var : Var.t -> t
  val is_cons : t -> bool
  val is_var : t -> bool
  val normalized : t -> Var.t
  val subterm : position -> t -> t
  val subterm_opt : position -> t -> t option
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val hash_fold_t : t Base.Hash.folder
  val fold : (Var.t -> 'a -> 'a) -> t -> 'a -> 'a
  val is_closed : t -> bool
  val for_all : (Var.t -> bool) -> t -> bool
  val instanciate : (Var.t -> term) -> t -> term
  val as_term : t -> term
  val product : t -> t -> t option
  val print : t -> Format.formatter -> unit
  val print_var : (Var.t -> Format.formatter -> unit) -> t -> Format.formatter -> unit
  end

module Make (F: Symbol.S) (X : VARIABLE) = struct
  module Sym = F
  module Var = X

  module Holder = struct
    open MyStdLib
    type ('sym, 'x) abs_pattern = ('sym, 'x) pattern =
      | Cons of 'sym * (('sym, 'x) pattern) list
      | Var of 'x
    [@@deriving eq, hash, ord]
    type term = Sym.t Term.term
    [@@deriving eq, hash, ord]
    type t_node = (Sym.t, Var.t) pattern
    [@@deriving eq, hash, ord]

    type t = t_node hash_consed
    [@@deriving eq, hash, ord]

    let table = HashConsTable.create 1000

    let create
        (node:t_node)
      : t =
      HashConsTable.hashcons
        hash_t_node
        compare_t_node
        table
        node

    let node (x:t)
      : t_node =
      x.node
  end
  include Holder

  exception InvalidPosition of position * t

  let cons f l =
    create (if Sym.arity f = List.length l then
      Cons (f, l)
            else raise (Invalid_argument "symbol arity does not match list length"))

  let rec of_term (Term.Term (f, l)) =
    Cons (f, List.map (of_term) l)

  let of_term x = create (of_term x)

  let of_var x =
    create (Var x)

  let is_cons x =
    match node x with
    | Cons _ -> true
    | _ -> false

  let is_var x =
    match node x with
    | Var _ -> true
    | _ -> false

  let normalized x =
    match node x with
    | Var x -> x
    | _ -> raise (Invalid_argument "not normalized.")

  let rec subterm_opt pos t =
    match pos, t with
    | Term.Subterm (i, pos), Cons (_, l) ->
      (match List.nth_opt l i with Some s -> subterm_opt pos s | None -> None)
    | Term.Root, _ -> Some (create t)
    | _, _ -> None

  let subterm_opt pos t =
    subterm_opt pos (node t)

  let subterm pos t =
    match subterm_opt pos t with
    | Some t -> t
    | None -> raise (InvalidPosition (pos, t))

  (* let variables t =
     let rec vars set = function
      | Cons (f, l) -> List.fold_left (vars) set l
      | Var x -> VarSet.add x set
     in vars (VarSet.empty) t *)

  let fold f t x =
    let rec do_fold t x =
      match t with
      | Cons (_, l) -> List.fold_right do_fold l x
      | Var var -> f var x
    in
    do_fold (node t) x

  let rec is_closed = function
    | Cons (_, l) -> List.for_all (is_closed) l
    | Var _ -> false

  let is_closed x = is_closed (node x)

  let rec for_all f = function
    | Cons (_, l) -> List.for_all (for_all f) l
    | Var x -> f x

  let for_all f x = for_all f (node x)

  let rec apply sigma = function
    | Cons (f, l) -> Cons (f, List.map (apply sigma) l)
    | Var x ->
      try sigma x with
      | Not_found -> Var x
  let apply s x = create (apply s (node x))

  let rec instanciate sigma = function
    | Cons (f, l) -> Term.Term (f, List.map (instanciate sigma) l)
    | Var x -> sigma x
  let instanciate s x = instanciate s (node x)

  let as_term t =
    instanciate (function _ -> raise (Invalid_argument "pattern is not a term")) t

  let rec product a b =
    match a, b with
    | Cons (fa, la), Cons (fb, lb) when Sym.compare fa fb = 0 ->
      let fold_product c d l = begin
        match l with
        | Some l ->
          begin
            match product c d with
            | Some p -> Some (p::l)
            | None -> None
          end
        | None -> None
      end in
      begin
        match List.fold_right2 (fold_product) la lb (Some []) with
        | Some l -> Some (Cons (fa, l))
        | None -> None
      end
    | Var x, Var y ->
      begin
        match Var.product x y with
        | Some z -> Some (Var z)
        | None -> None
      end
    | _ ->
      None

  let product a b = Option.map (create) (product (node a) (node b))

  let rec print_var pp_var t out =
    match t with
    | Cons (f, []) -> Sym.print f out
    | Cons (f, l) ->
      Format.fprintf out "%t(%t)" (Sym.print f) (Collections.List.print (print_var pp_var) ", " l)
    | Var x -> pp_var x out

  let print_var pp_var t out = print_var pp_var (node t) out

  let print = print_var Var.print
end

module Ext (A : S) (B : S with module Sym = A.Sym) = struct
  let rec substitute sigma = function
    | A.Cons (f, l) -> B.Cons (f, List.map (substitute sigma) l)
    | A.Var x -> sigma x
end

module Product (A : S) (B : S with module Sym = A.Sym) (AB : S with module Sym = B.Sym) = struct
  let rec product mult a b =
    match a, b with
    | A.Cons (fa, la), B.Cons (fb, lb) when A.Sym.compare fa fb = 0 ->
      let fold_product c d l = begin
        match l with
        | Some l ->
          begin
            match product (mult) c d with
            | Some p -> Some (p::l)
            | None -> None
          end
        | None -> None
      end in
      begin
        match List.fold_right2 (fold_product) la lb (Some []) with
        | Some l -> Some (AB.Cons (fa, l))
        | None -> None
      end
    | A.Var x, B.Var y ->
      begin
        match mult x y with
        | Some z -> Some (AB.Var z)
        | None -> None
      end
    | _ ->
      None
end
