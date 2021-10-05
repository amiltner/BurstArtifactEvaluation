type position = Term.position

type ('sym, 'x, 'ty) typed_pattern = ('sym, 'x, 'ty) value * 'ty

and ('sym, 'x, 'ty) value =
  | Cons of 'sym * (('sym, 'x, 'ty) typed_pattern) list
  | Var of 'x
  | Cast of ('sym, 'x, 'ty) typed_pattern

module type S = sig
  module Sym : Symbol.S
  module Var : Pattern.VARIABLE
  module Type : TypedTerm.TYPE

  module Substitution : Substitution.S with type key = Var.t

  type ('sym, 'x, 'ty) abs_value = ('sym, 'x, 'ty) value =
    | Cons of 'sym * (('sym, 'x, 'ty) typed_pattern) list
    | Var of 'x
    | Cast of ('sym, 'x, 'ty) typed_pattern

  type pattern = (Sym.t, Var.t) Pattern.pattern
  type typed_term = (Sym.t, Type.t) TypedTerm.typed_term
  type t = (Sym.t, Var.t, Type.t) typed_pattern

  exception InvalidPosition of position * t

  val create : Sym.t -> t list -> Type.t -> t
  val of_var : Var.t -> Type.t -> t
  val of_term : typed_term -> t
  val as_term : t -> typed_term
  val as_term_opt : t -> typed_term option
  val normalized : t -> Var.t * Type.t
  val strip : t -> pattern
  val subterm : position -> t -> t
  val subterm_opt : position -> t -> t option
  val size : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val hash_fold_t : t Base.Hash.folder
  val is_var : t -> bool
  val is_closed : t -> bool
  val for_all : (Var.t -> Type.t -> bool) -> t -> bool
  val fold : (t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter : (t -> unit) -> t -> unit
  val instanciate : (Var.t -> Type.t -> typed_term) -> t -> typed_term
  val substitution : t -> Type.t Substitution.t
  val substitution_opt : t -> (Type.t Substitution.t) option
  val get_substitution : t -> typed_term -> Var.t -> Type.t -> typed_term
  val apply : (Var.t -> Type.t -> t) -> t -> t
  val substitute_types : (Var.t -> Type.t) -> t -> t
  val rename : (Var.t -> Var.t) -> t -> t
  val product : t -> t -> t option
  val print : t -> Format.formatter -> unit
  val print_var : (Var.t -> Format.formatter -> unit) -> t -> Format.formatter -> unit
end

let rec list_map_opt f = function
  | [] -> Some []
  | e::l ->
    begin
      match list_map_opt f l with
      | Some l ->
        begin
          match f e with
          | Some e -> Some (e::l)
          | None -> None
        end
      | None -> None
    end

module Make (F: Symbol.S) (X : Pattern.VARIABLE) (T : TypedTerm.TYPE) = struct
  module Sym = F
  module Var = X
  module Type = T

  module Substitution = Substitution.Make (Var)

  type ('sym, 'x, 'ty) abs_value = ('sym, 'x, 'ty) value =
    | Cons of 'sym * (('sym, 'x, 'ty) typed_pattern) list
    | Var of 'x
    | Cast of ('sym, 'x, 'ty) typed_pattern

  type pattern = (Sym.t, Var.t) Pattern.pattern
  type typed_term = (Sym.t, Type.t) TypedTerm.typed_term
  type t = (Sym.t, Var.t, Type.t) typed_pattern

  exception InvalidPosition of position * t

  let create f l typ =
    if Sym.arity f = List.length l then
      Cons (f, l), typ
    else raise (Invalid_argument "symbol arity does not match list length")

  let of_var x typ =
    Var x, typ

  let rec of_term = function
    | TypedTerm.Term (f, l), typ -> Cons (f, List.map of_term l), typ
    | TypedTerm.Cast t, typ -> Cast (of_term t), typ

  let rec instanciate sigma = function
    | Cons (f, l), typ -> TypedTerm.Term (f, List.map (instanciate sigma) l), typ
    | Cast t, typ -> TypedTerm.Cast (instanciate sigma t), typ
    | Var x, typ -> sigma x typ

  let rec as_term_opt = function
    | Cons (f, l), typ ->
      begin
        match list_map_opt as_term_opt l with
        | Some l -> Some (TypedTerm.Term (f, l), typ)
        | None -> None
      end
    | Cast t, typ ->
      begin
        match as_term_opt t with
        | Some t -> Some (TypedTerm.Cast t, typ)
        | None -> None
      end
    | Var _, _ -> None

  let as_term t =
    match as_term_opt t with
    | Some t -> t
    | None -> raise (Invalid_argument "TypedPattern.as_term: this pattern contains variables.")

  let normalized = function
    | Var x, ty -> x, ty
    | _ -> raise (Invalid_argument "TypedPattern.normalized: not a variable.")

  let rec strip = function
    | Cons (f, l), _ -> Pattern.Cons (f, List.map strip l)
    | Cast t, _ -> strip t
    | Var x, _ -> Pattern.Var x

  let rec subterm_opt pos (t, typ) =
    match pos, t with
    | pos, Cast term -> subterm_opt pos term
    | Term.Subterm (i, pos), Cons (_, l) ->
      (match List.nth_opt l i with Some s -> subterm_opt pos s | None -> None)
    | Term.Root, _ -> Some (t, typ)
    | _, _ -> None

  let subterm pos t =
    match subterm_opt pos t with
    | Some t -> t
    | None -> raise (InvalidPosition (pos, t))

  let rec size = function
    | Cons (_, l), _ -> List.fold_left (fun s e -> s + size e) 1 l
    | Cast pattern, _ -> 1 + size pattern
    | Var _, _ -> 1

  let rec compare (a, ta) (b, tb) =
    let c = Type.compare ta tb in
    if c = 0 then
      match a, b with
      | Var x, Var y -> Var.compare x y
      | Var _, _ -> 1
      | _, Var _ -> -1
      | Cast a, Cast b -> compare a b
      | Cast _, _ -> 1
      | _, Cast _ -> -1
      | Cons (fa, la), Cons (fb, lb) -> (* copy/paste from above *)
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
    else c

  let rec equal (a, ta) (b, tb) =
    Type.equal ta tb &&
    begin
      match a, b with
      | Var x, Var y -> Var.equal x y
      | Cast a, Cast b -> equal a b
      | Cons (fa, la), Cons (fb, lb) ->
        Sym.equal fa fb && List.for_all2 (fun sa sb -> equal sa sb) la lb
      | _, _ -> false
    end

  let hash t = Hashtbl.hash t
  let hash_fold_t s v = (MyStdLib__.Util.hash_fold_from_hash hash) s v

  let is_var = function
    | Var _, _ -> true
    | _, _ -> false

  (* let variables t =
     let rec vars set = function
      | (Cons (f, l), _) -> List.fold_left (vars) set l
      | (Cast t, _) -> vars set t
      | (Var x, _) -> VarSet.add x set
     in vars (VarSet.empty) t *)

  let rec is_closed = function
    | Cons (_, l), _ -> List.for_all (is_closed) l
    | Cast t, _ -> is_closed t
    | Var _, _ -> false

  let rec for_all f = function
    | Cons (_, l), _ -> List.for_all (for_all f) l
    | Cast t, _ -> for_all f t
    | Var x, typ -> f x typ

  let rec fold f t x =
    match t with
    | Cons (_, l), _ -> f t (List.fold_right (fold f) l x)
    | Cast t', _ -> f t (f t' x)
    | Var _, _ -> f t x

  let iter f t =
    fold (fun t' () -> f t') t ()

  let rec apply sigma = function
    | Cons (f, l), typ -> (Cons (f, List.map (apply sigma) l), typ)
    | Cast t, typ -> (Cast (apply sigma t), typ)
    | Var x, typ ->
      try sigma x typ with
      | Not_found ->
        Var x, typ

  let rec substitute_types sigma = function
    | Cons (f, l), typ -> Cons (f, List.map (substitute_types sigma) l), typ
    | Cast pattern, typ -> Cast (substitute_types sigma pattern), typ
    | Var x, _ -> Var x, sigma x

  let rec rename g = function
    | Cons (f, l), typ -> Cons (f, List.map (rename g) l), typ
    | Cast pattern, typ -> Cast (rename g pattern), typ
    | Var x, typ -> Var (g x), typ

  let rec substitution_opt = function
    | Cons (_, l), _ ->
      begin
        let add sigma t =
          match sigma with
          | Some s1 ->
            begin
              let sigma' = substitution_opt t in
              match sigma' with
              | Some s2 -> Some (Substitution.union Type.product s1 s2)
              | None -> None
            end
          | None -> None
        in
        List.fold_left add (Some Substitution.empty) l
      end
    | Cast t, _ -> substitution_opt t
    | Var x, typ -> Some (Substitution.singleton x typ)

  let substitution t =
    match substitution_opt t with
    | Some sigma -> sigma
    | None -> raise (Invalid_argument "No valid substitution")

  let get_substitution t term =
    let module TypedTerm = TypedTerm.Make (Sym) (Type) in
    let table = Hashtbl.create 8 in
    let rec get (t, ty) (term, ty') =
      match Type.product ty ty' with
      | Some ty ->
        begin match t, term with
          | Cons (f, l), TypedTerm.Term (f', l') when Sym.equal f f' ->
            List.iter2 get l l'
          | Var x, term ->
            begin match Hashtbl.find_opt table x with
              | Some term' ->
                begin match TypedTerm.product (term, ty) term' with
                  | Some term ->
                    Hashtbl.replace table x term
                  | None ->
                    raise Not_found
                end
              | None ->
                Hashtbl.replace table x (term, ty)
            end
          | Cast t', TypedTerm.Cast term' ->
            get t' term'
          | _ ->
            raise Not_found
        end
      | None ->
        raise Not_found
    in
    get t term;
    fun x _ -> Hashtbl.find table x

  let rec product (a, ta) (b, tb) =
    match Type.product ta tb with
    | Some t ->
      begin
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
            | Some l -> Some (Cons (fa, l), t)
            | None -> None
          end
        | Cast a, Cast b ->
          begin
            match product a b with
            | Some p -> Some (Cast p, t)
            | None -> None
          end
        | Var x, Var y ->
          begin
            match Var.product x y with
            | Some z -> Some (Var z, t)
            | None -> None
          end
        | _ ->
          None
      end
    | None -> None

  let rec print_var pp_var (p, typ) out =
    begin
      match p with
      | Cons (f, []) -> Sym.print f out
      | Cons (f, l) ->
        Format.fprintf out "%t(%t)" (Sym.print f) (Collections.List.print (print_var pp_var) ", " l)
      | Cast t ->
        Format.fprintf out "(%t)" (print_var pp_var t)
      | Var x ->
        pp_var x out
    end;
    Format.fprintf out ":%t" (Type.print typ)

  let print = print_var Var.print
end

(* module Ext (A : S) (B : S with module Term = A.Term and module Type = A.Type and module Var = A.Var) = struct
   let rec substitute sub = function
    | (A.Cons (f, l), typ) -> (B.Cons (f, List.map (substitute sub) l), typ)
    | (A.Cast t, typ) -> (B.Cast (substitute sub t), typ)
    | (A.Var x, _) -> A.Substitution.find x sub
   end

   module Product
    (A : S)
    (B : S with module Term = A.Term and module Type = A.Type and module Var = A.Var)
    (AB : S with module Term = B.Term and module Type = B.Type and module Var = B.Var)
   = struct
   module Type = A.Type

   let rec product mult (a, ta) (b, tb) =
    match Type.product ta tb with
    | Some t ->
      begin
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
            | Some l -> Some (AB.Cons (fa, l), t)
            | None -> None
          end
        | A.Cast a, B.Cast b ->
          begin
            match product mult a b with
            | Some p -> Some (AB.Cast p, t)
            | None -> None
          end
        | A.Var x, B.Var y ->
          begin
            match mult x y with
            | Some z -> Some (AB.Var z, t)
            | None -> None
          end
        | _ ->
          None
      end
    | None -> None
   end *)
