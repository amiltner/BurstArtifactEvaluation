type position = TypedTerm.position

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

  (** Get all the variables in the term. *)
  (* val variables : t -> VarSet.t *)

  val is_var : t -> bool

  val is_closed : t -> bool

  val for_all : (Var.t -> Type.t -> bool) -> t -> bool

  val fold : (t -> 'a -> 'a) -> t -> 'a -> 'a

  val iter : (t -> unit) -> t -> unit

  val instanciate : (Var.t -> Type.t -> typed_term) -> t -> typed_term

  val substitution : t -> Type.t Substitution.t
  (* May raise an Invalid_argument if the term is not well-typed. *)
  (* In this case, well-typed means that a variable have a single type. *)

  val substitution_opt : t -> (Type.t Substitution.t) option
  (* Returns None is the term is not well typed. *)
  (* In this case, well-typed means that a variable have a single type. *)

  val get_substitution : t -> typed_term -> Var.t -> Type.t -> typed_term

  val apply : (Var.t -> Type.t -> t) -> t -> t

  val substitute_types : (Var.t -> Type.t) -> t -> t
  (** Replace the types of the variables using the given substitution. *)

  val rename : (Var.t -> Var.t) -> t -> t

  (** Pattern internal product. *)
  val product : t -> t -> t option

  val print : t -> Format.formatter -> unit

  (** Format with a special formatter for variables *)
  val print_var : (Var.t -> Format.formatter -> unit) -> t -> Format.formatter -> unit
end

module Make (F: Symbol.S) (X : Pattern.VARIABLE) (T: TypedTerm.TYPE) : sig
  include S
    with module Sym = F
     and module Var = X
     and module Type = T
end

(** Pattern external operations. *)
(* module Ext (A : S) (B : S with module Sym = A.Sym and module Type = A.Type and module Var = A.Var) : sig
   val substitute : B.t A.Substitution.t -> A.t -> B.t
   end *)

(* module Product
    (A : S)
    (B : S with module Term = A.Term and module Type = A.Type and module Var = A.Var)
    (AB : S with module Term = B.Term and module Type = B.Type and module Var = B.Var)
   : sig
    val product : (A.Var.t -> B.Var.t -> AB.Var.t option) -> A.t -> B.t -> AB.t option
    (** Pattern external product *)
   end *)
