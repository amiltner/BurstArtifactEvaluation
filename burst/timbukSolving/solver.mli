open Collections

module type VARIABLE = sig
  include Map.OrderedType

  val print : t -> Format.formatter -> unit
end

module type S = sig
  module Var : VARIABLE

  type t

  type const

  module Model : Map.S with type key = Var.t

  type model = int Model.t

  type atom =
    | Variable of Var.t
    | Constant of const

  type expr =
    | Eq of atom * atom
    | Neq of atom * atom
    | Or of expr list
    | And of expr list
    | Impl of expr * expr

  type 'a result =
    | Sat of 'a
    | Unsat
    | Unknown (* when there is a timeout. *)

  val create : unit -> t

  val release : t -> unit
  (** [release t] declares that the solver won't be used anymore.
      This will cause the underlying solving resources to be freed.
      Using [t] after calling [release t] can cause undefined behavior. *)

  val declare : Var.t -> t -> t

  val new_const : t -> t * const

  val add : expr -> t -> t

  val mem : expr -> t -> bool

  val solve : ?debug:bool -> t -> model result

  (** A constraints to the solver to get the next possible solution. *)
  val next : t -> t result

  val print : t -> Format.formatter -> unit

  type error =
    | UndefinedVariable of Var.t

  exception Error of error
end
