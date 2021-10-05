open Codemap

module type S = sig
  module Id: Set.OrderedType
  module Type: sig type t end

  type t

  exception AlreadyDefined of Span.t

  val empty : t

  val mem : Id.t -> t -> bool

  val add : Id.t -> Type.t Span.located -> t -> t

  (** May fail with Not_found. *)
  val find : Id.t -> t -> Type.t Span.located

  val find_opt : Id.t -> t -> Type.t Span.located option

  val choose : t -> Id.t * (Type.t Span.located)

  val choose_opt : t -> (Id.t * (Type.t Span.located)) option

  val iter : (Id.t -> Type.t Span.located -> unit) -> t -> unit

  val values : t -> Type.t Span.located list
end

module Make (Id : Set.OrderedType) (T : sig type t end) : S with module Id = Id and module Type = T
