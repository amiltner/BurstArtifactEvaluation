module type CLASS = sig
  type t

  val equal: t -> t -> bool

  val union: t -> t -> t
end

module type S = sig
  type elt

	type repr

  type t

  type factory = elt -> repr

  val create: ?size:int -> unit -> t

  val find: ?default:factory -> elt -> t -> repr

  val find_opt: ?default:factory -> elt -> t -> repr option

  val union: ?default:factory -> ?hook:(repr -> repr -> unit) -> elt -> elt -> t -> t
  (* hook is triggered only if both elements are not in the same class. *)
end

module Make (E: HashTable.HashedType) (C: CLASS) : S with type elt = E.t and type repr = C.t
