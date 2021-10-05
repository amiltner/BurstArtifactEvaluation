open Timbuk

(** Alphabet is a special dictionary dedicated to symbols.
    It includes a formatting function displaying the arity of each symbol. *)
module Make (Id : Set.OrderedType) (Symbol : Symbol.S) : sig
  include module type of Dictionary.Make (Id) (Symbol)

	val print : t -> Format.formatter -> unit
end
