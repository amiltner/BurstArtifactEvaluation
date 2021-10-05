module type BASE = sig
  type node

  module NodeSet : Set.S with type elt = node

  type t

  val empty : t

  val nodes : t -> NodeSet.t

  val successors : t -> node -> NodeSet.t

  val fold : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a

  val add : node -> t -> t

  val connect : node -> node -> t -> t

  val scheduling : t -> node list
end

module type S = sig
  include BASE

  val components_graph : t -> (module BASE with type node = NodeSet.t and type t = 'a) -> 'a
end

module Make (Node : HashTable.HashedType) :
  S with type node = Node.t
