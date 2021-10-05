open Codemap

module type S = sig
  module Id: Set.OrderedType
  module Type: sig type t end
  type t
  exception AlreadyDefined of Span.t
  val empty : t
  val mem : Id.t -> t -> bool
  val add : Id.t -> Type.t Span.located -> t -> t
  val find : Id.t -> t -> Type.t Span.located
  val find_opt : Id.t -> t -> Type.t Span.located option
  val choose : t -> Id.t * (Type.t Span.located)
  val choose_opt : t -> (Id.t * (Type.t Span.located)) option
  val iter : (Id.t -> Type.t Span.located -> unit) -> t -> unit
  val values : t -> Type.t Span.located list
end

module Make (Id : Set.OrderedType) (T : sig type t end) = struct
  module Id = Id
  module Type = T
  module IdMap = Map.Make (Id)

  exception AlreadyDefined of Span.t

  type t = Type.t Span.located IdMap.t

  let empty = IdMap.empty

  let mem = IdMap.mem

  let add id e d =
    match IdMap.find_opt id d with
    | Some (_, span) -> raise (AlreadyDefined span)
    | None -> IdMap.add id e d

  let find = IdMap.find

  let find_opt = IdMap.find_opt

  let choose = IdMap.choose

  let choose_opt = IdMap.choose_opt

  let iter = IdMap.iter

  let values t = List.map (fun (_, v) -> v) (IdMap.bindings t)
end
