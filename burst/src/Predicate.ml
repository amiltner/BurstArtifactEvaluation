open MyStdLib
open Lang

type t = Value.t
[@@deriving eq, hash, ord, show]

let top = Value.mk_wildcard

let rec conjunct
    (p1:t)
    (p2:t)
  : t option =
  begin match (Value.node p1,Value.node p2) with
    | (Wildcard,_) -> Some p2
    | (_,Wildcard) -> Some p1
    | (Func _, Func _) ->
      if Value.equal p1 p2 then
        Some p1
      else
        None
    | (Ctor (i1,v1),Ctor (i2,v2)) ->
      if Id.equal i1 i2 then
        Option.map
          ~f:(Value.mk_ctor i1)
          (conjunct v1 v2)
      else
        None
    | (Tuple vs1, Tuple vs2) ->
      begin match List.map2 ~f:conjunct vs1 vs2 with
        | Ok vos ->
          Option.map
            ~f:Value.mk_tuple
            (distribute_option vos)
        | Unequal_lengths ->
          None
      end
    | _ ->
      None
  end

let conjunct_exn
    (p1:t)
    (p2:t)
  : t =
  Option.value_exn (conjunct p1 p2)

let rec (=>)
    (p1:t)
    (p2:t)
  : bool =
  begin match (Value.node p1,Value.node p2) with
    | (_,Wildcard) -> true
    | (Wildcard,_) -> false
    | (Func _, Func _) ->
      if Value.equal p1 p2 then
        true
      else
        false
    | (Ctor (i1,v1),Ctor (i2,v2)) ->
      Id.equal i1 i2 && v1 => v2
    | (Tuple vs1, Tuple vs2) ->
      begin match List.for_all2 ~f:(=>) vs1 vs2 with
        | Ok b -> b
        | Unequal_lengths ->
          false
      end
    | _ ->
      false
  end


let implied_by_strict_functional_subvalue ~(break:t -> bool) (e1:t) (e2:t) : bool =
  List.exists ~f:(fun v -> v => e1) (Value.strict_functional_subvalues ~break e2)

let is_concrete
  : t -> bool =
  Value.fold
    ~func_f:(fun _ _ -> true)
    ~ctor_f:(fun _ b -> b)
    ~tuple_f:(fun bs -> List.for_all ~f:ident bs)
    ~wildcard_f:false
