open MyStdLib
open Lang

module TypedAbs =
struct
  type t = Predicate.t list
  [@@deriving eq, hash, ord, show]

  let abstract
      (ps:t)
      (v:Value.t)
    : Predicate.t =
    Predicate.
      (let applies = List.filter ~f:(fun p -> (v => p)) ps in
       fold_on_head_with_default
         ~default:Predicate.top
         ~f:conjunct_exn
         applies)
end

module D = DictOf(Type)(TypedAbs)

type t = D.t
[@@deriving eq, hash, ord, show]

let add
    (a:t)
    (t:Type.t)
    (p:Predicate.t)
  : t =
  let ps =
    begin match D.lookup a t with
      | None -> [Predicate.top]
      | Some ps -> ps
    end
  in
  D.insert a t (List.dedup_and_sort ~compare:Predicate.compare (p::ps))

let rec abstract_list
    (vs:Value.t list)
    (valid:Value.t list -> bool)
  : Value.t list =
  let rec abstract_list_internal
      (processed:Value.t list)
      (remaining:Value.t list)
    : Value.t list =
    begin match remaining with
      | [] -> processed
      | h::remaining ->
        let h = abstract_value h (fun v -> valid (processed@(v::remaining))) in
        abstract_list_internal
          (processed@[h])
          remaining
    end
  in
  abstract_list_internal [] vs
and
  abstract_value
    (v:Value.t)
    (valid:Value.t -> bool)
  : Value.t =
  if Value.equal v Value.unit_ then
    Value.unit_
  else if valid Value.mk_wildcard then
    Value.mk_wildcard
  else
    begin match Value.node v with
      | Func _ -> v
      | Ctor (i,v) ->
        Value.mk_ctor i (abstract_value v (fun v -> valid (Value.mk_ctor i v)))
      | Tuple vs ->
        Value.mk_tuple
          (abstract_list
             vs
             (fun vs -> valid (Value.mk_tuple vs)))
      | Wildcard ->
        Value.mk_wildcard
    end

let abstract
    (a:t)
    (v:Value.t)
    (t:Type.t)
  : Predicate.t =
  let ta =
    D.lookup_default
      ~default:([Predicate.top])
      a
      t
  in
  TypedAbs.abstract ta v

let abstract_final
    ~(out:Value.t)
    ~(pred:Predicate.t -> bool)
  : Predicate.t =
  out (*TODO*)

let init = D.empty
