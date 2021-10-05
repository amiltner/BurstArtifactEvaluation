open MyStdLib
open Lang

module T = struct
  include Map.Make(Id)
  include Provide_bin_io(Id)
  include Provide_hash(Id)
end

include T

let set_multiple
    (c:'a T.t)
    (vs:(Id.t * 'a) list)
  : 'a T.t =
  List.fold
    ~f:(fun acc (key,data) -> set acc ~key ~data)
    ~init:c
    vs

module Exprs = struct
  type key = T.Key.t
  type value = Type.t

  type t = Type.t T.t
  [@@deriving eq, hash, ord]
end

module Types = struct
  type key = T.Key.t
  type value = Type.t

  type t = Type.t T.t
  [@@deriving eq, hash, ord]
end

module Variants = struct
  type key = T.Key.t
  type value = (Id.t * Type.t) list

  type t = (Id.t * Type.t) list T.t
  [@@deriving eq, hash, ord]
end

let get_foldable_t (tc:Types.t) (fold_completion:Type.t) : Type.t =
  let rec type_to_folded_type_internal
      (i:Id.t)
      (t:Type.t)
    : Type.t =
    begin match Type.node t with
      | Named i' ->
        if Id.equal i i' then
          fold_completion
        else
          t
      | Tuple ts ->
        Type.mk_tuple (List.map ~f:(type_to_folded_type_internal i) ts)
      | Variant branches ->
        Type.mk_variant
          (List.map
             ~f:(fun (b,t) ->
                 (Id.mk_prime b
                 ,type_to_folded_type_internal i t))
             branches)
      | Arrow _ | Mu _ -> t
    end
  in
  let t = find_exn tc (Id.create "t") in
  let tv = Type.destruct_id_exn t in
  let t = find_exn tc tv in
  let ito = Type.destruct_mu t in
  begin match ito with
    | None -> t
    | Some (i,t) ->
      type_to_folded_type_internal i t
  end

type t =
  {
    ec : Exprs.t ;
    tc : Types.t ;
    vc : Variants.t ;
    full_ec : Exprs.t ;
    full_tc : Types.t ;
    full_vc : Variants.t ;
    evals : (Id.t * Expr.t) list ;
    full_evals : (Id.t * Expr.t) list ;
  }
