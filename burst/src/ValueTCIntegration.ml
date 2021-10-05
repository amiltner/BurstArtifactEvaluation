open MyStdLib
open Lang

module Derivation =
struct
  type t =
    {
      typ   : Type.t  ;
      value : Value.t ;
      node  : t_node  ;
    }
  and t_node =
    | CtorRule of Id.t * t
    | TupleRule of t list
  [@@deriving eq, hash, ord, show]

  let node (x:t)
    : t_node =
    x.node

  let rec sub_derivations
      (d:t)
    : t list =
    d::
    (begin match (node d) with
       | CtorRule (_,d) -> sub_derivations d
       | TupleRule ds ->
         List.concat_map
           ~f:sub_derivations
           ds
     end)

  let get_type
      (d:t)
    : Type.t =
    d.typ

  let get_value
      (d:t)
    : Value.t =
    d.value
end

let rec tc_val
    (tc:Context.Types.t)
    (v:Value.t)
    (t:Type.t)
  : Derivation.t =
  let mk_derivation n : Derivation.t =
    {
      typ = t;
      value = v;
      node = n;
    }
  in
  begin match Type.node t with
    | Named i ->
      tc_val
        tc
        v
        (Context.find_exn tc i)
    | Mu (i,t') ->
      let t' = Type.replace t' i t in
      tc_val tc v t'
    | Arrow _ -> failwith "hofs not supported"
    | Tuple ts ->
      begin match Value.node v with
        | Tuple vs ->
          let ds =
            List.map2_exn
              ~f:(fun t v ->
                  tc_val
                    tc
                    v
                    t)
              ts
              vs
          in
          mk_derivation (TupleRule ds)
        | _ -> failwith "ill typed"
      end
    | Variant branches ->
      begin match Value.node v with
        | Ctor (i,v) ->
          let t =
            List.Assoc.find_exn
              ~equal:Id.equal
              branches
              i
          in
          let d =
            tc_val
              tc
              v
              t
          in
          mk_derivation (CtorRule (i,d))
        | _ -> failwith "ill typed"
      end
  end
