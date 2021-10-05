open Core
open Lang
open Printf

module type Refine_Sig = sig
    (* Refine function examples: function name -> argument name -> examples. *)
    val func  : id -> id -> world list -> world list

    (* Refine tuple examples: produces a list of lists of examples, where the *)
    (* kth list is the set of examples for the kth subexpression in the tuple *)
    val tuple : world list -> world list list

    (* Refine record examples: produces a labelled list of examples, where a  *)
    (* list with label l is the set of examples for the subexpression with    *)
    (* label l in the record                                                  *)
    val record : world list -> (world list) record

    (* Refine constructor examples: Assumes that all examples have the same  *)
    (* constructor.  Retrieves the bodies of the examples.                   *)
    val ctor  : world list -> world list

    (* Create an environment out of a pattern and a scrutinee value.         *)
    val pattern_to_env : pattern -> value -> env
end

module Refine : Refine_Sig = struct
    let func (f:id) (x:id) (vs:world list) : world list =
      let map_fn (env', v) = match v with
        | VPFun ios -> List.map ~f:(fun (v1, v2) -> ((f, v) :: (x, v1) :: env', v2)) ios
        | _         -> failwith "(Refine.func) non-IO example in goal position"
      in
      List.concat_map ~f:map_fn vs

    let tuple (vs:world list) : world list list =
      let arity = match List.hd_exn vs with
        | (_, VTuple ts) -> List.length ts
        | _               -> failwith "(Refine.tuple) non-tuple example in goal position"
      in
      let map_fn n = List.fold_left
        ~f:(fun acc (env', v) ->
            match v with
            | VTuple vs -> (env', List.nth_exn vs n) :: acc
            | _         -> failwith "(Refine.tuple) non-tuple example in goal position")
        ~init:[]
        vs
      in
      List.map ~f:map_fn (Util.range arity)

    let record (vs:world list) : (world list) record =
      List.map ~f:(fun (env, v) ->
        begin match v with
        | VRcd rvs -> List.map ~f:(fun (l,v') -> (l,(env,v'))) rvs
        | _ -> failwith "(Refine.record) non-record example in goal position"
        end
      ) vs |> Util.combine_assoc

    let ctor (vs:world list) : world list =
      List.map ~f:(fun (env, v) ->
        match v with
        | VCtor (_, v') -> (env, v')
        | _ -> failwith "(Refine.ctor) constructor expected")
      vs

    let rec pattern_to_env (p:pattern) (scrut_v:value) : env =
      match (p, scrut_v) with
        | (PWildcard, _) -> []
        | (PVar x,    v) -> [(x, v)]
        | (PTuple ps, VTuple vs) -> List.zip_exn ps vs |> List.concat_map
            ~f:(fun (p,v) -> pattern_to_env p v)
        | (PRcd ps, VRcd vs) -> Util.zip_without_keys ps vs |> List.concat_map
            ~f:(fun (p,v) -> pattern_to_env p v)
        | _ -> failwith (sprintf "Pattern %s does not match value %s" 
                         (Pp.pp_pattern p) (Pp.pp_value scrut_v))

end
