let eq = (=)
let neq = (<>)

module MyRope = Rope
open Core
open Consts
open Printf
open Lang
open Sigma
open Gamma
open Refine
module Rope = MyRope

(***** Type definitions {{{ *****)

(* rtree: A single node of a refinement tree.                                             *)
type rtree =
  { t                 : typ               (* Goal type that we wish to generate.          *)
  ; mutable sz        : int               (* Size of the refinement tree.                 *)
  ; g                 : Gamma.t           (* Names that are in scope.                     *)
  ; worlds            : world list        (* Example worlds to which this rtree conforms. *)
  ; mutable timed_out : bool              (* Whether the generation process has timed out.*)
  ; mutable es        : exp list          (* Expressions that have been generated so far. *)
  ; refinements       : rnode list        (* Generated using IRefine rules.               *)
  ; mutable matches   : (rmatch list) option  (* Generated using IRefine-match rule.      *)
  ; mutable scrutinee_size : int          (* The size of scrutinees for matches.          *)
  }

and rnode =
  | SAbs   of id * arg * typ * rtree      (* IRefine-Fix.                                 *)
  | SCtor  of id * rtree                  (* IRefine-Ctor.                                *)
  | STuple of rtree list                  (* IRefine-Tuple.                               *)
  | SRcd   of rtree record                (* IRefine-Record.                              *)
  | SUnit                                 (* IRefine-Unit.                                *)

and rmatch = exp *                        (* The match scrutinee.                         *)
             (pat * rtree) list            (* The branches of the match statement.         *)
             * (int list) list

(* rtree_size: Determines the size of an rtree, which is defined as the number of rtrees  *)
(*             contained in this and child trees.                                         *)
let rec rtree_size (t:rtree) : int =
  let rnode_size n =
    match n with
    | SAbs (_, _, _, t) -> rtree_size t
    | SCtor (_, t)      -> rtree_size t
    | STuple ts -> List.fold_left ~f:(fun acc t -> rtree_size t + acc) ~init:0 ts
    | SRcd ts -> List.fold_left ~f:(fun acc (_,t) -> rtree_size t + acc) ~init:0 ts
    | SUnit -> 0
  in
  let match_size ((_, ls,_) : rmatch) =
      List.fold_left ~f:(fun acc t -> acc + rtree_size t) ~init:0 (List.map ~f:snd ls)
  in
  let matches_size = function
    | None    -> 0
    | Some ms -> List.fold_left ~f:(fun acc m -> acc + match_size m) ~init:0 ms
  in
  List.fold_left
    ~f:(fun acc n -> acc + rnode_size n)
    ~init:(1 + matches_size t.matches)
    t.refinements

(***** }}} *****)

(***** Pretty printing {{{ *****)

type pretty_line = int * string

let print_whitespace (n:int) = (String.make (n + 1) '*') ^ "   "
let pretty_lines (lines:pretty_line list) : string list =
  List.map ~f:(fun (n, s) -> print_whitespace n ^ s) lines

let rec stringify (ss:string list) : string =
  match ss with
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ "\n" ^ stringify ss

let stringify_rtree_matches (t:rtree) : string =
  match t.matches with
  | None    -> "growable"
  | Some ls -> sprintf "scrutinee_size = %d, #/matches = %d" t.scrutinee_size (List.length ls)

let rec build_lines_rtree (k:int) (t:rtree) : pretty_line list =
  let childlines   = List.concat_map ~f:(build_lines_rnode k t.t) t.refinements in
  let matchlines   = build_lines_matches k t.t t.matches  in
  (k, sprintf "* :: %s [E-size = %d, timed_out = %b, exp_count = %d, %s]"
    (Pp.pp_typ t.t) t.sz t.timed_out
    (List.length t.es) (stringify_rtree_matches t)) :: (matchlines @ childlines)

and build_lines_match (k:int) (tt:typ) ((e, bs,_):rmatch) : pretty_line list =
    let s = Printf.sprintf "match %s :: %s" (Pp.pp_exp e) (Pp.pp_typ tt) in
    (k, s) :: List.concat_map ~f:(fun (p, t) ->
      let s = sprintf "| %s ->" (Pp.pp_pat p) in
      (k+1, s) :: build_lines_rtree (k+2) t) bs

and build_lines_matches k t ms = match ms with
  | None -> []
  | Some ms -> List.concat_map ~f:(build_lines_match k t) ms

and build_lines_rnode (k:int) (tt:typ) (n:rnode) : pretty_line list =
  match n with
  | SAbs (f, (x, t1), t2, t) ->
      let s = Printf.sprintf "fix %s (%s:%s) : %s :: %s" f x (Pp.pp_typ t1) (Pp.pp_typ t2) (Pp.pp_typ tt) in
      (k, s) :: build_lines_rtree (k+1) t
  | SCtor (c, t) ->
      let s = Printf.sprintf "ctor %s :: %s" c (Pp.pp_typ tt) in
      (k, s) :: (build_lines_rtree (k+1) t)
  | STuple ts ->
      let s = Printf.sprintf "tuple :: %s" (Pp.pp_typ tt) in
      (k, s) :: List.concat_map ~f:(build_lines_rtree (k+1)) ts
  | SRcd ts ->
      let s = Printf.sprintf "record :: %s" (Pp.pp_typ tt) in
      (k, s) :: List.concat_map ~f:(fun (_,t) -> build_lines_rtree (k+1) t) ts
  | SUnit ->
      let s = Printf.sprintf "unit :: %s" (Pp.pp_typ tt) in
      [(k, s)]

let pp_rtree t = build_lines_rtree 0 t |> pretty_lines |> stringify

(***** }}} *****)

(***** Refinement tree construction {{{ *****)

type synth_branch  = id * pat * Gamma.t * world list
type eval_val      = {
    scrut_ctor  : id;            (* The constructor that the scrutinee evaluates to.    *)
    scrut_val   : value;         (* The value that the scrutinee evalutes to (no ctor). *)
    env:env;                     (* The environment for a particular world.             *)
    goal:value;                  (* The expected outcome of the larger match statement. *)
    num: int;
}

(* Creates a rtree for the given synthesis problem. *)
let rec create_rtree (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                     (worlds:world list) (matches_count:int) : rtree =
  { t         = t
  ; sz        = 1
  ; g         = g
  ; worlds    = worlds
  ; es        = []
  ; timed_out = false
  ; matches   = if matches_count <= 0 then None
                else Some (create_matches s g env t worlds matches_count 1 !scrutinee_size_lim)
  ; refinements  = create_non_matches s g env t worlds matches_count
  ; scrutinee_size = !scrutinee_size_lim
  }

(***** Create refinement tree match statements {{{ *****)

(* Distributes the examples according to the constructors that e evaluates to.
 * For each examles (env, v), if env(v) ~~> C (...), then (env, v) is filed
 * under the C bucket. *)
and distribute_constraints (s:Sigma.t) (g:Gamma.t) (e:exp) (evs:eval_val list) : synth_branch list  * (int list list) =
  if List.length evs = 0 then ([],[]) else
  let dt = Sigma.ctor_datatype ((List.hd_exn evs).scrut_ctor) s in
  Sigma.ctors dt s |> List.map ~f:begin fun (c, (c_typ, _)) ->
    (* Generate a pattern.                                                                *)
    let (p_opt, g) = match c_typ with        (* Don't create a pattern at unit type.      *)
      | TUnit -> (None, g)
      | _ -> let (p, g) = Gamma.insert_pattern c_typ g in (Some p, g)
    in
    (* Mark pattern variables as decreasing if possible.                                  *)
    let (p_opt, g) = match (p_opt, Gamma.fun_of_arg e g) with
      | (None, _) | (_, None) -> (p_opt, g)
      | (Some p, Some f) ->
        let g  = List.fold_left
              ~f:(fun g x -> Gamma.mark_as_dec_arg_of_fun x f g)
              ~init:g
              (extract_ids_from_pattern p)
        in
        (p_opt, g)
    in
    let pattern_env v = match p_opt with
      | None -> []
      | Some p -> Refine.pattern_to_env p v
    in
    let (worlds_for_c,distribution) =
      List.filter ~f:(fun ev -> eq c ev.scrut_ctor) evs |>
      List.map ~f:(fun ev ->
          (((pattern_env ev.scrut_val) @ ev.env, ev.goal), ev.num)
        )
    |> List.unzip
    in
    ((c, (c, p_opt), g, worlds_for_c), List.sort ~compare:Int.compare distribution)
  end
  |> List.unzip
  |> (fun (ev,dists) -> (ev,List.sort ~compare:(List.compare Int.compare) dists))

(* Creates a single match for the given synthesis problem and scrutinee expression. *)
(* If evaluation of the potential scrutinee results in no example generated         *)
(* (because all examples resulted in bad pattern matches), then reject this         *)
(* scrutinee immediately.                                                           *)
and create_match (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                     (_:world list) (matches:int) ((e, evs):exp * (eval_val list))
                     : rmatch option =
    (* Returns true if the given synth_branches are an adequate distribution of the       *)
    (* examples as determined by {distribute_constraints}.                                *)
    (* Every branch must have one example.                                                *)
    let is_adequate_distribution (bs:synth_branch list) : bool =
      let count = List.fold_left
        ~f:(fun acc (_, _, _, l) -> if List.length l > 0 then acc + 1 else acc)
        ~init:0 bs
      in
      count = List.length bs
    in
    if List.length evs = 0 then None else
      let (branches,dist) = distribute_constraints s g e evs in
    if not (is_adequate_distribution branches) then None else
    let trees = List.map ~f:(fun (_, p, g, ws) ->
      (p, create_rtree s g env t ws (matches-1))) branches
    in
  Some (e, trees,dist) 

(* Creates match nodes for the given synthesis problem.                                   *)
and create_matches (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                   (ws:world list) (matches:int)
                   (scrutinee_min:int) (scrutinee_max:int) : rmatch list =
    match t with
    | TArr _ -> []
    | _      ->
      (* Evaluate a scrutinee candidate {e} to constructors in each example world,        *)
      (* creating a corresponding eval_val for each world.                                *)
      let eval_scrutinee (ws:world list) (e:exp) : exp * (eval_val list) =
          let eval_fn i (env', goal) =
            try
              match Eval.eval (env @ env') e with
              | VCtor (c, v) -> Some {scrut_ctor = c; scrut_val = v; env = env'; goal = goal; num= i}
              | _ -> failwith "(eval_scrutinee) non-constructor encountered"
            with
              Eval.Eval_error _ -> None
          in
          (e, List.filter_mapi ~f:eval_fn ws)
      in

      (* Generate scrutinees of size {size} of any type.                                  *)
      let gen_scrutinees size =
          (* Generate scrutinees of size {size} and type {t}.                             *)
          let gen_scrutinees_of_type t' =
              let met = Gen.gen_metric size 1 in
              let scrut_exps = Gen.gen_eexp Timeout.unlimited s g t' met in
              let scrut_vals = Rope.map ~f:(eval_scrutinee ws) scrut_exps in
              let ms = Rope.map ~f:(create_match s g env t ws matches) scrut_vals in
              Rope.filter_map ~f:Fn.id ms
          in
          Rope.concat_map ~f:gen_scrutinees_of_type (Rope.of_list (Sigma.types s))
      in
      Util.rangen scrutinee_min scrutinee_max |>
      Rope.of_list                            |>
      Rope.concat_map ~f:gen_scrutinees       |>
      Rope.to_list

(***** }}} *****)

(***** Create refinement tree non-match statements {{{ *****)

(* Creates (type-directed) rtree nodes for the given synthesis problem.                   *)
and create_non_matches (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ) (vs:world list)
                       (matches:int) : rnode list =
  match t with
  | TUnit -> [SUnit]

  (* Refine constructors *)
  | TBase _ ->
      let ctors_match v1 v2 = match (v1, v2) with
        | (VCtor (c1, _), VCtor (c2, _)) -> eq c1 c2
        | _ -> false
      in
      let extract_ctor v = match v with
        | VCtor (c, _) -> c
        | _ -> internal_error "extract_ctor" (sprintf "ctor expected: %s" (Pp.pp_value v))
      in
      let values = List.map ~f:snd vs in
      if List.length values > 0 && Util.all_eq ctors_match values then
        let c       = extract_ctor (List.hd_exn values) in
        let (c_typ, _) = Sigma.lookup_ctor_exn c s in
        [SCtor (c, create_rtree s g env c_typ (Refine.ctor vs) matches)]
      else []

  (* Refine functions *)
  | TArr (t1, t2) ->
    let f  = Gamma.fresh_id (gen_var_base t ) g in
    let x  = Gamma.fresh_id (gen_var_base t1) (Gamma.insert f t g) in
    let g  = Gamma.insert f t g                 |>
             Gamma.insert x t1                  |>
             Gamma.mark_as_rec_fun_with_arg f x |>
             Gamma.mark_as_arg_of_fun x f
    in
    let vs = Refine.func f x vs in
    [SAbs (f, (x, t1), t2, create_rtree s g env t2 vs matches)]

  (* Refine tuples *)
  | TTuple ts ->
      let tuples_match v1 v2 = match (v1, v2) with
        | (VTuple vs1, VTuple vs2) -> (List.length vs1) = (List.length vs2) &&
                                      (List.length vs1) = (List.length ts)
        | _ -> false
      in
      let values = List.map ~f:snd vs in
      if List.length values > 0 && Util.all_eq tuples_match values then
        let sub_vs = List.zip_exn ts (Refine.tuple vs) in
        let trees =
          List.map ~f:(fun (t, vs) -> create_rtree s g env t vs matches) sub_vs
        in
        [STuple trees]
      else []

  (* Refine records *)
  | TRcd ts ->
      let tlabels = Util.fst_assoc ts in
      let values = Util.snd_assoc vs in
      let labels_match = List.for_all values ~f:(fun v ->
        begin match v with
          | VRcd vs' -> eq (Util.fst_assoc vs') tlabels
          | _ -> false
        end) in
      if (List.length values <= 0) || (not labels_match) then [] else
        let sub_vs = Util.zip_with_keys ts (Refine.record vs) in
        let trees = List.map sub_vs ~f:(fun (l, (t, vs)) ->
          (l, create_rtree s g env t vs matches)) in
        [SRcd trees]

(***** }}} *****)

(* Grows the given refinement tree by one level of matches. *)
let rec grow_matches (s:Sigma.t) (env:env) (t:rtree) =
  begin match t.matches with
  | None ->
    if List.length t.es = 0 then
      let ms = create_matches s t.g env t.t t.worlds 1 1 !scrutinee_size_lim in
      (*print_endline ("before" ^ (string_of_int (List.length ms)));
      let ms =
        Util.core_deduper
          ~compare:(fun (_,_,il1) (_,_,il2) ->
              List.compare
                (List.compare Int.compare)
                il1
                il2)
          ~to_size:(fun (e,_,_) -> size e)
          ms
      in
        print_endline ("after" ^ (string_of_int (List.length ms)));*)
      t.matches <- Some (ms);
      t.scrutinee_size <- !scrutinee_size_lim
  | Some ms ->
      List.iter
        ~f:(fun (_, bs, _) -> List.iter ~f:(fun (_, t) -> grow_matches s env t) bs)
        ms
  end;
  List.iter ~f:(grow_matches_rnode s env) t.refinements

and grow_matches_rnode (s:Sigma.t) (env:env) (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> grow_matches s env t
  | SCtor (_, t) -> grow_matches s env t
  | STuple ts -> List.iter ~f:(grow_matches s env) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> grow_matches s env t) ts
  | SUnit -> ()

(* Grows the given refinement tree by expanding the match scrutinees by
 * size k. *)
let rec grow_scrutinees (s:Sigma.t) (env:env) (k:int) (t:rtree) =
  begin match t.matches with
  | None -> ()
  | Some ms ->
      let min = t.scrutinee_size+1 in
      let max = t.scrutinee_size+k in
      let ms' = create_matches s t.g env t.t t.worlds 1 min max in
      let ms =
        (*Util.core_deduper
          ~compare:(fun (_,_,il1) (_,_,il2) ->
              List.compare
                (List.compare Int.compare)
                il1
                il2)
          ~to_size:(fun (e,_,_) -> size e)*)
          (ms@ms')
      in
      t.matches <- Some (ms);
      t.scrutinee_size <- max;
      List.iter
        ~f:(fun (_, bs, _) ->
          List.iter ~f:(fun (_, t) -> grow_scrutinees s env k t) bs)
        ms
  end;
  List.iter ~f:(grow_scrutinees_rnode s env k) t.refinements

and grow_scrutinees_rnode (s:Sigma.t) (env:env) (k:int) (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> grow_scrutinees s env k t
  | SCtor (_, t) -> grow_scrutinees s env k t
  | STuple ts -> List.iter ~f:(grow_scrutinees s env k) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> grow_scrutinees s env k t) ts
  | SUnit -> ()

(***** }}} *****)

(***** Refinement tree manipulation {{{ *****)
let check_exp (e:exp) (env_global:env) (env_local:env) (v:value) : bool =
  try eq v (Timing.record
            ~label:"update_exps::eval"
            ~action:(fun _ -> Eval.eval (env_local @ env_global) e))
  with Eval.Eval_error msg ->
    if not !incomplete_constraints_flag then begin
      incomplete_constraints_flag := true;
      eprintf "Warning: incomplete constraint set given\n%s\n" msg;
    end; false

let satisfies_example (e:exp) (env_global:env) (ws:world list) : bool =
  List.for_all ~f:(fun (env_local, w) -> check_exp e env_global env_local w) ws

(***** update_exps: e-guesses at each node in the rtree {{{ *****)

let rec update_exps ?short_circuit:(sc = true) (timeout:float)
                    (s:Sigma.t) (env:env) (t:rtree) =
  let do_if_no_exp (f:unit -> unit) =
    if not sc || List.length t.es = 0 then f ()
  in
  (* Update this node's expressions... *)
  do_if_no_exp (fun _ ->
    (* NOTE: only generate expressions at this node if it is at base type... *)
    begin match t.t with
    | TArr _ | TUnit | TTuple _ | TRcd _ -> ()
    | TBase _ ->
      (* ...and we have not exceeded the max eguess size nor timed out yet. *)
      if (not t.timed_out) && t.sz <= !max_eguess_size then try
        Timing.record
          ~label:"update_exps::gen"
          ~action:begin fun _ ->
            Gen.gen_eexp
              (Timeout.create timeout) s t.g t.t (Gen.gen_metric t.sz 1)
          end
        |> Rope.to_list
        |> List.map ~f:(fun e -> (size e,e))
        |> List.sort ~compare:(fun (i1,_) (i2,_) -> Int.compare i1 i2)
        |> List.map ~f:snd
        |>
        List.iter ~f:begin fun e ->
            (* TODO: probably want to short-circuit walking through gen_eexp
             * results as well... *)
            if sc then
              match t.es with
              | [] -> if satisfies_example e env t.worlds then t.es <- [e]
              | _ :: _ -> ()
            else
              if satisfies_example e env t.worlds then t.es <- e :: t.es
            end;
        t.sz <- t.sz + 1
      with
        Timeout.Timeout_exception -> begin
          do_if_verbose (fun _ ->
            Printf.printf
              "Timeout occurred while guessing, size = %d\n%!" t.sz);
          t.timed_out <- true
        end

    end);
  (* ...if we didn't update this tree's exp then recursively update it's
   * children. *)
  do_if_no_exp (fun _ -> begin
    update_exps_matches ~short_circuit:sc timeout s env t.matches;
    List.iter ~f:(update_exps_node ~short_circuit:sc timeout s env)
      t.refinements;
  end)

and update_exps_matches ?short_circuit:(sc = true) (timeout:float) (s:Sigma.t)
                        (env:env) (mopt:rmatch list option) =
  match mopt with
  | None -> ()
  | Some ms ->
      List.iter ~f:(update_exps_rmatch ~short_circuit:sc timeout s env) ms

and update_exps_rmatch ?short_circuit:(sc = true) (timeout:float)
                       (s:Sigma.t) (env:env) (m:rmatch) =
  let (_, bs, _) = m in
  List.iter ~f:(fun (_, t) -> update_exps ~short_circuit:sc timeout s env t) bs

and update_exps_node ?short_circuit:(sc = true) (timeout:float)
                     (s:Sigma.t) (env:env) (n:rnode) =
  begin match n with
  | SAbs (_, _, _, t) -> update_exps ~short_circuit:sc timeout s env t
  | SCtor (_, t) -> update_exps ~short_circuit:sc timeout s env t
  | STuple ts -> List.iter ~f:(update_exps ~short_circuit:sc timeout s env) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> update_exps ~short_circuit:sc timeout s env t) ts
  | SUnit -> ()
  end

(***** }}} *****)

(***** reset_timeouts: resets the timeout flag in the rtree {{{ *****)

let rec reset_timeouts (t:rtree) = begin
  t.timed_out <- false;
  match t.matches with
  | None -> ()
  | Some ms -> begin
    List.iter ~f:(fun (_, bs, _) ->
      List.iter ~f:(fun (_, t) -> reset_timeouts t) bs) ms
    end;
  List.iter ~f:reset_timeouts_refinements t.refinements
end

and reset_timeouts_refinements (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> reset_timeouts t
  | SCtor (_, t) -> reset_timeouts t
  | STuple ts -> List.iter ~f:reset_timeouts ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> reset_timeouts t) ts
  | SUnit -> ()

(***** }}} *****)

(***** propogate_exps: tries to construct exps from rtree sub-children {{{ *****)

let rec propogate_exps ?short_circuit:(sc = true) (t:rtree) : exp list =
  if sc && List.length t.es > 0 then
    t.es
  else
    (* NOTE: Prioritize lambdas, matches, and then constructors, in that order. *)
    let es = t.es
      @ (List.filter ~f:(function SAbs _ -> true | _ -> false) t.refinements
        |> List.concat_map ~f:(propogate_exps_node ~short_circuit:sc))
      @ propogate_exps_matches ~short_circuit:sc t.matches
      @ (List.filter ~f:(function SCtor _ -> true | _ -> false) t.refinements
        |> List.concat_map ~f:(propogate_exps_node ~short_circuit:sc))
      @ (List.filter ~f:(function STuple _ -> true | _ -> false) t.refinements
        |> List.concat_map ~f:(propogate_exps_node ~short_circuit:sc))
      @ (List.filter ~f:(function SRcd _ -> true | _ -> false) t.refinements
        |> List.concat_map ~f:(propogate_exps_node ~short_circuit:sc))
      @ (List.filter ~f:(function SUnit -> true | _ -> false) t.refinements
        |> List.concat_map ~f:(propogate_exps_node ~short_circuit:sc))     
    in
      t.es <- es;
      es

and propogate_exps_matches ?short_circuit:(sc = true) (mopt:rmatch list option) : exp list =
  match mopt with
  | None -> []
  | Some ms -> List.concat_map ~f:(propogate_exps_rmatch ~short_circuit:sc) ms

and propogate_exps_rmatch ?short_circuit:(sc = true) (m:rmatch) : exp list =
  let (e, bs, _)  = m in
  let (ps, ts) = List.unzip bs in
  List.map ~f:(propogate_exps ~short_circuit:sc) ts
    |> Util.combinations
    |> List.map ~f:(fun es -> EMatch (e, List.zip_exn ps es))

and propogate_exps_node ?short_circuit:(sc = true) (n:rnode) : exp list =
  match n with
  | SUnit -> [EUnit]

  | SAbs (f, x, ty, t) ->
      List.map ~f:(fun e -> EFix (f, x, ty, e)) (propogate_exps ~short_circuit:sc t)

  | SCtor (c, t) ->
      propogate_exps ~short_circuit:sc t |> List.map ~f:(fun e -> ECtor (c, e))

  | STuple ts ->
      List.map ~f:(propogate_exps ~short_circuit:sc) ts
        |> Util.combinations
        |> List.map ~f:(fun es -> ETuple es)

  | SRcd ts ->
      List.map ~f:(fun (l,t) ->
        List.map ~f:(fun e -> (l,e)) (propogate_exps ~short_circuit:sc t)) ts
        |> Util.combinations
        |> List.map ~f:(fun es -> ERcd es)

(***** }}} *****)

(***** }}} *****)
