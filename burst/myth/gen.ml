let eq = (=)

module MyRope = Rope
open Core
open Consts
open Lang
open Gamma
open Sigma
module Rope = MyRope

(***** Term generation metrics {{{ *****)

type metric =
  { size : int
  ; lambdas : int
  }

let gen_metric (size:int) (lambdas:int) : metric =
  { size = size; lambdas = lambdas }

(***** }}} *****)

(***** Memoization Tables {{{ *****)

module GTS : sig
  type t = { g : Gamma.t; t : typ; met : metric }
  val make_key : Gamma.t -> typ -> metric -> t
  include Hashable.S with type t := t
end = struct
  module T = struct
    type t = { g : Gamma.t; t : typ; met : metric }
    let make_key (g:Gamma.t) (t:typ) (met:metric) = { g = g; t = t; met = met }
    let hash k =
      let hash_met met =
        Int.hash met.size lxor Int.hash met.lambdas lxor 7919
      in
        (Gamma.hash k.g) lxor (hash_typ k.t) lxor (hash_met k.met)
    let compare = compare   (* NOTE: use the built-in compare function *)
    let hash_fold_t s k = Hash.fold_int s (hash k)
    let sexp_of_t (_:t) : Sexp.t = failwith "GTS.sexp_of_t unimplemented"
    let t_of_sexp (_:Sexp.t) : t = failwith "GTS.t_of_sexp unimplemented"
  end
  include T
  include Hashable.Make(T)
end

let memo_eexp_tbl     : (GTS.t, exp Rope.t) Hashtbl.t =
  GTS.Table.create ()
let memo_eexp_rel_tbl : (GTS.t, exp Rope.t) Hashtbl.t =
  GTS.Table.create ()
let memo_iexp_tbl     : (GTS.t, exp Rope.t) Hashtbl.t =
  GTS.Table.create ()
let memo_iexp_rel_tbl : (GTS.t, exp Rope.t) Hashtbl.t =
  GTS.Table.create ()

(***** }}} *****)

(***** Term Generation and Synthesis {{{ *****)

let find_in_table (tbl:('a, 'b) Hashtbl.t) (key:'a) : 'b option =
  if !eterm_lookup_tables then
    Hashtbl.find tbl key
  else
    None

let fetch_or_calculate (tbl: ('a, 'b) Hashtbl.t) (key:'a) (f:unit -> 'b) : 'b =
  match find_in_table tbl key with
  | Some ans -> ans
  | None ->
      let ans = f () in begin
        Hashtbl.set tbl ~key ~data:ans; ans
      end

(* Projection can either be ints (for tuples) or labels (for records). *)
(* We use this type to factor projection generation code together.     *)
type proj = | TupleProj of int
            | RcdProj of label

type rel_gen_sig = Sigma.t -> Gamma.t -> (exp * typ)
                -> typ -> metric -> exp Rope.t

let rec gen_eexp (tmo:Timeout.t) (s:Sigma.t)
                 (g:Gamma.t) (t:typ) (met:metric) : exp Rope.t =
  Timeout.check_timeout tmo;
  if met.size <= 0 then Rope.empty else
  fetch_or_calculate memo_eexp_tbl (GTS.make_key g t met)
    begin fun _ ->
      match Gamma.peel g with
      | None -> Rope.empty
      | Some ((erel, trel), g) ->
        let weakened = gen_eexp tmo s g t met in
        let relevant = gen_eexp_rel tmo s (erel, trel) g t met in
        Rope.concat weakened relevant
    end

and gen_eexp_rel (tmo:Timeout.t) (s:Sigma.t)
                 ((erel, trel):exp * typ)
                 (g:Gamma.t) (t:typ) (met:metric) : exp Rope.t =
  Timeout.check_timeout tmo;
  if met.size <= 0 then Rope.empty else
  fetch_or_calculate memo_eexp_rel_tbl
    (GTS.make_key (Gamma.insert_exp erel trel g) t met)
    begin fun _ ->
      if met.size = 1 && eq trel t then
        Rope.cons erel Rope.empty
      else
        Rope.concat (gen_eexp_rel_app  tmo s (erel, trel) g t met)
                    (gen_eexp_rel_proj tmo s (erel, trel) g t met)
    end

(* The only case when we eguess projection is when we project on an application. *)
and gen_eexp_rel_proj (tmo:Timeout.t) (s:Sigma.t)
                      ((erel, trel):exp * typ)
                      (g:Gamma.t) (goal:typ) (met:metric) : exp Rope.t =

  (* Does a product type contain our goal type? *)
  let rec contains_goal (t:typ) =
    if eq t goal then true else
    begin match t with
    | TTuple ts -> Util.one_true contains_goal ts
    | TRcd ts -> Util.one_true contains_goal (Util.snd_assoc ts)
    | _ -> false
    end
  in

  (* What are possible paths of projection that will lead to the goal type? *)
  let rec path_to_goal_type (t:typ) (path:proj list) : proj list list =
    if eq t goal then [path] else
    begin match t with
    | TTuple ts ->
      List.concat_mapi ~f:(fun i t -> path_to_goal_type t ((TupleProj (i + 1)) :: path)) ts
    | TRcd ts ->
      List.concat_map ~f:(fun (l,t) -> path_to_goal_type t ((RcdProj l) :: path)) ts
    | _ -> []
    end
  in

  (* Convert a path into chain of projection on {e}. *)
  let rec project_path_on_exp (path:proj list) (e:exp) : exp =
    begin match path with
    | [] -> e
    | (TupleProj i) :: path' -> EProj (i, project_path_on_exp path' e)
    | (RcdProj l) :: path' -> ERcdProj (l, project_path_on_exp path' e)
    end
  in

  (* Is t an arrow type that produces a product type that contains our goal type? *)
  let rec arrow_produces_product_type_with_goal (t:typ) : typ option =
    begin match t with
    | TArr (_, TTuple ts) ->
      if contains_goal (TTuple ts) then Some (TTuple ts) else None
    | TArr (_, TRcd ts) ->
      if contains_goal (TRcd ts) then Some (TRcd ts) else None
    | TArr (_, t2) -> arrow_produces_product_type_with_goal t2
    | _ -> None
    end
  in

  (* Find the arrow-result types that can be projected on to produce our goal. *)
  let types = Gamma.insert_exp erel trel g
              |> Gamma.types
              |> (List.dedup_and_sort ~compare)
              |> List.filter_map ~f:arrow_produces_product_type_with_goal
  in

  (* Generate applications and project on them as necessary. *)
  Rope.concat_map ~f:begin fun t ->
      (* A list of functions that project on expressions to get to the goal type.*)
      let path_fns = path_to_goal_type t [] |> List.map ~f:project_path_on_exp in

      (* Generate applications and project on them with the path functions. *)
      gen_eexp_rel_app tmo s (erel, trel) g t met
      |> Rope.concat_map ~f:(fun e -> List.map ~f:(fun f -> f e) path_fns |> Rope.of_list)
  end (Rope.of_list types)

and gen_eexp_rel_app (tmo:Timeout.t) (s:Sigma.t)
                     ((erel, trel):exp * typ)
                     (g:Gamma.t) (t:typ) (met:metric) : exp Rope.t =

  (***** gen_eexp_rel_app helpers {{{ *****)

  (* Extract the producer components of this type.  For arrows this is the
   * left-hand type of the arrow. *)
  let rec extract_producer (t:typ) (u:typ) : typ option =
    match u with
    | TArr (_, t2) -> if eq t2 t then Some u else extract_producer t t2
    | TBase _ -> None
    | TTuple _ -> None
    | TRcd _ -> None
    | TUnit -> None
  in

  (* Generates applications using the two exp-generations functions to create
   * the left- and right-hand sides of the applications, respectively. *)
  let gen_apps (ts:typ list) (met:metric)
               (e1s_fn:rel_gen_sig) (e2s_fn:rel_gen_sig) =
    ts |> Rope.of_list |> Rope.concat_map ~f:(fun t ->
      begin match t with
      | TArr (t1, _) ->
          Util.partitions (met.size - 1) 2
            |> Rope.of_list
            |> Rope.concat_map ~f:(fun part ->
              begin match part with
              | [n1; n2] ->
                  let e1s = e1s_fn s g (erel, trel)
                    t { met with size = n1 }
                  in
                  let e2s = e2s_fn s g (erel, trel)
                    t1 { met with size = n2 }
                  in
                  (* Re-insert relevant variable into ctx for analysis... *)
                  let g = Gamma.insert_exp erel trel g in
                  (* ...and generate recursive and non-recursive applications *)
                  let (e1s_rec, e1s) =
                    Util.separate ~f:(fun e1 -> Gamma.is_rec_fun e1 g) (Rope.to_list e1s)
                  in
                  (* NOTE: Recursive functions may only appear in applications consisting *)
                  (*       of variables and projections of variables, since these are the *)
                  (*       only expressions that can be decreasing by current definitions.*)
                  (*       Thus, n1 and n2 must be size 1.                                *)
                  let es_rec =
                    Rope.concat_map ~f:begin fun e1 ->
                      if n1 <> 1 || n2 <> 1 then Rope.empty else
                      (* Filter out all invalid applications.                             *)
                      Rope.filter ~f:(fun e2 -> Gamma.is_valid_app e1 e2 g) e2s |>
                      Rope.map    ~f:(fun e2 -> EApp (e1, e2))
                    end (Rope.of_list e1s_rec)
                  in
                  let es_nonrec = Rope.cartesian_product [Rope.of_list e1s; e2s]
                    |> Rope.map ~f:begin fun pair ->
                        begin match pair with
                        | [e1; e2] -> EApp (e1, e2)
                        | _ -> failwith "(gen_eexp_rel_app) invalid part found"
                        end
                      end
                  in
                  Rope.concat es_nonrec es_rec
              | _ -> failwith "(gen_eexp_rel_app) invalid part found"
              end)
      | _ -> failwith "(get_eexp_rel_app) non-arrow type found"
      end)
  in

  (***** }}} *****)

  Timeout.check_timeout tmo;
  if met.size < 2 then Rope.empty else begin
  let producers =
      Gamma.insert_exp erel trel g
      |> Gamma.types
      |> List.dedup_and_sort ~compare
      |> List.fold_left ~f:(fun acc u ->
        begin match extract_producer t u with
        | Some prod -> prod :: acc
        | None -> acc
        end) ~init:[]
      |> List.dedup_and_sort ~compare
  in
  (* To synthesize applications, there are two cases:
   * (1) xrel appears at the head of the application, i.e., must be a function
   *     that produces ts *)
  let head_relevant = gen_apps producers met
    (fun s g (erel, trel) t m -> gen_eexp_rel tmo s (erel, trel) g t m)
    (fun s g (erel, trel) t m ->
      gen_iexp tmo s (Gamma.insert_exp erel trel g) t m)
  in
  (* (2) xrel does not appear at the head so it appears in the argument *)
  let head_not_relevant = gen_apps producers met
    (fun s g _ t m -> gen_eexp tmo s g t m)
    (fun s g (erel, trel) t m -> gen_iexp_rel tmo s (erel, trel) g t m)
  in
  Rope.concat head_relevant head_not_relevant end

and gen_iexp (tmo:Timeout.t) (s:Sigma.t) (g:Gamma.t)
             (t:typ) (met:metric) : exp Rope.t =

  (***** gen_iexp_helpers {{{ *****)

  let gen_ctor_one (s:Sigma.t) (g:Gamma.t) ((c, (c_typ, _)):id * (typ * id))
                   (met:metric) : exp Rope.t =
    let sub_exps = gen_iexp tmo s g c_typ { met with size = met.size - 6 } in
    Rope.map ~f:(fun sub_exp -> ECtor (c, sub_exp)) sub_exps
  in

  let gen_ctors (s:Sigma.t) (g:Gamma.t) (dt:id) : exp Rope.t =
    Sigma.ctors dt s |> Rope.of_list
      |> Rope.concat_map ~f:(fun ctor -> gen_ctor_one s g ctor met)
  in

  let gen_tuple (s:Sigma.t) (g:Gamma.t) (ts:typ list) : exp Rope.t =
     Util.partitions (met.size - 1) (List.length ts)
       |> List.map ~f:(List.zip_exn ts)
       |> Rope.of_list
       |> Rope.concat_map ~f:(fun part -> begin
           List.map ~f:(fun (t, n) ->
             gen_iexp tmo s g t { met with size = n }) part
             |> Rope.cartesian_product
             |> Rope.map ~f:(fun es -> ETuple es)
         end)
  in

  let gen_record (s:Sigma.t) (g:Gamma.t) (ts:typ record) : exp Rope.t =
     Util.partitions (met.size - 1) (List.length ts)
       |> List.map ~f:(List.zip_exn ts)
       |> Rope.of_list
       |> Rope.concat_map ~f:(fun part -> begin
           List.map ~f:(fun ((_,t), n) ->
             gen_iexp tmo s g t { met with size = n }) part
             |> Rope.cartesian_product
             |> Rope.map ~f:(fun es ->
               ERcd (List.zip_exn (Util.fst_assoc ts) es))
         end)
  in

  let gen_abs (s:Sigma.t) (g:Gamma.t) (t1:typ) (t2:typ) : exp Rope.t =
    let x = Gamma.fresh_id (gen_var_base t1) g in
    gen_iexp tmo s (Gamma.insert x t1 g) t2
      { size = met.size; lambdas = met.lambdas - 1 }
      |> Rope.map ~f:(fun e -> EFun ((x, t1), e))
  in

  (***** }}} *****)

  Timeout.check_timeout(tmo);
  if met.size <= 0 then Rope.empty else
  fetch_or_calculate memo_iexp_tbl (GTS.make_key g t met)
    begin fun _ ->
      begin match Gamma.peel g with
      | None ->
          begin match t with
          | TBase dt -> gen_ctors s g dt
          | TArr (t1, t2) -> gen_abs s g t1 t2
          | TTuple ts -> gen_tuple s g ts
          | TRcd ts -> gen_record s g ts
          | TUnit     -> Rope.cons EUnit Rope.empty
          end
      | Some ((erel, trel), g) ->
        let weakened = gen_iexp tmo s g t met in
        let relevant = gen_iexp_rel tmo s (erel, trel) g t met in
        Rope.concat weakened relevant
      end
    end

and gen_iexp_rel (tmo:Timeout.t) (s:Sigma.t)
                 ((erel, trel):exp * typ)
                 (g:Gamma.t) (t:typ) (met:metric) : exp Rope.t =

  (***** gen_iexp_rel helpers {{{ *****)

  let gen_ctor_one (s:Sigma.t) (g:Gamma.t) ((c, (c_typ, _)):id * (typ * id))
                   (met:metric) : exp Rope.t =
    let sub_exps =
      gen_iexp_rel tmo s (erel, trel) g c_typ { met with size = met.size - 6 }
    in
    Rope.map ~f:(fun sub_exp -> ECtor (c, sub_exp)) sub_exps
  in

  let gen_ctors (s:Sigma.t) (g:Gamma.t) (dt:id) : exp Rope.t =
    Sigma.ctors dt s |> Rope.of_list
      |> Rope.concat_map ~f:(fun ctor -> gen_ctor_one s g ctor met)
  in

  let gen_tuple (s:Sigma.t) (g:Gamma.t) (ts:typ list) : exp Rope.t =
    let argc = List.length ts in
    let choices = Util.partitions_rel argc in
    let parts   = Util.partitions (met.size - 1) argc
      |> List.map ~f:(List.zip_exn ts)
    in
    List.cartesian_product parts choices
      |> List.map ~f:(fun (ps, cs) -> List.zip_exn ps cs) |> Rope.of_list
      |> Rope.concat_map ~f:(fun part -> begin
           List.map ~f:(fun ((t, n), ch) ->
             let met = { met with size = n } in
             begin match ch with
             | Util.MayNot -> gen_iexp tmo s g t met
             | Util.Must   -> gen_iexp_rel tmo s (erel, trel) g t met
             | Util.May    ->
                 gen_iexp tmo s (Gamma.insert_exp erel trel g) t met
             end) part
             |> Rope.cartesian_product
             |> Rope.map ~f:(fun es -> ETuple es)
         end)
  in

  let gen_record (s:Sigma.t) (g:Gamma.t) (lts:typ record) : exp Rope.t =
    let ts = Util.snd_assoc lts in
    let argc = List.length ts in
    let choices = Util.partitions_rel argc in
    let parts   = Util.partitions (met.size - 1) argc
      |> List.map ~f:(List.zip_exn ts)
    in
    List.cartesian_product parts choices
      |> List.map ~f:(fun (ps, cs) -> List.zip_exn ps cs) |> Rope.of_list
      |> Rope.concat_map ~f:(fun part -> begin
           List.map ~f:(fun ((t, n), ch) ->
             let met = { met with size = n } in
             begin match ch with
             | Util.MayNot -> gen_iexp tmo s g t met
             | Util.Must   -> gen_iexp_rel tmo s (erel, trel) g t met
             | Util.May    ->
                 gen_iexp tmo s (Gamma.insert_exp erel trel g) t met
             end) part
             |> Rope.cartesian_product
             |> Rope.map ~f:(fun es ->
               ERcd (List.zip_exn (Util.fst_assoc lts) es))
         end)
  in

  let gen_abs (s:Sigma.t) (g:Gamma.t) (t1:typ) (t2:typ) =
    let x = Gamma.fresh_id (gen_var_base t1) g in
    gen_iexp_rel tmo s (erel, trel) (Gamma.insert x t1 g)
      t2 { size = met.size; lambdas = met.lambdas - 1 }
      |> Rope.map ~f:(fun e -> EFun ((x, t1), e))
  in

  (***** }}} *****)

  Timeout.check_timeout tmo;
  if met.size <= 0 then Rope.empty else
  fetch_or_calculate memo_iexp_rel_tbl
    (GTS.make_key (Gamma.insert_exp erel trel g) t met)
    begin fun _ ->
      begin match t with
      | TBase dt -> gen_ctors s g dt
      | TArr (t1, t2) -> gen_abs s g t1 t2
      | TTuple ts -> gen_tuple s g ts
      | TRcd ts -> gen_record s g ts
      | TUnit     -> Rope.empty
      end
      |> Rope.concat (gen_eexp_rel tmo s (erel, trel) g t met)
    end

(***** }}} *****)
