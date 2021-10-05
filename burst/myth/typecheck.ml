let neq = (<>)
let eq = (=)

open Core
open Lang
open Pp
open Printf
open Sigma
open Gamma

exception Type_error of string

module type Typecheck_Sig = sig
    val typecheck : prog -> Sigma.t * Gamma.t
    val check_decls : Sigma.t -> Gamma.t -> decl list -> Sigma.t * Gamma.t
end

module Typecheck : Typecheck_Sig = struct
    let type_error s = raise @@ Type_error s

    (***** Typecheck expressions {{{ *****)
    let rec check_exp (s:Sigma.t) (g:Gamma.t) (e:exp) : typ =
      match e with
      (* Variable: Retrieve its type from the context.                                    *)
      | EVar x -> begin match Gamma.lookup_type x g with
          | Some t -> t
          | None -> type_error (x ^ " hasn't been declared.")
          end
      (* Application: Ensure the function and argument types align.                       *)
      | EApp (e1, e2) ->
           let (t_func, t_arg) = (check_exp s g e1, check_exp s g e2) in
           begin match t_func with
           | TArr (t1, t2) ->
               if neq t_arg t1 then
                   type_error (sprintf
                       "Type mismatch in application %s.  %s found but %s expected "
                       (pp_exp e) (pp_typ t_arg) (pp_typ t1))
               else (*if not (Gamma.is_valid_app e1 e2 g) then
                   type_error
                      (sprintf "Non-decreasing argument wrt recursive function: %s" 
                      (Pp.pp_exp e))
                      else*) t2
           | _ -> type_error
               (sprintf "Function type expected but not found: %s" (Pp.pp_typ t_func))
           end
       (* Projection: Check the subexpressions of the tuple.                              *)
       | EProj (n, e) ->
           let t = check_exp s g e in
           begin match t with
           | TTuple ts ->
               if n > List.length ts || n < 1 then
                   type_error (sprintf "Invalid projection index %d: %s" n (Pp.pp_typ t))
               else
                   List.nth_exn ts (n - 1)
           | _ -> type_error (sprintf "Non-tuple type for projection: %s" (Pp.pp_typ t))
           end
       (* Record Projection: Check matching labeled subexpressions in the record.         *)
       | ERcdProj (l,e) ->
           let t = check_exp s g e in
           begin match t with
           | TRcd ts -> begin match Util.lookup l ts with
                         | Some t' -> t'
                         | None -> type_error @@
                                   sprintf "Label '%s' not found in record type: %s" l (Pp.pp_typ t)
                        end
           | _ -> type_error (sprintf "Non-record type for record projection: %s" (Pp.pp_typ t))
           end
       (* Function: Add the function argument to the context and check the body.          *)
       | EFun ((x, t1), e) -> TArr (t1, check_exp s (Gamma.insert x t1 g) e)
       (* Let: Distinguish between value and function bindings.                           *)
       | ELet (f, is_rec, xs, t_expected, e1, e2) ->
           (* Value binding.                                                              *)
           if List.length xs = 0 then
               check_exp s (Gamma.insert f (check_exp s g e1) g) e2
           (* Function binding.                                                           *)
           else
              let f_type = (List.map ~f:snd xs) @ [t_expected] |> types_to_arr in
              let t_actual = check_function_body s g f f_type xs e1 is_rec in
              if neq t_expected t_actual then
                type_error
                  (sprintf "Type mismatch in function body.  Expected %s, found %s"
                  (Pp.pp_typ t_expected) (Pp.pp_typ t_actual))
              else
                check_exp s (Gamma.insert f f_type g) e2
       (* Constructor: Check that it contains a properly typed expression.               *)
       | ECtor (c, e) -> begin match Sigma.lookup_ctor c s with
            | Some (t_expected, d) ->
                let t_actual = check_exp s g e in
                if neq t_expected t_actual then
                  type_error (sprintf
                    "Type mismatch in constructor: expected %s but found %s : %s"
                    (Pp.pp_typ t_expected) (Pp.pp_exp e) (Pp.pp_typ t_actual))
                else TBase d
            | None ->
                type_error (sprintf "%s: Constructor not found: %s" (Pp.pp_exp e) c)
            end
       (* Tuple: Check subexpressions.                                                   *)
       | ETuple es -> TTuple (List.map ~f:(check_exp s g) es)
       (* Record: Check subexpressions                                                   *)
       | ERcd es -> TRcd (List.map ~f:(fun (l,e) -> (l, check_exp s g e)) es)
       (* Match: Check branches.                                                         *)
       | EMatch (e, bs) -> begin match check_exp s g e with
           | TBase d ->
               let ctors = Sigma.restrict d s in
               let ts = check_branches s g ctors e bs in 
               if (Util.all_eq eq ts) && (List.length ts > 0) then List.hd_exn ts
               else type_error "type mismatch in match branches"
           | _ -> type_error (sprintf "%s: datatype expected in match" (Pp.pp_exp e))
           end
       | EPFun ios ->
           let ts = List.map ~f:(fun (e1, e2) ->
             let t1 = check_exp s g e1 in
             let t2 = check_exp s g e2 in
             TArr (t1, t2)) ios
           in
           if List.length ios = 0 then
             type_error "Partial function has no cases"
           else if not (Util.all_eq eq ts) then
             type_error
               (sprintf "%s: partial function branch types do not match"
                 (Pp.pp_exp e))
           else
             List.hd_exn ts
       | EFix (f, (x, t1), t2, e) ->
           let g = g |> Gamma.insert f (TArr (t1, t2))
                     |> Gamma.insert x t1
                     |> Gamma.mark_as_rec_fun_with_arg f x
                     |> Gamma.mark_as_arg_of_fun x f
           in
           let t2' = check_exp s g e in
           if neq t2 t2' then
               type_error (sprintf
                 "Type mismatch in function body %s.  %s found but %s expected"
                 (pp_exp e) (pp_typ t2') (pp_typ t2))
           else
             TArr (t1, t2)
       | EUnit -> TUnit

     and check_evidence (s:Sigma.t) (g:Gamma.t) (t:typ) (es:exp list) : unit =
       List.iter ~f:(fun e ->
           if neq t (check_exp s g e)
         then type_error (sprintf "%s: type mismatch in evidence" (pp_exp e))) es

     and check_branches (s:Sigma.t) (g:Gamma.t) (_:Sigma.t) (scrut:exp)
                        (bs:branch list) : typ list =
       let rec extract_types_from_pattern (t:typ) (p:pattern) : (id * typ) list =
         match (p, t) with
         | (PWildcard, _) -> []
         | (PVar x,    _) -> [(x, t)]
         | (PTuple ps, TTuple ts) ->
           if List.length ps <> List.length ts then
             type_error (sprintf "check_branches: pattern %s does not match type %s."
                         (Pp.pp_pattern p) (Pp.pp_typ t))
           else
             List.concat_map
               ~f:(fun (t, p) -> extract_types_from_pattern t p)
              (List.zip_exn ts ps)
         | (PRcd ps, TRcd ts) ->
           begin try List.concat_map ~f:(fun (p, v) ->
             extract_types_from_pattern v p) (Util.zip_without_keys ps ts)
           with Invalid_argument _ ->
             failwith (sprintf "check_branches: pattern %s down not match type %s"
                       (Pp.pp_pattern p) (Pp.pp_typ t))
           end
         | (_, _) -> 
             type_error (sprintf "check_branches: pattern %s does not match type %s."
                         (Pp.pp_pattern p) (Pp.pp_typ t))
       in
       let check_branch (((ctor_name, p_opt), branch_exp):branch) : typ =
           match Sigma.lookup_ctor ctor_name s with
           | None -> type_error ("Unknown constructor: " ^ ctor_name)
           | Some (arg_type, _) ->
             let extracted_types = begin match p_opt with
               | None -> []
               | Some p -> extract_types_from_pattern arg_type p 
             end in
             let g = List.fold_left
               ~f:(fun g (x, t) -> Gamma.insert x t g)
               ~init:g
               extracted_types
             in
             let g = begin match Gamma.fun_of_arg scrut g with
               | Some f -> List.fold_left
                 ~f:(fun g (x, _) -> Gamma.mark_as_dec_arg_of_fun x f g)
                 ~init:g
                 extracted_types
               | None   -> g
             end in
             check_exp s g branch_exp
       in
       List.map ~f:check_branch bs

     and check_function_body (s:Sigma.t) (g:Gamma.t) (f:id) (f_type:typ) (xs:arg list)
                             (body:exp) (is_rec:bool) : typ =
       (* Create context for checking function body.                                      *)
       let g_body = (* (1) Add arguments.                                                 *)
           List.fold_left
               ~f:(fun g (x, t) -> g |> Gamma.insert x t |> Gamma.mark_as_arg_of_fun x f)
               ~init:g
               xs
       in
       let g_body = (* 2) Add f to the context if it is recursive.                        *)
           if is_rec then List.fold_left
               ~f:(fun g (x, _) -> Gamma.mark_as_rec_fun_with_arg f x g)
               ~init:(Gamma.insert f f_type g_body)
               xs
           else g_body
       in
       check_exp s g_body body

    (***** }}} *****)
    
    (***** Typecheck declarations {{{ *****)
    (* Typecheck a single declaration.                                                    *)
    let check_decl (s:Sigma.t) (g:Gamma.t) (d:decl) : Sigma.t * Gamma.t =
      match d with
      | DData (datatype, ctors) ->
          (Sigma.append s (Sigma.make_from_data datatype ctors), g)
      | DLet (f, is_rec, xs, t_expected, e) ->
          (* A value binding.                                                             *)
          if List.length xs = 0 then
              let t_actual = check_exp s g e in
              if eq t_actual t_expected then
                  (s, Gamma.insert f t_actual g)
              else
                  type_error (sprintf "Type mismatch in let: %s expected, but %s found"
                      (Pp.pp_typ t_expected) (Pp.pp_typ t_actual))
          (* A function binding.                                                          *)
          else
              let func_type = (List.map ~f:snd xs) @ [t_expected] |> types_to_arr in
              let t_actual  = check_function_body s g f func_type xs e is_rec in
              if neq t_expected t_actual then
                type_error
                  (sprintf "Type mismatch in let function body.  Expected %s, found %s"
                  (Pp.pp_typ t_expected) (Pp.pp_typ t_actual))
              else
                (s, Gamma.insert f func_type g)

    (* Typecheck a list of declarations.                                                  *)
    let check_decls (s:Sigma.t) (g:Gamma.t) (ds:decl list) : Sigma.t * Gamma.t =
        List.fold_left ~f:(fun (s, g) d -> check_decl s g d) ~init:(s, g) ds

    let check_synth_problem (s:Sigma.t) (g:Gamma.t) ((_, t, vs):synth_problem) =
      check_evidence s g t vs

    (***** }}} *****)

    (* Typecheck an entire program.                                                       *)
    let typecheck ((decls, synth_problem):prog) =
      let (sigma, gamma) = check_decls Sigma.empty Gamma.empty decls in
      let _              = check_synth_problem sigma gamma synth_problem in
      (sigma, gamma)
end
    
