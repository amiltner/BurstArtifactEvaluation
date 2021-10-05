open MyStdLib
open Burst
open Lang

module T : Burst.Synthesizers.IOSynth.S = struct
  type t = (Context.t * Type.t * Type.t) * Problem.t

  let init
      ~(problem:Problem.t)
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
    : t =
    ((context,tin,tout),problem)

  let context = fst3 % fst
  let tin = snd3 % fst
  let tout = trd3 % fst

  let rec term_of_type
      (c:Context.t)
      (t:Type.t)
    : Expr.t =
    begin match Type.node t with
      | Named i -> term_of_type c (Context.find_exn c.tc i)
      | Arrow (t1,t2) ->
        Expr.mk_func
          (Id.create "x",t1)
          (term_of_type c t2)
      | Tuple ts ->
        Expr.mk_tuple (List.map ~f:(term_of_type c) ts)
      | Mu _ -> failwith "TODO"
      | Variant bs ->
        let (i,t) = List.hd_exn bs in
        Expr.mk_ctor i (term_of_type c t)
    end

  let synthesize
      (a:t)
      (ios:(Value.t * Value.t) list)
    : Expr.t =
    if (List.length ios = 0) then
      term_of_type (context a) (Type.mk_arrow (tin a) (tout a))
    else
    let ios = List.map ~f:(fun (v1,v2) -> (Value.to_exp v1,Value.to_exp v2)) ios in
    let ios =
      List.map
        ~f:(fun (vin,vout) ->
            begin match Expr.destruct_tuple vin with
              | Some vins -> (vins,vout)
              | None -> ([vin],vout)
            end)
        ios
    in
    let tins =
      begin match Type.destruct_tuple (tin a) with
        | None -> [(tin a)]
        | Some tins -> tins
      end
    in
    let (sigma,iets,examples,t,tins,tout) = ToSmythConverter.convert_problem_examples_type_to_smyth (snd a) ios tins (tout a) in
    let datatype_ctx : Smyth.Lang.datatype_ctx =
      sigma
    in
    let asserts =
      List.map
        ~f:(fun (eins,e2) ->
            (List.fold_left
               ~f:(fun e arg ->
                   (Smyth.Lang.EApp
                      (false,e
                      ,EAExp arg)))
               ~init:(Smyth.Lang.EVar "f")
               eins)
          ,e2)
        examples
    in
    let (firsttin,othertins) = split_by_first_exn tins in
    let surround b e =
      let mk_x i =
        "x" ^ (string_of_int i)
      in
          let (e,i) =
            List.fold_right
              ~f:(fun _ (e,i) ->
                  (Smyth.Lang.EFix
                     (None
                     ,Smyth.Lang.PatParam (Smyth.Lang.PVar (mk_x i))
                     ,e)
                  ,i+1))
              ~init:(e,0)
              othertins
          in
          Smyth.Lang.EFix
            ((if b then Some "f" else None)
            ,Smyth.Lang.PatParam (Smyth.Lang.PVar (mk_x i))
            ,e)
    in
    let final_var =
      ("f"
      ,(t
       ,surround false (Smyth.Lang.EHole 0)))
    in
    let desugar_program : Smyth.Desugar.program =
      { datatypes = datatype_ctx
      ; definitions = iets@[final_var]
      ; assertions = asserts
      ; main_opt = None
      }
    in
    let result = Smyth.Endpoint.solve_program desugar_program in
    begin match result with
      | Ok r ->
        begin match Smyth.Rank.sort (r.hole_fillings) with
          | [(0,e)]::_ ->
            let e = surround true e in
            let e = FromSmythConverter.convert_expr e in
            begin match Type.destruct_tuple (tin a) with
              | Some ts ->
                let argv = Id.create "x" in
                let arge = Expr.mk_var argv in
                Expr.mk_func
                  (Id.create "x",(tin a))
                  (fst (List.fold_left
                     ~f:(fun (acce,i) tin ->
                         (Expr.mk_app
                            acce
                            (Expr.mk_proj i arge),
                          i+1))
                     ~init:(e,0)
                     ts))
              | None ->
                e
            end
          | x ->
            failwith "No solutions found"
        end
      | Error e ->
        print_endline (Smyth.Endpoint.show_error e);
        failwith "ah"
    end

  let synth
      (a:t)
      (ios:(Value.t * Value.t) list)
    : t * Expr.t =
    (a,synthesize a ios)
end
