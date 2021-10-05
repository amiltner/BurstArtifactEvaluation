open MyStdLib
open Lang

module type IS = (Singleton with type t = Value.t list)

module T(IS : IS) = struct
  let satisfies_post
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(cand:Expr.t)
      ~(checker:Value.t -> Value.t -> bool)
    : Value.t option =
    let sized =
      List.sort
        ~compare:(fun v1 v2 -> Int.compare (Value.size v1) (Value.size v1))
        IS.value
    in
    let ios =
      List.map
        ~f:(fun v ->
            (v,Eval.safe_evaluate_with_holes ~eval_context:context.evals (Expr.mk_app cand (Value.to_exp v))))
        sized
    in
    List.find_map
      ~f:(fun (i,o) ->
          begin match o with
            | Some o ->
              if checker i o then
                 None
              else
                 Some i
            | None ->
              Some i
          end)
      ios
end
