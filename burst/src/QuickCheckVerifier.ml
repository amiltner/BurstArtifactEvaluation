open MyStdLib
open Lang

module T = struct
  let _NUM_CHECKS_ = 4096
  module Generators = struct
    type t = Expr.t Sequence.t
  end

  module D = Map.Make(Type)

  let rec generator_of_type
      (tc:Context.Types.t)
      (t:Type.t)
    : Value.t QC.g =
    let generator_of_type_simple = generator_of_type tc in
    fun i ->
      begin match Type.node t with
        | Named i ->
          generator_of_type_simple (Context.find_exn tc i)
        | Arrow _ ->
          failwith "Will do if necessary..."
        | Tuple ts ->
          QC.map
            ~f:Value.mk_tuple
            (fun i -> (QC.product (List.map ~f:generator_of_type_simple ts)) i)
        | Mu (v,t) ->
          let tc = Context.set tc ~key:v ~data:t in
          generator_of_type tc t
        | Variant options ->
          let options_generators =
            List.map
              ~f:(fun (i,t) ->
                  let g = generator_of_type_simple t in
                  let g = QC.map ~f:(Value.mk_ctor i) g in
                  QC.subtract_size g 1)
              options
          in
          QC.choice options_generators
      end
        i

  let satisfies_post
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(cand:Expr.t)
      ~(checker:Value.t -> Value.t -> bool)
    : Value.t option =
    let generator = QC.g_to_seq (generator_of_type context.tc tin) in
    let io_seq =
      Sequence.map
        ~f:(fun v ->
            (v,Eval.safe_evaluate_with_holes ~eval_context:context.evals (Expr.mk_app cand (Value.to_exp v))))
        generator
    in
    let io_finite =
      Sequence.take
        io_seq
        _NUM_CHECKS_
    in
    Sequence.find_map
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
      io_finite
end
