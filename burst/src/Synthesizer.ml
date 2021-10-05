open Lang

module type IOSynth = sig
  val synth : problem:Problem.t -> Expr.t
end
