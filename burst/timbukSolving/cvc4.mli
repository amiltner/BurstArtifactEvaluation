
module type CONF = sig
  (* path to the CVC4 executable. *)
  val path : unit -> string

  val log : unit -> (string * out_channel) option
end

module Make (Conf : CONF) (Var : Solver.VARIABLE) : sig
  include Solver.S with module Var = Var

  val to_smt2: t -> Smt2.t
end
