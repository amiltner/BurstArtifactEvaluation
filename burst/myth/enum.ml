(*******************************************************************************
 * enum.ml - top-level driver for enumeration mode
 ******************************************************************************)

open Core
open Consts
open Lang
open Printf
open Rtree
open Sigma

let saturate_guesses_enum (timeout:float) (s:Sigma.t) (env:env) (t:rtree) =
  let rec update n =
    if n <= !max_eguess_size then begin
      do_if_verbose (fun _ -> printf "Synthesizing at size %d\n%!" n);
      update_exps ~short_circuit:false timeout s env t;
      update (n+1)
    end
  in
  update 1

let execute_enum_plan (s:Sigma.t) (env:env) (t:rtree) : exp list =
  let rec update n =
    if n <= !max_eguess_size then begin
      do_if_verbose (fun _ -> printf "Synthesizing at size %d\n%!" n);
      update_exps ~short_circuit:false 1.0 s env t;
      update (n+1)
    end
  in
  update 1;
  propogate_exps ~short_circuit:false t

let enumerate (s:Sigma.t) (env:env) (t:rtree) : exp list =
  execute_enum_plan s env t
