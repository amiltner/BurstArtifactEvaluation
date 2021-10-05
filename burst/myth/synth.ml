open Core
open Consts
open Lang
open Printf
open Rtree
open Sigma

type synth_step =
  | SynthSaturate of float      (* Try to saturate e-guesses *)
  | SynthGrowMatches            (* Increase the depth of matches *)
  | SynthGrowScrutinees of int  (* Grow the scrutinees of all matches *)

type synth_plan = synth_step list

let standard_synth_plan : synth_plan =
  [ SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ]

let saturate_guesses (timeout:float) (s:Sigma.t) (env:env) (t:rtree) =
  let rec update n =
    if n <= !max_eguess_size then begin
      Timing.record
        ~label:"saturate_guesses::update_exps"
        ~action:(fun _ -> update_exps timeout s env t);
      Timing.record
        ~label:"saturate_guesses::propogate_exps"
        ~action:(fun _ -> propogate_exps t |> ignore);
      update (n+1)
    end
  in
    update 1

let execute_synth_step (s:Sigma.t) (env:env) (t:rtree) (st:synth_step) : exp list option =
  reset_timeouts t;
  begin match st with
  | SynthSaturate timeout -> begin
      do_if_verbose (fun _ ->
        printf "Saturating E-guesses (timeout = %.2f)...\n%!" timeout);
      Timing.record
        ~label:"synth::saturate_guesses"
        ~action:(fun _ -> saturate_guesses timeout s env t)
    end
  | SynthGrowMatches -> begin
      do_if_verbose (fun _ -> printf "Growing matches...\n%!");
      Timing.record
        ~label:"synth::grow_matches"
        ~action:(fun _ -> grow_matches s env t)
    end
  | SynthGrowScrutinees k -> begin
      do_if_verbose (fun _ -> printf "Growing scrutinees by %d...\n%!" k);
      Timing.record
        ~label:"synth::grow_scrutinees"
        ~action:(fun _ -> grow_scrutinees s env k t)
    end
  end;
  do_if_verbose (fun _ -> printf "%s\n%!" (Rtree.pp_rtree t));
  let es =
    Timing.record
      ~label:"synth::propogate_exps"
      ~action:(fun _ -> propogate_exps ~short_circuit:false t)
  in
  begin match es with
  | [] -> None
  | es -> Some es
  end

let rec execute_synth_plan
    (s:Sigma.t)
    (env:env)
    (t:rtree)
    (plan:synth_plan) : exp list =
  match plan with
  | [] -> failwith "couldn't find"
  | st :: plan -> begin
    match execute_synth_step s env t st with
      | Some es ->
        let sized_es =
          List.map
            ~f:(fun e -> (size e,e))
            es
        in
        let sorted_es =
          List.sort
            ~compare:(fun (i1,_) (i2,_) -> Int.compare i1 i2)
            sized_es
        in
        List.map ~f:snd sorted_es
      | None ->
        print_endline "step 1";
        execute_synth_plan s env t plan
    end

let synthesize (s:Sigma.t) (env:env) (t:rtree) : exp list =
  execute_synth_plan s env t standard_synth_plan
