let logging = ref false
let use_random = ref false
let print = ref false

let log thunk =
  if !logging then
    print_endline (Core.Time.to_string (Core.Time.now ()) ^ " " ^ thunk ())
  else
    ()

let path_to_vata = ref "../../libvata/build/cli/vata"

let isect_times = ref (0.0,0.0)
let minify_times = ref (0.0,0.0)
let min_elt_times = ref (0.0,0.0)
let initial_creation_times = ref (0.0,0.0)
let accepts_term_times = ref (0.0,0.0)
let copy_times = ref (0.0,0.0)
let full_synth_times = ref (0.0,0.0)

let loop_count = ref 0

let time t f =
  let (ttot,tmax) = !t in
  let init = Sys.time () in
  let ans = f () in
  let time_taken = (Sys.time() -. init) in
  let ttot = (ttot +. time_taken) in
  let tmax = max time_taken tmax in
  t := (ttot,tmax);
  ans

let total t = fst !t
let max t = snd !t
