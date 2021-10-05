open Consts
open Format
open Lang

(***** Helpers  *****)

let fpf         = fprintf ;;
let ident ppf s = fpf ppf "%s" s ;;
let kwd   ppf s = fpf ppf "%s" s ;;

(*****  *****)

(***** Types  *****)

let prec_of_typ (t:typ) =
  match t with
  | TUnit    -> 150
  | TBase  _ -> 125
  | TRcd   _ -> 100
  | TTuple _ -> 75
  | TArr   _ -> 50

let rec fpf_typ ppf ((lvl, t): int * typ) =
  let this_lvl = prec_of_typ t in
  (if this_lvl < lvl then fpf ppf "(");
  begin match t with
  | TBase x       -> fpf ppf "%a" ident x
  | TArr (t1, t2) ->
      fpf ppf "@[<2>%a ->@ %a@]" fpf_typ (this_lvl+1, t1) fpf_typ (this_lvl, t2)
  | TTuple ts -> fpf_tuple_typ_list ppf (lvl, ts)
  | TRcd ts -> fpf ppf "{ %a }" fpf_record_typ (lvl, ts)
  | TUnit     -> fpf ppf "unit"
  end;
  (if this_lvl < lvl then fpf ppf ")")

and fpf_tuple_typ_list ppf (lvl, ts) =
  match ts with
  | []    -> ()
  | [t]   -> fpf ppf "%a" fpf_typ (76, t)  (* Hack to ensure that nested tuples get parens *)
  | t::ts -> fpf ppf "%a * %a" fpf_typ (76, t) fpf_tuple_typ_list (lvl, ts)

and fpf_record_typ ppf (lvl, ts) =
  match ts with
  | []    -> ()
  | [(l,t)] -> fpf ppf "%s : %a" l fpf_typ (101, t)
  | (l,t)::ts' -> fpf ppf "%s : %a; %a" l fpf_typ (101, t) fpf_record_typ (lvl, ts')

(*****  *****)

(***** Declarations and expressions  *****)

let prec_of_exp (e:exp) : int =
  match e with
  | EApp _  -> 500
  | EProj _ -> 500
  | ERcdProj _ -> 500
  | EFun _ | EFix _ | EPFun _ | ELet _-> 100
  | ECtor  (_, e) -> (match e with EUnit -> 1000 | _ -> 600)
  | ERcd _       -> 800
  | ETuple _       -> 700
  | EMatch  _      -> 200
  | _              -> 1000

let prec_of_value (v:value) : int =
  match v with
  | VFun _ | VPFun _ -> 100
  | VCtor (_, v) -> (match v with VUnit -> 1000 | _ -> 600)
  | VTuple _ -> 700
  | VRcd _ -> 800
  | VUnit    -> 1000

let rec is_nat_literal (e:exp) : bool =
  match e with
  | ECtor ("O", EUnit) -> true
  | ECtor ("S", e)     -> is_nat_literal e
  | _                  -> false

let rec is_list_literal (e:exp) : bool =
  match e with
  | ECtor ("Nil", EUnit)          -> true
  | ECtor ("Cons", ETuple [_; e]) -> is_list_literal e
  | _                             -> false

let fpf_nat_literal ppf e =
  let rec count n e =
    match e with
    | ECtor ("O", EUnit) -> fpf ppf "%d" n
    | ECtor ("S", e)     -> count (n+1) e
    | _ -> internal_error "fpf_nat_literal" "non-nat literal encountered"
  in
  count 0 e

let rec fpf_pattern_list ppf (ps:pattern list) =
  match ps with
  | []    -> ()
  | [p]   -> fpf ppf "%a" fpf_pattern p
  | p::ps -> fpf ppf "%a,@ %a" fpf_pattern p fpf_pattern_list ps

and fpf_record_pattern ppf (ps: pattern record) =
  match ps with
  | []    -> ()
  | [(l,p)] -> fpf ppf "%s = %a" l fpf_pattern p
  | (l,p)::ps' -> fpf ppf "%a; %s = %a" fpf_record_pattern ps' l fpf_pattern p

and fpf_pattern ppf (p:pattern) =
  match p with
  | PWildcard -> fpf ppf "@[<2>_@]"
  | PVar x    -> fpf ppf "%a" ident x
  | PTuple ps -> fpf ppf "@[<2>(%a)@]" fpf_pattern_list ps
  | PRcd ps -> fpf ppf "@[<2>{%a}@]" fpf_record_pattern ps

let fpf_pat ppf ((c, p):pat) =
  match p with
  | None -> fpf ppf "@[<2>%a@]" ident c
  | Some p -> fpf ppf "@[<2>%a %a@]" ident c fpf_pattern p

let fpf_ctor ppf ((c, t): ctor) =
  match t with
  | TUnit -> fpf ppf "%a" ident c
  | _     -> fpf ppf "%a of %a" ident c fpf_typ (0, t)

let rec fpf_ctors ppf (cs:ctor list) =
  match cs with
  | []    -> ()
  | [c]   -> fpf ppf "| %a" fpf_ctor c
  | c::cs -> fpf ppf "| %a@\n%a" fpf_ctor c fpf_ctors cs

let rec fpf_branch ppf ((lvl, b):int * branch) =
  let (p, e) = b in
  fpf ppf "@[<2>| %a -> %a@]" fpf_pat p fpf_exp (lvl, e)

and fpf_branches ppf ((lvl, bs):int * branch list) =
  match bs with
  | [] -> ()
  | [b] -> fpf ppf "%a" fpf_branch (lvl, b)
  | b::bs -> fpf ppf "%a@\n%a" fpf_branch (lvl, b) fpf_branches (lvl, bs)

and fpf_env_one ppf ((x, v):id * value) =
  fpf ppf "%a := %a" ident x fpf_value (0, v)

and fpf_env ppf (ev:env) =
  match ev with
  | []    -> fpf ppf "·"
  | [v]   -> fpf ppf "%a" fpf_env_one v
  | v::vs -> fpf ppf "%a,@\n%a" fpf_env_one v fpf_env vs

and fpf_example_list ppf (ws: world list) =
  match ws with
  | []    -> ()
  | [w]   -> fpf ppf "%a" fpf_example w
  | w::ws -> fpf ppf "%a;@  %a" fpf_example w fpf_example_list ws

and fpf_example ppf ((env, goal):world) =
  fpf ppf "%a |-> %a" fpf_env env fpf_value (0, goal)

and fpf_exp_list ppf (es:exp list) =
  match es with
  | []    -> ()
  | [e]   -> fpf ppf "%a" fpf_exp (0, e)
  | e::es -> fpf ppf "%a,@ %a" fpf_exp (0, e) fpf_exp_list es

and fpf_record_exp ppf (es: exp record) =
  match es with
  | []    -> ()
  | [(l,e)]   -> fpf ppf "%s = %a" l fpf_exp (0, e)
  | (l,e)::es' -> fpf ppf "%s = %a; %a" l fpf_exp (0, e) fpf_record_exp es'

and fpf_arg ppf ((x, t):arg) = fpf ppf "(%a:%a)" ident x fpf_typ (0, t)

and fpf_arg_list ppf (xs:arg list) =
  match xs with
  | []    -> ()
  | [x]   -> fpf ppf "%a" fpf_arg x
  | x::xs -> fpf ppf "%a %a" fpf_arg x fpf_arg_list xs

and fpf_ios ppf ((lvl, ios):int * (exp * exp) list) =
  match ios with
  | []            -> ()
  | [(e1, e2)]    -> fpf ppf "(f %a) -> %a" fpf_exp (lvl, e1) fpf_exp (lvl, e2)
  | (e1, e2)::ios -> fpf ppf "(f %a) -> %a@\n| %a"
      fpf_exp (lvl, e1) fpf_exp (lvl, e2) fpf_ios (lvl, ios)

and fpf_decl ppf (d:decl) =
  match d with
  | DData (dt, cs) -> fpf ppf "@[<2>type %a =@\n%a@]" ident dt fpf_ctors cs
  | DLet (x, is_rec, xs, t, e) ->
      fpf ppf "@[<2>let ";
      (if is_rec then fpf ppf "rec ");
      if List.length xs = 0 then
        fpf ppf "%a : %a =@\n%a@]@\n;;" ident x fpf_typ (0, t) fpf_exp (0, e)
      else
        fpf ppf "%a %a : %a =@\n%a@]@\n;;"
          ident x fpf_arg_list xs fpf_typ (0, t)
          fpf_exp (0, e);

and fpf_exp ppf ((lvl, e):int * exp) =
  if !pretty_ctors && is_nat_literal e then
    fpf_nat_literal ppf e
  else if !pretty_ctors && is_list_literal e then
    fpf_list_literal ppf e
  else
    let this_lvl = prec_of_exp e in
    (if this_lvl < lvl then fpf ppf "(");
    begin match e with
    | EVar x -> fpf ppf "%a" ident x
    | EApp (e1, e2) ->
        fpf ppf "@[<2>%a@ %a@]"
          fpf_exp (this_lvl, e1) fpf_exp (this_lvl + 1, e2)
    | EProj (n, e) ->
        fpf ppf "@[<2>#%d@ %a@]" n fpf_exp (this_lvl + 1, e)
    | EFun (x, e) ->
        fpf ppf "@[<2>fun %a ->@ %a@]" fpf_arg x fpf_exp (this_lvl, e)
    | ELet (f, is_rec, xs, t, e1, e2) ->
        fpf ppf "@[<2>let ";
        (if is_rec then fpf ppf "rec ");
        fpf ppf "%a %a : %a =@\n%a@]@\n"
          ident f fpf_arg_list xs fpf_typ (0, t)
          fpf_exp (this_lvl, e1);
        fpf ppf "@[<2>in@\n%a@]" fpf_exp (this_lvl, e2)
    | ECtor (c, EUnit)  -> fpf ppf "@[<2>%a@]" ident c
    | ECtor (c, e)      -> fpf ppf "@[<2>%a %a@]" ident c fpf_exp (this_lvl + 1, e)
    | EMatch (e, bs) ->
        fpf ppf "@[<2>match %a with@\n%a@]"
          fpf_exp (0, e) fpf_branches (this_lvl+1, bs)
    | EPFun ios -> fpf ppf "@[<2>%a@]" fpf_ios (this_lvl, ios)
    | EFix (f, x, t, e) -> fpf ppf "@[<2>fix %a %a : %a =@ %a@]"
      ident f fpf_arg x fpf_typ (0, t) fpf_exp (this_lvl, e)
    | ETuple es -> fpf ppf "@[<2>(%a)@]" fpf_exp_list es
    | EUnit -> fpf ppf "@[<2>()@]"
    | ERcd es -> fpf ppf "@[<2>{%a}@]" fpf_record_exp es
    | ERcdProj (l,e) -> fpf ppf "@[<2>%a.%s@]" fpf_exp (this_lvl + 1, e) l
    end;
    (if this_lvl < lvl then fpf ppf ")")

and fpf_list_literal ppf e =
  let rec fpf_elems ppf e =
    match e with
    | ECtor ("Nil", EUnit) -> ()
    | ECtor ("Cons", ETuple [e; ECtor ("Nil", EUnit)]) -> fpf ppf "%a" fpf_exp (0, e)
    | ECtor ("Cons", ETuple [e1; e2]) -> begin
        fpf ppf "%a " fpf_exp (0, e1);
        fpf_elems ppf e2
      end
    | _ -> internal_error "fpf_list_literal"
        (sprintf "non-list literal encountered")
        (* TODO: to print out the literal here, we need to make pp_exp
         * mutually recursive with fpf_exp... but I don't think that the
         * print formatters are reentrant... >_< *)
  in
  fpf ppf "[";
  fpf_elems ppf e;
  fpf ppf "]"

and fpf_value_list ppf (vs:value list) =
  match vs with
  | []    -> ()
  | [v]   -> fpf ppf "%a" fpf_value (0, v)
  | v::vs -> fpf ppf "%a,@ %a" fpf_value (0, v) fpf_value_list vs

and fpf_record_value ppf (vs: value record) =
  match vs with
  | []    -> ()
  | [(l,v)]   -> fpf ppf "%s = %a" l fpf_value (0, v)
  | (l,v)::vs' -> fpf ppf "%s = %a;@ %a" l fpf_value (0, v) fpf_record_value vs'

and fpf_value_pairs ppf ((lvl, vps):int * (value * value) list) =
  match vps with
  | []            -> ()
  | [(v1, v2)]    -> fpf ppf "%a => %a" fpf_value (lvl, v1) fpf_value (lvl, v2)
  | (v1, v2) :: vps -> fpf ppf "%a => %a@\n| %a"
      fpf_value (lvl, v1) fpf_value (lvl, v2) fpf_value_pairs (lvl, vps)

and fpf_value ppf ((lvl, v):int * value) =
  let this_lvl = prec_of_value v in
  (if this_lvl < lvl then fpf ppf "(");
  begin match v with
  | VCtor (c, VUnit) -> fpf ppf "@[<2>%a@]" ident c
  | VCtor (c, VTuple e) -> fpf ppf "@[<2>%a %a@]" ident c fpf_value (this_lvl, VTuple e)
  | VCtor (c, v)     -> fpf ppf "@[<2>%a %a@]" ident c fpf_value (this_lvl, v)
  | VFun (x, e, _) ->
      fpf ppf "@[<2>fun %a ->@ %a@]" ident x fpf_exp (this_lvl, e)
  | VPFun vps -> fpf ppf "@[<2>%a@]" fpf_value_pairs (this_lvl, vps)
  | VTuple vs -> fpf ppf "@[<2>(%a)@]" fpf_value_list vs
  | VRcd vs -> fpf ppf "@[<2>{%a}@]" fpf_record_value vs
  | VUnit -> fpf ppf "@[()@]"
  end;
  (if this_lvl < lvl then fpf ppf ")")

let rec fpf_decls ppf (ds:decl list) =
  match ds with
  | []    -> ()
  | [d]   -> fpf ppf "%a" fpf_decl d
  | d::ds -> fpf ppf "%a@\n@\n%a" fpf_decl d fpf_decls ds

let fpf_synth_problem ppf ((x, t, es):synth_problem) =
  fpf ppf "@[<2>let %a : %a |>@ { %a } =@ ?@]"
    ident x fpf_typ (0, t) fpf_exp_list es

let fpf_prog ppf ((ds, p):prog) =
  if List.length ds > 0 then
    fpf ppf "%a@\n@\n%a" fpf_decls ds fpf_synth_problem p
  else
    fpf ppf "%a" fpf_synth_problem p

(*****  *****)

let pp_aux (f:formatter -> 'a -> unit) : 'a -> string =
  (fun (x:'a) -> f str_formatter x; flush_str_formatter ())

let pp_typ t = (fpf_typ str_formatter (0, t); flush_str_formatter ()) ;;
let pp_exp e = (fpf_exp str_formatter (0, e); flush_str_formatter ()) ;;
let pp_value v = (fpf_value str_formatter (0, v); flush_str_formatter ()) ;;
let pp_decl = pp_aux fpf_decl    ;;
let pp_pat  = pp_aux fpf_pat     ;;
let pp_pattern = pp_aux fpf_pattern ;;
let pp_prog = pp_aux fpf_prog    ;;
let pp_env  = pp_aux fpf_env     ;;
let pp_example = pp_aux fpf_example ;;
let pp_example_list = pp_aux fpf_example_list ;;
