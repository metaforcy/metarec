(* variable assignment environment with tracking of
   newly assigned type and term variables in named
   "difference slots" to be used by algorithms *)
signature ENV_DIFF = sig
  type env

  val empty: int -> env

  val get_env: env -> Envir.env
  val get_diff_slots: env -> (indexname list * indexname list) Symtab.table

  val unsafe_map_env: (Envir.env -> Envir.env) -> env -> env
  val unsafe_map_tyenv: (Type.tyenv -> Type.tyenv) -> env -> env
  val unsafe_map_tenv: (Envir.tenv -> Envir.tenv) -> env -> env
  val inc_maxidx: env -> env 

  val is_empty: env -> bool
  val maxidx_of: env -> int
  val term_env: env -> Envir.tenv
  val type_env: env -> Type.tyenv
  val merge: env * env -> env

  val register_diff_slot: string -> env -> env
  val unregister_diff_slot: string -> env -> env
  val get_diff_slot: env -> string -> indexname list * indexname list
  val clear_diff_slot: string -> env -> env
  val with_diff_slot: string -> (env -> env)
    -> env -> (indexname list * indexname list) * env

  val get_and_clear_diff_slot: string -> env -> (indexname list * indexname list) * env
  val genvars: string -> typ list -> env -> term list * env
  val genvar: string -> typ -> env -> term * env

  val lookup: env -> indexname * typ -> term option
  val lookup': env -> indexname * typ -> term option
  val lookup_wotype: env -> indexname -> (typ * term) option

  val lookup_type: env -> indexname * sort -> typ option
  val lookup_type_wosort: env -> indexname -> (sort * typ) option

  val update: (indexname * typ) * term -> env -> env
  val update_type: (indexname * sort) * typ -> env -> env

  val above: env -> int -> bool

  val norm_term_same: env -> term Same.operation
  val norm_term: env -> term -> term
  val norm_type: env -> typ -> typ
  val head_norm: env -> term -> term
  val fastype: env -> typ list -> term -> typ

  (* substitution without deep variable chasing *)
  val subst_type: env -> typ -> typ
  val subst_term: env -> term -> term

  (* can raise Type.TUNIFY *)
  val typ_match: theory -> typ * typ -> env -> env

  (* can raise Type.TYPE_MATCH *)
  val typ_unify: theory -> typ * typ -> env -> env


  exception Bound0Dependent of int
  datatype head_norm_ty = NormUnderAbs | NoNormUnderAbs
  val decr_bnd : int -> int -> term
  val decr_normopt : Envir.env -> int -> term -> term option
  val head_norm_same: head_norm_ty -> Envir.env -> term -> term
  val betaeta_head_norm: Envir.env -> term -> term

  (* only normalizing around instantiation sites of variables, not normalizing in the instantiation sites,
     but beta outside instantiation sites can affect instantiation via substitution of course *)
  val shallow_norm_type: env -> (typ -> typ) -> typ -> typ
  val shallow_norm_term: env -> ((typ -> typ) * (term -> term)) -> term -> term
  val shallow_norm_term_deepenv: env -> env -> term -> term

  val norm_context_structure : (term -> term) * ((typ -> typ) * (term -> term))
    -> term -> term

  val rename_abs_headnorming : env -> term -> term -> term -> term option
end



structure EnvDiff : ENV_DIFF = struct


datatype env = EnvDiff of { env: Envir.env,  diff_slots: (indexname list * indexname list) Symtab.table }

fun empty maxidx = EnvDiff { env = Envir.empty maxidx, diff_slots = Symtab.empty }

fun get_env (EnvDiff {env, ...}) = env
fun get_diff_slots (EnvDiff {diff_slots, ...}) = diff_slots

fun unsafe_map_env f (EnvDiff {env, diff_slots}) =
  EnvDiff {env = f env, diff_slots = diff_slots}
fun map_diff_slots f (EnvDiff {env, diff_slots}) =
  EnvDiff {env = env, diff_slots = f diff_slots}


fun unsafe_map_tyenv f = unsafe_map_env (fn (Envir.Envir { maxidx, tenv, tyenv }) =>
  Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = f tyenv })
fun unsafe_map_tenv f = unsafe_map_env (fn (Envir.Envir { maxidx, tenv, tyenv }) =>
  Envir.Envir {maxidx = maxidx, tenv = f tenv, tyenv = tyenv })
fun map_maxidx f = unsafe_map_env (fn (Envir.Envir { maxidx, tenv, tyenv }) =>
  Envir.Envir {maxidx = f maxidx, tenv = tenv, tyenv = tyenv })
val inc_maxidx = map_maxidx (fn i => i + 1)

val is_empty = get_env #> Envir.is_empty
val maxidx_of = get_env #> Envir.maxidx_of
val term_env = get_env #> Envir.term_env
val type_env = get_env #> Envir.type_env


fun register_diff_slot uid envdiff =
  map_diff_slots (Symtab.update_new (uid, ([], []))) envdiff
  handle Symtab.DUP _ => error ("register_diff_slot: already registered uid "^quote uid)
fun unregister_diff_slot uid envdiff =
  map_diff_slots (Symtab.delete uid) envdiff
  handle Symtab.UNDEF _ => error ("unregister_diff_slot: unregistered uid "^quote uid)
fun get_diff_slot envdiff uid =
  case Symtab.lookup (get_diff_slots envdiff) uid of
    SOME inst_vars => inst_vars
  | NONE => error ("get_diff_slot: unregistered uid "^quote uid)
fun clear_diff_slot uid =
  map_diff_slots (Symtab.update (uid, ([], [])))

fun get_and_clear_diff_slot uid envdiff =
  let val diff_slot = get_diff_slot envdiff uid
  in (diff_slot, clear_diff_slot uid envdiff) end

fun with_diff_slot name f envdiff =
  let
    val uid = name ^ string_of_int (serial ())
    val envdiff2 = envdiff |> register_diff_slot uid |> f
    val (diff, envdiff3) = get_and_clear_diff_slot uid envdiff2
      ||> unregister_diff_slot uid
  in
    (diff, envdiff3)
  end


fun set_env env2 envdiff = unsafe_map_env (K env2) envdiff

val maxidx_of = Envir.maxidx_of o get_env
val term_env = Envir.term_env o get_env
val type_env = Envir.type_env o get_env
val is_empty = Envir.is_empty o get_env


fun merge
      (EnvDiff {env=env1, diff_slots=diff_slots1},
       EnvDiff {env=env2, diff_slots=diff_slots2}) =
   EnvDiff {env = Envir.merge (env1, env2),
     diff_slots = Symtab.join (fn _ => fn ((tvar_ixns1, var_ixns1), (tvar_ixns2, var_ixns2)) =>
         (Library.merge (op =) (tvar_ixns1, tvar_ixns2),
          Library.merge (op =) (var_ixns1, var_ixns2)))
       (diff_slots1, diff_slots2) }

fun genvars n Ts envdiff =
  let val (env2, ts) = Envir.genvars n (get_env envdiff, Ts)
  in (ts, envdiff |> set_env env2) end
fun genvar n T envdiff = 
  let val (env2, t) = Envir.genvar n (get_env envdiff, T)
  in (t, envdiff |> set_env env2) end

fun lookup envdiff ixnT = Envir.lookup (get_env envdiff, ixnT)
fun lookup' envdiff ixnT = Envir.lookup' (term_env envdiff, ixnT)
fun lookup_wotype envdiff ixn = Vartab.lookup (term_env envdiff) ixn

fun lookup_type envdiff ixnS = Type.lookup (type_env envdiff) ixnS
fun lookup_type_wosort envdiff ixn = Vartab.lookup (type_env envdiff) ixn

(* EnvDiff's raison d'etre *)
fun update (ixnT_t as ((ixn, T), _)) envdiff =
  let
    val _ = ()
      (*case Vartab.lookup (term_env envdiff) ixn of
        SOME (T2, t) => error ("EnvDiff.update: variable "
          ^Syntax.string_of_term @{context} (Var (ixn, T))
          ^(if Type.eq_type (type_env envdiff) (T, T2) then ""
            else " (with differring types "^commas ([T,T2] |> map (Syntax.string_of_typ @{context}))^")")
          ^" already bound to "^Syntax.string_of_term @{context} t)
      | NONE => ()*)
  in
    envdiff
    |> unsafe_map_env (curry Envir.update ixnT_t)
    |> map_diff_slots (Symtab.map (K (apsnd (cons ixn))))
  end
fun update_type ((ixn, S), T) envdiff = envdiff
  |> unsafe_map_tyenv (Vartab.update_new (ixn, (S, T)))
  |> map_diff_slots (Symtab.map (K (apfst (cons ixn))))

fun above envdiff i = Envir.above (get_env envdiff) i

(* no vupdate with more complex variable assignment logic *)

val norm_term_same = Envir.norm_term_same o get_env
val norm_term = Envir.norm_term o get_env
val norm_type = Envir.norm_type o type_env
val head_norm = Envir.head_norm o get_env
val fastype = Envir.fastype o get_env


val subst_type = Envir.subst_type o type_env
fun subst_term envdiff = Envir.subst_term (type_env envdiff, term_env envdiff)








fun tvar_clash ixn S S' = raise TYPE ("Type variable " ^
  quote (Term.string_of_vname ixn) ^ " has two distinct sorts",
  [TVar (ixn, S), TVar (ixn, S')], []);


(*occurs check*)
fun occurs v envdiff =
  let
    fun occ (Type (_, Ts)) = exists occ Ts
      | occ (TFree _) = false
      | occ (TVar (w, S)) =
          Term.eq_ix (v, w) orelse
            (case lookup_type envdiff (w, S) of
              NONE => false
            | SOME U => occ U);
  in occ end;

(*chase variable assignments; if devar returns a type var then it must be unassigned*)
fun devar envdiff (T as TVar v) =
      (case lookup_type envdiff v of
        SOME U => devar envdiff U
      | NONE => T)
  | devar _ T = T;





fun typ_match thy =
  let
    val tsig = Sign.tsig_of thy

    fun match (V as TVar (v, S), T) envdiff =
          (case lookup_type envdiff (v, S) of
            NONE =>
              if V = T then envdiff
              else if Type.of_sort tsig (T, S) then update_type ((v, S), T) envdiff
              else raise Type.TYPE_MATCH
          | SOME U => if U = T then envdiff else raise Type.TYPE_MATCH)
      | match (Type (a, Ts), Type (b, Us)) envdiff =
          if a <> b then raise Type.TYPE_MATCH
          else matches (Ts, Us) envdiff
      | match (TFree x, TFree y) envdiff =
          if x = y then envdiff else raise Type.TYPE_MATCH
      | match _ _ = raise Type.TYPE_MATCH
    and matches (T :: Ts, U :: Us) envdiff = matches (Ts, Us) (match (T, U) envdiff)
      | matches _ envdiff = envdiff;

  in match end;




(*order-sorted unification*)
fun typ_unify thy TU =
  let
    val {classes = (_, classes), ...} = Sign.tsig_of thy |> Type.rep_tsig

    fun gen_tyvar S envdiff =
      let val maxidx = maxidx_of envdiff
      in (TVar ((Name.aT, maxidx+1), S), inc_maxidx envdiff) end

    fun mg_domain a S = Sorts.mg_domain classes a S
      handle Sorts.CLASS_ERROR _ => raise Type.TUNIFY;

    fun meet (_, []) envdiff = envdiff
      | meet (TVar (xi, S'), S) envdiff =
          if Sorts.sort_le classes (S', S) then envdiff
          else
            let val (T, envdiff2) = gen_tyvar (Sorts.inter_sort classes (S', S)) envdiff
            in update_type ((xi, S'), T) envdiff2 end
      | meet (TFree (_, S'), S) envdiff =
          if Sorts.sort_le classes (S', S) then envdiff
          else raise Type.TUNIFY
      | meet (Type (a, Ts), S) envdiff = meets (Ts, mg_domain a S) envdiff
    and meets (T :: Ts, S :: Ss) envdiff = meets (Ts, Ss) (meet (devar envdiff T, S) envdiff)
      | meets _ envdiff = envdiff;

    fun unif (ty1, ty2) envdiff =
      (case (devar envdiff ty1, devar envdiff ty2) of
        (T as TVar (v, S1), U as TVar (w, S2)) =>
          if Term.eq_ix (v, w) then
            if S1 = S2 then envdiff else tvar_clash v S1 S2
          else if Sorts.sort_le classes (S1, S2) then
            update_type ((w, S2), T) envdiff
          else if Sorts.sort_le classes (S2, S1) then
            update_type ((v, S1), U) envdiff
          else
            let val (T_inter, envdiff2) = gen_tyvar (Sorts.inter_sort classes (S1, S2)) envdiff
            in update_type ((v, S1), T_inter) (update_type ((w, S2), T_inter) envdiff2) end
      | (TVar (v, S), T) =>
          if occurs v envdiff T then raise Type.TUNIFY
          else meet (T, S) (update_type ((v, S), T) envdiff)
      | (T, TVar (v, S)) =>
          if occurs v envdiff T then raise Type.TUNIFY
          else meet (T, S) (update_type ((v, S), T) envdiff)
      | (Type (a, Ts), Type (b, Us)) =>
          if a <> b then raise Type.TUNIFY
          else unifs (Ts, Us) envdiff
      | (T, U) => if T = U then envdiff else raise Type.TUNIFY)
    and unifs (T :: Ts, U :: Us) envdiff = unifs (Ts, Us) (unif (T, U) envdiff)
      | unifs _ envdiff = envdiff;

  in unif TU end;












(* !! NB polyML compiler bug workaround: when handling exceptions with no
   (or unit) arguments, other exceptions with no (or unit) arguments are
   also handled so we avoid conflict with handling of Same.SAME and
   add useless int argument to Bound0Dependent exception!! *)
exception Bound0Dependent of int

fun decr_bnd lev i =
  let val _ = () (*tracing ("decr_bnd with level "^string_of_int lev^" on Bound "^string_of_int i)*)
  in
  if i = lev then
    let val _ = () (*tracing ("raising Bound0Dependent")*)
    in raise Bound0Dependent 0 end
  else if i > lev then Bound (i - 1)
  else raise Same.SAME
  end

(* NB: assumes head-normal term0 (i.e. not of the form
   (% xs. (% z. ..) $ a $ ..) modulo variable instantiation);
   instantiated variables are only chased if one of their arguments depends on  Bound 0 *)
fun decr_normopt env lev term0 =
  let
    fun full_commit f x = Same.commit f x handle Bound0Dependent _ => x


    fun decr lev (Abs (a, T, body)) =
          Abs (a, T, decr (lev + 1) body)
      | decr lev term =
          let
            val (head, args) = Term.strip_comb term
            val recfun = decr lev o Envir.head_norm env

            (*val _ = tracing ("decr: app split argument: "
              ^PolyML.makestring (*Syntax.string_of_term @{context}*) head^" $ "
              ^commas (args |> map (PolyML.makestring (*Syntax.string_of_term @{context}*))))*)

            val args'_calc_opt = args |> map (fn t => (t, Same.capture recfun t)) |> SOME
              handle Bound0Dependent _ => NONE
            val args_dependent = not (is_some args'_calc_opt)
            fun args'_committed () =
              (case args'_calc_opt of
                 SOME args'_calc => args'_calc
               | NONE => error "decr_normopt: internal error")
              |> map (fn (t, t'_opt) => the_default t t'_opt)
            fun args'_fully_committed () = args |> map (full_commit recfun)
            fun form_comb_with_same_head () =
              if args_dependent then raise Bound0Dependent 0
              else
                let val args' =
                  (case args'_calc_opt of
                     SOME args'_calc => args'_calc
                   | NONE => error "decr_normopt: internal error")
                  |> map (fn (_, t'_opt) => case t'_opt of SOME t' => t' | NONE => raise Same.SAME)
                in Term.list_comb (head, args') end
          in
            case head of
              Var (ixn, T) =>
                if args_dependent then
                  case Envir.lookup (env, (ixn, T)) of
                    SOME u => Same.commit (decr lev)
                      (Envir.head_norm env (Term.betapplys (u, args'_fully_committed ())))
                  | NONE => raise Bound0Dependent 0
                else
                  form_comb_with_same_head ()
            | Bound i =>
                if args_dependent then raise Bound0Dependent 0
                else
                  ((Term.list_comb (decr_bnd lev i, args'_committed ()))
                  handle Same.SAME => form_comb_with_same_head ()
                    (*| ex as Bound0Dependent _ =>
                        let val _ = tracing ("Bound0Dependent raised after decr_bnd in decr")
                        in raise ex end*))
            | Abs _ =>
                (* NB: term is head-normal (assumed for input term, otherwise ensured),
                   so head cannot be an abstraction *)
                error ("decr_normopt: term not head normal")
            | _ => 
                form_comb_with_same_head ()
          end
    val res = Same.commit (decr lev) term0 |> SOME
      handle Bound0Dependent _ => NONE
    (*val _ = tracing ("decr_normopt: returning "^(case res of
        SOME t => "SOME  "^PolyML.makestring (*Syntax.string_of_term @{context}*) t
      | NONE => "NONE")) *)
  in
    res
  end


datatype head_norm_ty = NormUnderAbs | NoNormUnderAbs

(* NB: if under_abs = NoNormUnderAbs, (% x. ..) is regarded as toplevel-normal,
   unlike Envir.head_norm *)
fun head_norm_same under_abs env =
  let
    fun norm (Var v) =
        (case Envir.lookup (env, v) of
          SOME u => Same.commit norm u
        | NONE => raise Same.SAME)
      | norm (Abs (a, T, body)) =
          (case under_abs of
            NormUnderAbs => Abs (a, T, norm body)
          | NoNormUnderAbs => raise Same.SAME)
      | norm (Abs (_, _, body) $ t) = Same.commit norm (subst_bound (t, body))
      | norm (f $ t) =
          (case norm f of
            Abs (_, _, body) => Same.commit norm (subst_bound (t, body))
          | nf => nf $ t)
      | norm _ = raise Same.SAME;
  in norm end;


fun betaeta_head_norm_same env t =
  let
    val _ = () (*tracing ("betaeta_head_norm_same on "^PolyML.makestring (*Syntax.string_of_term @{context}*) t)*)
    fun eta_step_same t2 =
      let
        val _ = () (*tracing ("eta_step_same on "^PolyML.makestring (*Syntax.string_of_term @{context}*) t2)*)
        fun eta_headnormed_body body' =
          let
            val _ = () (*tracing ("eta_headnormed_body on "^PolyML.makestring body')*)
          in
          case body' of
            f $ arg =>
              let
                val _ = () (*tracing ("eta_step_same: norming argument "
                  ^PolyML.makestring (*Syntax.string_of_term @{context}*) arg)*)
                val arg_normed = Same.commit (head_norm_same NoNormUnderAbs env) arg
                val _ = () (*tracing ("eta_step_same: normed argument to "
                  ^PolyML.makestring (*Syntax.string_of_term @{context}*) arg_normed)*)
              in
              (case arg_normed of
                Bound 0 =>
                  let
                    val decr_res = decr_normopt env 0 f
                    val _ = () (*tracing ("eta_step_same: decr_normopt returned "
                      ^PolyML.makestring (*Syntax.string_of_term @{context}*) f) *)
                  in
                  (case decr_res of
                    SOME f' => 
                      let val _ = ()(*tracing ("eta_step_same: eta reduction to "
                         ^PolyML.makestring (*Syntax.string_of_term @{context}*) f')*)
                      in f' end
                  | NONE => raise Same.SAME)
                  end
              | _ => raise Same.SAME)
              end
          | _ => raise Same.SAME
          end
      in
        case t2 of
          Abs (x, T, body) =>
            let
              val body2_opt = Same.capture (betaeta_head_norm_same env) body
              val body_eta_opt = Same.capture eta_headnormed_body (the_default body body2_opt)
            in
              case body2_opt of
                NONE => (case body_eta_opt of
                    NONE => raise Same.SAME
                  | SOME body_eta => body_eta)
              | SOME body2 => (case body_eta_opt of
                    NONE => Abs (x, T, body2)
                  | SOME body2_eta => body2_eta)
            end
        | _ => raise Same.SAME
      end

     val res = 
       Same.commit eta_step_same (head_norm_same NoNormUnderAbs env t) |> SOME
       handle Same.SAME => Same.capture eta_step_same t
     (* val _ = tracing ("betaeta_head_norm_same: returning "^
       (case res of
         SOME x => PolyML.makestring (*Syntax.string_of_term @{context}*) x
       | NONE => "raised SAME")) *)
   in
     case res of 
       SOME x => x
     | NONE => raise Same.SAME
   end
fun betaeta_head_norm env t = Same.commit (betaeta_head_norm_same env) t






  (* pat0 expected to be beta-normal and env-normal as far as interesting here;
     term0 is assumed to superficially match pat0 (modulo env-normalization) and is not required
     to be env- or beta-normal. *)
fun match_bvs_headnorming env pat0 term0 =
  let
    fun match_bvs p t al =
      case (p, t) of
        (Abs(x, _, p_body), Abs(y, _, t_body)) =>
          match_bvs p_body t_body 
            (if x="" orelse y="" then al else (x,y) :: al)
      | (p_f $ p_arg, t_f $ t_arg) =>
          match_bvs p_f t_f (match_bvs p_arg (head_norm env t_arg) al)
      | _ => al
  in
    match_bvs pat0 (head_norm env term0) []
  end

(* adapted from Pure/term.ML:rename_abs *)
fun rename_abs_headnorming env pat0 term0 t =
  let
    val ren = match_bvs_headnorming env pat0 term0
    fun ren_abs (Abs (x, T, b)) =
          Abs (the_default x (AList.lookup (op =) ren x), T, ren_abs b)
      | ren_abs (f $ t) = ren_abs f $ ren_abs t
      | ren_abs t = t
  in
    if null ren then NONE
    else SOME (ren_abs t)
  end


fun shallow_norm_type_same env deep_norm : typ Same.operation =
  let
    fun norm (Type (a, Ts)) = Type (a, Same.map norm Ts)
      | norm (TFree _) = raise Same.SAME
      | norm (TVar v) =
          (case lookup_type env v of
            SOME U => deep_norm U (* NB: deep normalization factored out! *)
          | NONE => raise Same.SAME);
  in norm end;

fun shallow_norm_type env deep_norm = Same.commit (shallow_norm_type_same env deep_norm)



fun shallow_norm_term_same env (deep_normT, deep_norm) : term Same.operation =
  let
    val normT = shallow_norm_type_same env deep_normT;


    fun norm_spine (h, args) : term = case h of
        Const (a, T) =>
          (Term.list_comb (Const (a, normT T), map (Same.commit norm) args)
           handle Same.SAME => Term.list_comb (Const (a, T), Same.map norm args))
      | Free (a, T) =>
          (Term.list_comb (Free (a, normT T), map (Same.commit norm) args)
           handle Same.SAME => Term.list_comb (Free (a, T), Same.map norm args))
      | Var (xi, T) =>
          (case lookup env (xi, T) of
            SOME u =>
              (* NB: deep normalization factored out! *)
              (* we even avoid beta-reductions here, creating the possibility that
                 deep_norm retains  (% xs. u) $ args  as an explicit substitution to save work. *)
              deep_norm (Library.foldl (op $) (u, map (Same.commit norm) args))
          | NONE =>
              (Term.list_comb (Var (xi, normT T), map (Same.commit norm) args)
               handle Same.SAME => Term.list_comb (Var (xi, T), Same.map norm args)))
      | Bound i => Bound i
      | Abs (a, T, body) =>
          (case args of
            [] => 
              (Abs (a, normT T, Same.commit norm body)
              handle Same.SAME => Abs (a, T, norm body))
          | t1 :: args2 =>
              let val (h', args') = Term.strip_comb (Term.subst_bound (t1, body))
              in
                norm_spine (h', args' @ args2)
                handle Same.SAME => Term.list_comb (h', args' @ args2)
              end)

    and norm t = norm_spine (Term.strip_comb t)

  in fn t =>
    let 
      (*val _ = tracing ("shallow_norm_term: on "^Syntax.string_of_term @{context} t)*)
      val t' = norm t
      (*val _ = tracing ("shallow_norm_term: norming "^Syntax.string_of_term @{context} t
        ^"  to   "^Syntax.string_of_term @{context} t')*)
    in t' end
  end;

fun shallow_norm_term env deep_norms =
  Same.commit (shallow_norm_term_same env deep_norms)
fun shallow_norm_term_deepenv env deep_env =
  Same.commit (shallow_norm_term_same env (norm_type deep_env, norm_term deep_env))


fun strip_alls_headnorming headnorm P =
  case headnorm P of
    Const("all", _) $ Abs(a, T, P2) =>
      strip_alls_headnorming headnorm P2 |> apfst (cons (a, T))
  | P' => ([], P')

fun strip_imps_headnorming headnorm P =
  case headnorm P of
    Const ("==>", _) $ A $ P2 =>
      strip_imps_headnorming headnorm P2 |> apfst (cons A)
  | P' => ([], P')
    
    

(* norms Ts, As and headnorm P in (!! xs : Ts. As(xs) ==> P(xs)) *)
fun norm_context_structure (headnorm, (normT, norm)) prop =
  let
    val (xs, P0) = strip_alls_headnorming headnorm prop
    val (As, P) = strip_imps_headnorming headnorm P0
  in
    Logic.list_implies (map norm As, headnorm P)
    |> curry Logic.list_all (map (apsnd normT) xs)
  end








(* testing *)
(*
(* to workaround on-the-fly beta reduction when using @{term ..} expressions;
   NB: later Syntax.string_of_term calls expect argument to be beta normal?! *)
definition
  appmark :: "('a :: {} => 'b :: {}) => 'a => 'b" (infixl "$$" 100) where 
  "appmark(f,x) == f(x)"
ML {*
  fun rm_appmark t =
    case t of
      Abs(x, T, body) => Abs(x, T, rm_appmark body)
    | Const(@{const_name "appmark"}, _) $ t1 $ t2 => rm_appmark (t1 $ t2)
    | t1 $ t2 => rm_appmark t1 $ rm_appmark t2
    | a => a
  fun int_of_string str = read_int (raw_explode str) |> fst
  fun bndfree_map t =
    t |> map_aterms (fn a => case a of
        Free(n, _) =>
          (case try (unprefix "Bnd") n |> Option.map int_of_string of
            SOME i => Bound i
          | NONE => a)
      | _ => a)
*}

 
ML {*
  val _ = tracing "======="
  val env0 = (Envir.empty 0)
  val bhn = EnvDiff.betaeta_head_norm env0
  val t = @{term "% x. (% z. f(% y. z(y))) $$ x"} |> rm_appmark
  (*val t2 = t |> Same.commit (EnvDiff.head_norm_same EnvDiff.NoNormUnderAbs env0)
  val t3 = (Free("f", @{typ "'a => 'b"})) |> EnvDiff.decr_normopt env0 0*)
  val (r1, r2) = t
    |> (fn t => (bhn t, t |> Envir.beta_norm |> Envir.eta_contract))
  *}

ML {*
  val t = @{term "% x. f $$ (g $$ x $$ z) $$ (g $$ x $$ Bnd1) $$ x"} |> rm_appmark |> bndfree_map;
  EnvDiff.decr_normopt env0 0 t;
*}
*)


end
