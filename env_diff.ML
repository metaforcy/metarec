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
fun update (ixnT_t as ((ixn, _), _)) envdiff = envdiff
  |> unsafe_map_env (curry Envir.update ixnT_t)
  |> map_diff_slots (Symtab.map (K (apsnd (cons ixn))))
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



end
