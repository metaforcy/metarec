

structure EnvDiff = struct

datatype env = EnvDiff of { env: Envir.env,  diff_slots: indexname list Symtab.table }

fun empty maxidx = EnvDiff { env = Envir.empty maxidx, diff_slots = Symtab.empty }

fun get_env (EnvDiff {env, ...}) = env
fun get_diff_slots (EnvDiff {diff_slots, ...}) = diff_slots


fun map_env f (EnvDiff {env, diff_slots}) =
  EnvDiff {env = f env, diff_slots = diff_slots}
fun map_diff_slots f (EnvDiff {env, diff_slots}) =
  EnvDiff {env = env, diff_slots = f diff_slots}

fun register_diff_slot uid envdiff =
  map_diff_slots (Symtab.update_new (uid, [])) envdiff
  handle Symtab.DUP => error ("register_diff_slot: already registered uid "^quote uid)
fun unregister_diff_slot uid envdiff =
  map_diff_slots (Symtab.delete uid) envdiff
  handle Symtab.UNDEF => error ("unregister_diff_slot: unregistered uid "^quote uid)
fun get_diff_slot envdiff uid =
  case Symtab.lookup (get_diff_slots envdiff) uid of
    SOME inst_vars => inst_vars
  | NONE => error ("get_diff_slot: unregistered uid "^quote uid)
fun clear_diff_slot uid envdiff =
  map_diff_slots (Symtab.update (uid, []) uid)

fun get_and_clear_diff_slot uid envdiff =
  let val diff_slot = get_diff_slot envdiff uid
  in (diff_slot, clear_diff_slot uid envdiff) end

fun set_env env2 envdiff = map_env (K env2) envdiff
fun set_env_in envdiff env2 = set_env env2 envdiff

val maxidx_of = Envir.maxidx_of o get_env
val term_env = Envir.term_env o get_env
val type_env = Envir.type_env o get_env
val is_empty = Envir.is_empty o get_env

fun merge (EnvDiff {env=env1, diff_slots=diff_slots1})
     (EnvDiff {env=env2, diff_slots=diff_slots2}) =
   EnvDiff {env = Envir.merge (env1, env2),
     diff_slots = Symtab.merge_list (op =) (diff_slots1, diff_slots2)}

fun genvars n (envdiff, Ts) =
  Envir.genvars n (get_env envdiff, Ts)
  |>> set_env_in envdiff 
fun genvar n (envdiff, T) = 
  Envir.genvar n (get_env envdiff, T)
  |>> set_env_in envdiff

fun lookup (envdiff, ixnT) = Envir.lookup (get_env envdiff, ixnT)

(* no lookup' because it works directly on Envir.tenv *)

(* EnvDiff's raison d'etre *)
fun update (ixnT_t as ((ixn, _), _), envdiff) = envdiff
  |> map_env (curry Envir.update ixnT_t)
  |> map_diff_slots (Symtab.map (K (cons ixn)))

fun above envdiff envdiff i = Envir.above (get_env envdiff) i

(* no vupdate with more complex variable assignment logic *)

(* no norm_type* *)

val norm_term_same = Envir.norm_term_same o get_env
val norm_term = Envir.norm_term o get_env
val head_norm = Envir.head_norm o get_env
val fastype = Envir.fastype o get_env

(* no subst_* *)

end
