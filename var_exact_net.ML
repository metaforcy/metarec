
signature VAR_EXACT_NET =
sig
  (* type key
  val key_of_term: term -> key list *)

  type 'a net
  val empty: 'a net

  (* returns indices that are now instantiated, together with their previous partial instantiation *)
  val normalize: ('a * 'a -> bool) -> 'a net * EnvDiff.env
    -> (term * term) list * ('a net * EnvDiff.env)

  exception INSERT
  (* val insert: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_safe: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net*)
  val insert_term: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_term_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net

  exception DELETE
  (* val delete: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_safe: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net *)
  val delete_term: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val delete_term_safe: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net

  (* val lookup: 'a net -> key list -> 'a list *)
  (* these include normalization as preprocessing *)
  val lookup_term: ('a * 'a -> bool) -> 'a net * EnvDiff.env -> term
    -> 'a list * ('a net * EnvDiff.env)
  val rev_match_term: ('a * 'a -> bool) -> 'a net * EnvDiff.env -> term
    -> 'a list * ('a net * EnvDiff.env)

  val entries: 'a net -> 'a list
  val content: 'a net -> 'a list

  (* NB: these assume normalized net *)
  val subtract: ('b * 'a -> bool) -> 'a net -> 'b net -> 'b list
  val merge: ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
end;



structure VarExactNet : VAR_EXACT_NET = struct

(* NB: exact nets are always understood wrt. a linearly-threadid EnvDiff.env
   that contains the unprocessed instantiated unification variables in the diff_slot
   corresponding to the VarExactNet.net *)
datatype 'a net = VarExactNet of {
  net: 'a Net.net,
  diff_slot_uid: string,
  indices_with_unifvar: term Vartab.table }

fun map_net f (VarExactNet {net, diff_slot_uid, indices_with_unifvar}) =
  VarExactNet {net = f net, diff_slot_uid = diff_slot_uid,
    indices_with_unifvar = indices_with_unifvar}
fun map_diff_slot_uid f (VarExactNet {net, diff_slot_uid, indices_with_unifvar}) =
  VarExactNet {net = net, diff_slot_uid = f diff_slot_uid,
    indices_with_unifvar = indices_with_unifvar}
fun map_indices_with_unifvar f (VarExactNet {net, diff_slot_uid, indices_with_unifvar}) =
  VarExactNet {net = net, diff_slot_uid = diff_slot_uid,
    indices_with_unifvar = f indices_with_unifvar}

fun get_net (VarExactNet {net, diff_slot_uid, indices_with_unifvar}) =
  net
fun get_diff_slot_uid (VarExactNet {net, diff_slot_uid, indices_with_unifvar}) =
  diff_slot_uid
fun get_indices_with_unifvar (VarExactNet {net, diff_slot_uid, indices_with_unifvar}) =
  indices_with_unifvar


val empty = VarExactNet {
  net = Net.empty,
  diff_slot_uid = "exact_net_"^string_of_int (serial ()),
  indices_with_unifvar: Vartab.empty }

val fix_index_term =
  Term.map_aterms (fn Var((n, _), T) => Free(n, T) | t => t)

fun normalize eq (enet, envdiff) =
  let
    val (inst_vars, envdiff') =
      EnvDiff.get_and_clear_diff_slot (get_diff_slot_uid enet) envdiff
    val inst_indices = [] |> fold (fn inst_var =>
        case Vartab.lookup (get_indices_with_unifvar enet) inst_var of
          SOME index_term =>
            insert (eq_fst (op aconv)) (index_term, EnvDiff.norm_term envdiff index_term)
        | NONE => I)
      inst_vars
    val enet' = enet
      |> map_indices_with_unifvar (
           fold Vartab.delete_safe inst_vars
           #> fold (fn (_, inst_t) =>
                  let val vs = Term.add_vars inst_t [] |> map fst
                  in fold (fn v => Vartab.update_list (op aconv) (v, inst_t)) vs end) 
                inst_indices)
      |> map_net (fold (fn (t, inst_t) => fn net =>
             let
               val t'_keys = fix_index_term t |> Net.key_of_term
               val as = Net.lookup net t'_keys
             in 
               net |> fold (fn a =>
                   Net.delete eq (t'_keys, a)
                   #> Net.insert_term_safe eq (fix_index_term inst_t, a))
                 as
             end)
           inst_indices)
  in
    (inst_indices, (enet', envdiff'))
  end

fun insert_term eq (t, a) =
  let
    val t' = fix_index_term t
    val vars = Term.add_vars t []
  in
    map_net (Net.insert_term eq (t', a))
    #> map_indices_with_unifvar (fold (fn (ixn, _) => Vartab.update (ixn, t)) vars)
  end


fun lookup_term eq t (enet, envdiff) =
  let
    val (_, (enet', envdiff')) = normalize eq (enet, envdiff)
    val t' = fix_index_term t
    val as = Net.lookup (get_net enet) (Net.key_of_term t') 
  in (as, (enet', envdiff')) end

fun rev_match_term eq t (enet, envdiff) =
  let
    val (_, (enet', envdiff')) = normalize eq (enet, envdiff)
    val as = Net.unify_term (get_net enet') t
  in (as, (enet', envdiff')) end

val entries = Net.entries o get_net

fun subtract eq enet1 enet2 = Net.subtract eq (get_net enet1) (get_net enet2)
fun merge eq (enet1, enet2) = Net.merge eq (get_net enet1, get_net enet2)

val content = Net.content o get_net


end
