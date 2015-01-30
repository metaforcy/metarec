
(* Motivation: efficient rev_match_term in the face of common term shapes only differing in unifvars.
   This cannot be realized by just fixing unifvars in index terms before net insertion and lookup,
   because unifvars in index terms can become instantiated thus invalidating the indexing of the net
   (which is just an approximation precision issue in normal nets where unifvars are approximated by wildcards).
   Therefore we normalize the indexing. *)
signature VAR_EXACT_NET =
sig
  type 'a net

  val empty: EnvDiff.env -> 'a net * EnvDiff.env
  val unregister_diff_slot_of: 'a net -> EnvDiff.env -> EnvDiff.env
  val with_empty: ((EnvDiff.env -> EnvDiff.env) -> 'b -> 'b) -> ('b -> EnvDiff.env) -> 'b
    -> ('a net -> 'b -> 'b) -> 'b

  (* returns indices that are now instantiated, together with their previous partial instantiation *)
  val normalize: ('a * 'a -> bool) -> 'a net * EnvDiff.env
    -> (term * term) list * ('a net * EnvDiff.env)
  val is_normalized: 'a net * EnvDiff.env -> bool

  exception INSERT
  val insert_term: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_term_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net

  exception DELETE
  val delete_term: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val delete_term_safe: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net

  (* these assume env-normal term and include pre-lookup net normalization *)
  val lookup_term: ('a * 'a -> bool) -> term -> 'a net * EnvDiff.env
    -> 'a list * ('a net * EnvDiff.env)
  val rev_match_term: ('a * 'a -> bool) -> term -> 'a net * EnvDiff.env
    -> 'a list * ('a net * EnvDiff.env)

  exception NON_NORMAL_NET
  val demand_normalized: 'a net * EnvDiff.env -> unit
  val lookup_term_in_normed_net: ('a * 'a -> bool) -> 'a net * EnvDiff.env -> term
    -> 'a list
  val rev_match_term_in_normed_net: ('a * 'a -> bool) -> 'a net * EnvDiff.env -> term
    -> 'a list

  val entries: 'a net -> 'a list
  val content: 'a net -> 'a list

  (* NB: these assume normalized net *)
  val subtract: ('b * 'a -> bool) -> 'a net -> 'b net -> 'b list
  val merge: ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
end;


structure VarExactNet : VAR_EXACT_NET = struct

(* NB: exact nets are always understood wrt. a linearly-threaded EnvDiff.env
   that contains the unprocessed instantiated unification variables in the diff_slot
   corresponding to the VarExactNet.net *)
datatype 'a net = VarExactNet of {
    net: 'a Net.net,
    diff_slot_uid: string,
    (* (non-fixed) indices as they are used in net under fix_index_term preprocessing,
       indexed by their occuring type/term unification variable indexnames *)
    indices_with_type_unifvar: term list Vartab.table, 
    indices_with_term_unifvar: term list Vartab.table
  }

fun map_net f (VarExactNet { net, diff_slot_uid, indices_with_term_unifvar, indices_with_type_unifvar }) =
  VarExactNet { net = f net, diff_slot_uid = diff_slot_uid,
    indices_with_type_unifvar = indices_with_type_unifvar,
    indices_with_term_unifvar = indices_with_term_unifvar }
fun map_diff_slot_uid f (VarExactNet { net, diff_slot_uid,
      indices_with_term_unifvar, indices_with_type_unifvar }) =
  VarExactNet { net = net, diff_slot_uid = f diff_slot_uid,
    indices_with_type_unifvar = indices_with_type_unifvar,
    indices_with_term_unifvar = indices_with_term_unifvar }
fun map_indices_with_unifvar f g (VarExactNet { net, diff_slot_uid,
      indices_with_term_unifvar, indices_with_type_unifvar }) =
  VarExactNet { net = net, diff_slot_uid = diff_slot_uid,
    indices_with_type_unifvar = f indices_with_type_unifvar,
    indices_with_term_unifvar = g indices_with_term_unifvar }

fun get_net (VarExactNet {net, ...}) = net
fun get_diff_slot_uid (VarExactNet {diff_slot_uid, ...}) =
  diff_slot_uid
fun get_indices_with_term_unifvar (VarExactNet {indices_with_term_unifvar, ...}) =
  indices_with_term_unifvar
fun get_indices_with_type_unifvar (VarExactNet {indices_with_type_unifvar, ...}) =
  indices_with_type_unifvar


fun empty envdiff =
  let
    val enet = VarExactNet {
      net = Net.empty,
      diff_slot_uid = "var_exact_net:"^string_of_int (serial ()),
      indices_with_type_unifvar = Vartab.empty,
      indices_with_term_unifvar = Vartab.empty }
    val envdiff2 = envdiff
      |> EnvDiff.register_diff_slot (get_diff_slot_uid enet)
  in
    (enet, envdiff2)
  end

fun unregister_diff_slot_of enet =
  EnvDiff.unregister_diff_slot (get_diff_slot_uid enet)

fun with_empty map_envdiff get_envdiff init0 f =
  let
    val envdiff0 = get_envdiff init0
    val (enet, envdiff) = empty envdiff0
    val init = init0 |> map_envdiff (K envdiff)
    val res = f enet init
    val res2 = res |> map_envdiff (unregister_diff_slot_of enet)
  in res2 end




val fix_index_term =
  Term.map_types (Term.map_atyps (fn TVar((n, _), S) => TFree(n, S) | T => T))
  #> Term.map_aterms (fn Var((n, _), T) => Free(n, T) | t => t)

exception NON_NORMAL_NET


fun modify_indices_via_occ_unifvars T_op t_op t =
  let
    val tvars = Term.add_tvars t []
    val vars = Term.add_vars t []
  in
    map_indices_with_unifvar
      (fold (fn (ixn, _) => T_op (op aconv) (ixn, t)) tvars)
      (fold (fn (ixn, _) => t_op (op aconv) (ixn, t)) vars)
  end
fun upd_indices_via_occ_unifvars t =
  modify_indices_via_occ_unifvars Vartab.update_list Vartab.update_list t
fun rem_indices_via_occ_unifvars t =
  modify_indices_via_occ_unifvars Vartab.remove_list Vartab.remove_list t


fun normalize_internal demand_normal eq (enet, envdiff) =
  let
    val ((inst_Tvar_ixns, inst_var_ixns), envdiff2) =
      EnvDiff.get_and_clear_diff_slot (get_diff_slot_uid enet) envdiff
    val _ =
      if (null inst_Tvar_ixns andalso null inst_var_ixns) orelse not demand_normal then ()
      else 
        raise NON_NORMAL_NET

    fun add_index_term index_term = 
      (* NB: eta contraction just to improve index approx, we keep exact correspondence with indices *)
      insert (eq_fst (op aconv)) (index_term,
        EnvDiff.norm_term envdiff2 index_term |> Envir.eta_contract)
    val inst_indices = []
      |> fold (fn inst_Tvar_ixn =>
             fold add_index_term (Vartab.lookup (get_indices_with_type_unifvar enet) inst_Tvar_ixn |> these))
           inst_Tvar_ixns
      |> fold (fn inst_var_ixn =>
             fold add_index_term (Vartab.lookup (get_indices_with_term_unifvar enet) inst_var_ixn |> these))
           inst_var_ixns
    val enet2 = enet
      |> map_indices_with_unifvar (fold Vartab.delete_safe inst_Tvar_ixns)
           (fold Vartab.delete_safe inst_var_ixns)
      |> fold (fn (_, inst_t) => upd_indices_via_occ_unifvars inst_t) inst_indices
      |> map_net (fold (fn (t, inst_t) => fn net =>
             let
               val t'_keys = fix_index_term t |> Net.key_of_term
               val entries = Net.lookup net t'_keys
             in 
               net |> fold (fn a =>
                   Net.delete eq (t'_keys, a)
                   #> Net.insert_term_safe eq (fix_index_term inst_t, a))
                 entries
             end)
           inst_indices)
  in
    (inst_indices, (enet2, envdiff2))
  end

fun normalize eq enet_envdiff = normalize_internal false eq enet_envdiff
fun demand_normalized (enet, envdiff) = 
  let
    fun eq _ = error "enet content equality should be unnecessary"
    val _ = normalize_internal true eq (enet, envdiff)
  in () end
fun is_normalized (enet, envdiff) =
  (let val _ = demand_normalized (enet, envdiff)
   in true end)
  handle NON_NORMAL_NET => false




exception INSERT

(* NB: t not necessarily eta normal, but this is customary for better index approx *)
fun insert_term eq (t, a) enet =
  let
    val t' = fix_index_term t
  in
    enet
    |> map_net (fn net => Net.insert_term eq (t', a) net handle Net.INSERT => raise INSERT)
    |> upd_indices_via_occ_unifvars t
  end

fun insert_term_safe eq (t, a) enet =
  insert_term eq (t, a) enet handle INSERT => enet



  
exception DELETE

fun delete_term eq (t, a) enet =
  let
    val t' = fix_index_term t
  in
    enet
    |> map_net (fn net => Net.delete_term eq (t', a) net handle Net.DELETE => raise DELETE)
    |> rem_indices_via_occ_unifvars t
  end

fun delete_term_safe eq (t, a) enet =
  delete_term eq (t, a) enet handle DELETE => enet



fun lookup_term_internal demand_normal eq t (enet, envdiff) =
  let
    val (_, (enet2, envdiff2)) = normalize_internal demand_normal eq (enet, envdiff)
    val t' = fix_index_term t
    val entries = Net.lookup (get_net enet2) (Net.key_of_term t') 
  in (entries, (enet2, envdiff2)) end

fun lookup_term eq t enet_envdiff = lookup_term_internal false eq t enet_envdiff
fun lookup_term_in_normed_net eq enet_envdiff t =
  lookup_term_internal true eq t enet_envdiff |> fst


(* NB: assumes t to be beta-eta normal *)
(* Finds entries for indices that match against t. Normal net match operation
   makes little sense for var_exact_nets, just use lookup_term. *)
fun rev_match_term_internal demand_normal eq t (enet, envdiff) =
  let
    val (_, (enet2, envdiff2)) = normalize_internal demand_normal eq (enet, envdiff)
    val entries = Net.unify_term (get_net enet2) t
  in (entries, (enet2, envdiff2)) end

fun rev_match_term eq t enet_envdiff = rev_match_term_internal false eq t enet_envdiff
fun rev_match_term_in_normed_net eq enet_envdiff t =
  rev_match_term_internal true eq t enet_envdiff |> fst


fun entries enet = Net.entries (get_net enet)


(* NB: assumes normalized enet inputs! *)
fun subtract eq enet1 enet2 =
  if get_diff_slot_uid enet1 <> get_diff_slot_uid enet2 then
    error "var_exact_net subtract with different origins"
  else
    Net.subtract eq (get_net enet1) (get_net enet2)

(* NB: assumes normalized enet inputs! *)
fun merge eq (enet1, enet2) =
  if get_diff_slot_uid enet1 <> get_diff_slot_uid enet2 then
    error "var_exact_net merge with different origins"
  else
    enet1
    |> map_net (fn net1 => Net.merge eq (net1, get_net enet2))
    |> map_indices_with_unifvar
         (fn indices_w_type_unifvar1 =>
           Vartab.merge_list (op aconv) (indices_w_type_unifvar1, get_indices_with_type_unifvar enet2))
         (fn indices_w_term_unifvar1 =>
           Vartab.merge_list (op aconv) (indices_w_term_unifvar1, get_indices_with_term_unifvar enet2))

fun content enet = Net.content (get_net enet)


end

