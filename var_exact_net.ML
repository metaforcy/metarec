
(* Motivation: efficient rev_match_term in the face of common term shapes only differing in unifvars.
   This cannot be realized by just fixing unifvars in index terms before net insertion and lookup,
   because unifvars in index terms can become instantiated thus invalidating the indexing of the net
   (which is just an approximation precision issue in normal nets where unifvars are approximated by wildcards).
   Therefore we normalize the indexing and merge content that is now referred to by the same index.
     Additionally we perform normalizing (singulary) "merge" of content which became instantiated,
   even if the corresponding index did not become instantiated. *)
signature VAR_EXACT_NET =
sig
  type 'a net

  val empty: EnvDiff.env
    -> (EnvDiff.env -> 'a -> (indexname * sort) list)
    -> (EnvDiff.env -> 'a -> (indexname * typ) list)
    -> (Proof.context -> EnvDiff.env -> term -> 'a list -> 'a list)
    -> 'a net * EnvDiff.env
  val unregister_diff_slot_of: 'a net -> EnvDiff.env -> EnvDiff.env
  val with_empty_delayed_unreg: ((EnvDiff.env -> EnvDiff.env) -> 'b -> 'b) -> ('b -> EnvDiff.env) -> 'b
    -> (EnvDiff.env -> 'a -> (indexname * sort) list) 
    -> (EnvDiff.env -> 'a -> (indexname * typ) list)
    -> (Proof.context -> EnvDiff.env -> term -> 'a list -> 'a list)
    -> ('a net -> 'b -> 'c * 'b) -> ('c * ('b -> 'b)) * 'b
  val with_empty: ((EnvDiff.env -> EnvDiff.env) -> 'b -> 'b) -> ('b -> EnvDiff.env) -> 'b
    -> (EnvDiff.env -> 'a -> (indexname * sort) list)
    -> (EnvDiff.env -> 'a -> (indexname * typ) list)
    -> (Proof.context -> EnvDiff.env -> term -> 'a list -> 'a list)
    -> ('a net -> 'b -> 'c * 'b) -> 'c * 'b

  (* returns relevant instantiate type and term variables,
     and indices that are now instantiated, together with their previous partial instantiation *)
  val normalize: Proof.context -> ('a * 'a -> bool) -> 'a net * EnvDiff.env
    -> (((indexname * sort) list * (indexname * typ) list) * (term list * term) list)
       * ('a net * EnvDiff.env)
  val is_normalized: 'a net * EnvDiff.env -> bool

  exception INSERT
  (* index term has to be beta normal, not necessarily eta normal; net has to be normal *)
  val insert_term: EnvDiff.env -> ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_term_safe: EnvDiff.env -> ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net

  exception DELETE
  (* index term has to be beta normal, not necessarily eta normal; net has to be normal *)
  val delete_term: EnvDiff.env -> ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val delete_term_safe: EnvDiff.env -> ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net

  (* index term has to be beta- and env-normal, not necessarily eta normal;
     pre-lookup net normalization is included *)
  val lookup_term: Proof.context -> ('a * 'a -> bool) -> term -> 'a net * EnvDiff.env
    -> 'a list * ('a net * EnvDiff.env)
  val rev_match_term: Proof.context -> ('a * 'a -> bool) -> term -> 'a net * EnvDiff.env
    -> (term * 'a) list * ('a net * EnvDiff.env)

  exception NON_NORMAL_NET
  (* index term has to be beta- and env-normal, not necessarily eta normal;
     net has to be normal *)
  val demand_normalized: 'a net * EnvDiff.env -> unit
  val lookup_term_in_normed_net: 'a net * EnvDiff.env -> term -> 'a list
  val rev_match_term_in_normed_net: 'a net * EnvDiff.env -> term -> (term * 'a) list

  val entries: 'a net -> (term * 'a) list
  val content: 'a net -> (term * 'a) list

  (* these functions assume normalized net *)
  val subtract: EnvDiff.env -> ('b * 'a -> bool) -> 'a net -> 'b net -> (term * 'b) list
  val merge: EnvDiff.env -> ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
end;


structure VarExactNet : VAR_EXACT_NET = struct

(* NB: exact nets are always understood wrt. a linearly-threaded EnvDiff.env
   that contains the unprocessed instantiated unification variables in the diff_slot
   corresponding to the VarExactNet.net *)
datatype 'a net = VarExactNet of {
    net: (term * 'a) Net.net,
    diff_slot_uid: string,
    (* (non-fixed) indices as they are used in net under prepfix_index_term preprocessing,
       indexed by the type/term unification variable indexnames that occur in them
       or in content indexed by them *)
    indices_rel_for_type_unifvar: term list Vartab.table, 
    indices_rel_for_term_unifvar: term list Vartab.table,
    tvars_of_content: EnvDiff.env -> 'a -> (indexname * sort) list,
    vars_of_content: EnvDiff.env -> 'a -> (indexname * typ) list,
    merge_entries_on_index_inst: Proof.context -> EnvDiff.env -> term
      -> 'a list -> 'a list
  }

fun map_net f (VarExactNet { net, diff_slot_uid, indices_rel_for_term_unifvar,
    indices_rel_for_type_unifvar, tvars_of_content, vars_of_content, merge_entries_on_index_inst }) =
  VarExactNet { net = f net, diff_slot_uid = diff_slot_uid,
    indices_rel_for_type_unifvar = indices_rel_for_type_unifvar,
    indices_rel_for_term_unifvar = indices_rel_for_term_unifvar,
    tvars_of_content = tvars_of_content,
    vars_of_content = vars_of_content,
    merge_entries_on_index_inst = merge_entries_on_index_inst }
fun map_diff_slot_uid f (VarExactNet { net, diff_slot_uid,
      indices_rel_for_term_unifvar, indices_rel_for_type_unifvar,
      tvars_of_content, vars_of_content, merge_entries_on_index_inst }) =
  VarExactNet { net = net, diff_slot_uid = f diff_slot_uid,
    indices_rel_for_type_unifvar = indices_rel_for_type_unifvar,
    indices_rel_for_term_unifvar = indices_rel_for_term_unifvar,
    tvars_of_content = tvars_of_content,
    vars_of_content = vars_of_content,
    merge_entries_on_index_inst = merge_entries_on_index_inst }
fun map_indices_rel_for_unifvar f g (VarExactNet { net, diff_slot_uid,
      indices_rel_for_term_unifvar, indices_rel_for_type_unifvar,
      tvars_of_content, vars_of_content, merge_entries_on_index_inst }) =
  VarExactNet { net = net, diff_slot_uid = diff_slot_uid,
    indices_rel_for_type_unifvar = f indices_rel_for_type_unifvar,
    indices_rel_for_term_unifvar = g indices_rel_for_term_unifvar,
    tvars_of_content = tvars_of_content,
    vars_of_content = vars_of_content,
    merge_entries_on_index_inst = merge_entries_on_index_inst }

fun get_net (VarExactNet {net, ...}) = net
fun get_diff_slot_uid (VarExactNet {diff_slot_uid, ...}) =
  diff_slot_uid
fun get_indices_rel_for_term_unifvar (VarExactNet {indices_rel_for_term_unifvar, ...}) =
  indices_rel_for_term_unifvar
fun get_indices_rel_for_type_unifvar (VarExactNet {indices_rel_for_type_unifvar, ...}) =
  indices_rel_for_type_unifvar
fun get_merge_entries_on_index_inst (VarExactNet {merge_entries_on_index_inst, ...}) =
  merge_entries_on_index_inst 
fun get_tvars_of_content (VarExactNet {tvars_of_content, ...}) = tvars_of_content
fun get_vars_of_content (VarExactNet {vars_of_content, ...}) = vars_of_content


fun empty envdiff tvars_of_content vars_of_content merge_entries_on_index_inst =
  let
    val enet = VarExactNet {
      net = Net.empty,
      diff_slot_uid = "var_exact_net:"^string_of_int (serial ()),
      indices_rel_for_type_unifvar = Vartab.empty,
      indices_rel_for_term_unifvar = Vartab.empty,
      tvars_of_content = tvars_of_content,
      vars_of_content = vars_of_content,
      merge_entries_on_index_inst = merge_entries_on_index_inst }
    val envdiff2 = envdiff
      |> EnvDiff.register_diff_slot (get_diff_slot_uid enet)
  in
    (enet, envdiff2)
  end

fun unregister_diff_slot_of enet =
  EnvDiff.unregister_diff_slot (get_diff_slot_uid enet)

fun with_empty_delayed_unreg map_envdiff get_envdiff st0 tvars_of_content vars_of_content
    merge_entries_on_index_inst f =
  let
    val envdiff0 = get_envdiff st0
    val (enet, envdiff) = empty envdiff0 tvars_of_content vars_of_content merge_entries_on_index_inst 
    val st = st0 |> map_envdiff (K envdiff)
    val (res, st2) = f enet st
    val unregister_slot = map_envdiff (unregister_diff_slot_of enet)
  in ((res, unregister_slot), st2) end

fun with_empty map_envdiff get_envdiff st0 tvars_of_content vars_of_content merge_entries_on_index_inst f =
  let
    val ((res, unregister_slot), st2) =
      with_empty_delayed_unreg map_envdiff get_envdiff st0
        tvars_of_content vars_of_content merge_entries_on_index_inst f
  in (res, unregister_slot st2) end



val prepfix_index_term =
  Envir.eta_contract
  #> Term.map_types (Term.map_atyps (fn TVar((n, _), S) => TFree(n, S) | T => T))
  #> Term.map_aterms (fn Var((n, _), T) => Free(n, T) | t => t)

exception NON_NORMAL_NET



fun modify_indices_via_content_unifvars envdiff oper (t, x) enet =
  let
    val tvars = get_tvars_of_content enet envdiff x
    val vars = get_vars_of_content enet envdiff x
  in
    enet |> map_indices_rel_for_unifvar
      (fold (fn (ixn, _) => oper (op aconv) (ixn, t)) tvars)
      (fold (fn (ixn, _) => oper (op aconv) (ixn, t)) vars)
  end
fun ins_indices_via_content_unifvars envdiff (t, x) =
  modify_indices_via_content_unifvars envdiff Vartab.insert_list (t, x)
fun rem_indices_via_content_unifvars envdiff (t, x) =
  modify_indices_via_content_unifvars envdiff Vartab.remove_list (t, x)

fun modify_indices_via_occ_unifvars oper t =
  let
    val tvars = Term.add_tvars t []
    val vars = Term.add_vars t []
  in
    map_indices_rel_for_unifvar
      (fold (fn (ixn, _) => oper (op aconv) (ixn, t)) tvars)
      (fold (fn (ixn, _) => oper (op aconv) (ixn, t)) vars)
  end
fun ins_indices_via_occ_unifvars t =
  modify_indices_via_occ_unifvars Vartab.insert_list t
fun rem_indices_via_occ_unifvars t =
  modify_indices_via_occ_unifvars Vartab.remove_list t



fun index_eq env (t1, t2) = (EnvDiff.norm_term env t1) aconv (EnvDiff.norm_term env t2)

fun normalize_internal demand_normal ctxt_opt eq (enet, envdiff) =
  let
    val ((inst_Tvar_ixns, inst_var_ixns), envdiff2) =
      EnvDiff.get_and_clear_diff_slot (get_diff_slot_uid enet) envdiff
    val idx_eq = index_eq envdiff2

    fun add_index_term index_term = 
      insert (eq_fst (op aconv)) (index_term, EnvDiff.norm_term envdiff2 index_term)
    val inst_rel_indices = []
      |> fold (fn inst_Tvar_ixn =>
             fold add_index_term (Vartab.lookup (get_indices_rel_for_type_unifvar enet) inst_Tvar_ixn |> these))
           inst_Tvar_ixns
      |> fold (fn inst_var_ixn =>
             fold add_index_term (Vartab.lookup (get_indices_rel_for_term_unifvar enet) inst_var_ixn |> these))
           inst_var_ixns
  in
    if null inst_rel_indices then
      ((([], []), []), (enet, envdiff2))
    else if demand_normal then
      raise NON_NORMAL_NET
    else
      let
        val ctxt = case ctxt_opt of
            SOME ctxt => ctxt
          | NONE => error ("var exact net normalize: no context given and entry merge necessary")

        val inst_rel_indices_grpd = inst_rel_indices |> Library.partition_eq (eq_snd (op aconv))
          |> map (fn grp => (map fst grp, snd (hd grp)))
        (* val _ = tracing ("var exact net normalize: inst_rel_indices_grpd is \n"^
          cat_lines (inst_rel_indices_grpd |> map (fn (ts, inst_t) =>
            "  "^commas (ts |> map (Syntax.string_of_term ctxt))^"  instto  "
              ^Syntax.string_of_term ctxt inst_t))) *)
        val enet2 = enet
          |> map_indices_rel_for_unifvar (fold Vartab.delete_safe inst_Tvar_ixns)
               (fold Vartab.delete_safe inst_var_ixns)
          |> fold (fn (_, inst_t) => ins_indices_via_occ_unifvars inst_t) inst_rel_indices_grpd
          |> fold (fn (ts, inst_t) => fn enet =>
                 let
                   val (xss, enet2) = enet |> fold_map (fn t => fn enet_ =>
                       let
                         val t'_keys = prepfix_index_term t |> Net.key_of_term
                         val xs = Net.lookup (get_net enet_) t'_keys |> filter (fn (t2, _) => idx_eq (t2, t))
                           |> map snd
                         (* NB: uses "safe" delete to account for new identification of
                            previously distinct entries that have same key-approximation *)
                         val enet_2 = enet_
                           |> fold (fn x => map_net (Net.delete_safe (eq_pair idx_eq eq) (t'_keys, (t, x)))) xs
                       in (xs, enet_2) end)
                     (* NB: we include inst_t because it might have already existed as an index *)
                     (inst_t :: ts)

                   val xs' = get_merge_entries_on_index_inst enet2 ctxt envdiff2 inst_t (flat xss)
                   val enet3 = enet2 |> fold (fn x' =>
                       ins_indices_via_content_unifvars envdiff2 (inst_t, x'))
                     xs'
                 in
                   enet3 |> fold (fn x' =>
                       map_net (Net.insert_term_safe (eq_pair idx_eq eq) (prepfix_index_term inst_t, (inst_t, x'))))
                     xs'
                 end)
               inst_rel_indices_grpd

        val tvars_tab = Vartab.empty
          |> fold (fn (t, _) => fold Vartab.update (Term.add_tvars t [])) inst_rel_indices
        val vars_tab = Vartab.empty
          |> fold (fn (t, _) => fold Vartab.update (Term.add_vars t [])) inst_rel_indices
        val rel_inst_Tvars = inst_Tvar_ixns |> map_filter (fn ixn =>
          Vartab.lookup tvars_tab ixn |> Option.map (fn S => (ixn, S)))
        val rel_inst_vars = inst_var_ixns |> map_filter (fn ixn =>
          Vartab.lookup vars_tab ixn |> Option.map (fn T => (ixn, T)))

        fun intersects xs ys = not (null (inter (op =) xs ys))
        val inst_indices_grpd = inst_rel_indices_grpd |> filter (fn (ts, inst_t) =>
          ts |> exists (fn t => intersects rel_inst_vars (Term.add_vars t [])
            orelse intersects rel_inst_Tvars (Term.add_tvars t [])))
      in
        (((rel_inst_Tvars, rel_inst_vars), inst_indices_grpd), (enet2, envdiff2))
      end
  end

fun normalize ctxt eq enet_envdiff = normalize_internal false (SOME ctxt) eq enet_envdiff
fun demand_normalized (enet, envdiff) = 
  let
    fun eq _ = error "enet content equality should be unnecessary"
    val _ = normalize_internal true NONE eq (enet, envdiff)
  in () end
fun is_normalized (enet, envdiff) =
  (let val _ = demand_normalized (enet, envdiff)
   in true end)
  handle NON_NORMAL_NET => false




exception INSERT

(* t has to be beta normal *)
fun insert_term envdiff eq (t, x) enet =
  let val _ = demand_normalized (enet, envdiff)
  in
    enet
    |> map_net (fn net =>
         Net.insert_term (eq_pair (index_eq envdiff) eq) (prepfix_index_term t, (t, x)) net
         handle Net.INSERT => raise INSERT)
    |> ins_indices_via_occ_unifvars t
    |> ins_indices_via_content_unifvars envdiff (t, x)
  end

fun insert_term_safe envdiff eq (t, a) enet =
  insert_term envdiff eq (t, a) enet handle INSERT => enet



fun lookup_term_internal demand_normal ctxt_opt eq t (enet, envdiff) =
  let
    val (_, (enet2, envdiff2)) = normalize_internal demand_normal ctxt_opt eq (enet, envdiff)
    val xs = Net.lookup (get_net enet2) (prepfix_index_term t |> Net.key_of_term)
      |> filter (fn (t2, _) => index_eq envdiff2 (t2, t)) |> map snd
  in (xs, (enet2, envdiff2)) end

fun lookup_term ctxt eq t enet_envdiff = lookup_term_internal false (SOME ctxt) eq t enet_envdiff
fun lookup_term_in_normed_net enet_envdiff t =
  let fun eq _ = error "lookup_term_in_normed_net: equality unnecessary"
  in lookup_term_internal true NONE eq t enet_envdiff |> fst end


  
exception DELETE

(* t has to be beta normal *)
fun delete_term envdiff eq (t, x0) enet =
  let
    val xs = lookup_term_in_normed_net (enet, envdiff) t
    val x = case filter (fn x2 => eq (x0, x2)) xs of
        (x :: _) => x
      | _ => raise DELETE
    val xs' = xs |> remove eq x0
  in
    enet
    |> map_net (fn net =>
         Net.delete_term (eq_pair (index_eq envdiff) eq) (prepfix_index_term t, (t, x0)) net
         handle Net.DELETE => raise DELETE)
    |> rem_indices_via_occ_unifvars t
    |> rem_indices_via_content_unifvars envdiff (t, x)
       (* NB: without this we would remove too many indices_rel_for_unifvar entries because
          there could be content in xs' whose unifvars overlap with those in x *)
    |> fold (fn x' => ins_indices_via_content_unifvars envdiff (t, x')) xs'
  end

fun delete_term_safe envdiff eq (t, a) enet =
  delete_term envdiff eq (t, a) enet handle DELETE => enet





(* NB: assumes t to be beta normal *)
(* Finds entries for indices that match against t. Normal net match operation
   makes little sense for var_exact_nets, just use lookup_term. *)
fun rev_match_term_internal demand_normal ctxt_opt eq t (enet, envdiff) =
  let
    val (_, (enet2, envdiff2)) = normalize_internal demand_normal ctxt_opt eq (enet, envdiff)
    val xs = Net.unify_term (get_net enet2) (Envir.eta_contract t)
  in (xs, (enet2, envdiff2)) end

fun rev_match_term ctxt eq t enet_envdiff = rev_match_term_internal false (SOME ctxt) eq t enet_envdiff
fun rev_match_term_in_normed_net enet_envdiff t =
  let fun eq _ = error "rev_match_term_in_normed_net: equality unnecessary"
  in rev_match_term_internal true NONE eq t enet_envdiff |> fst end


fun entries enet = Net.entries (get_net enet)
fun content enet = Net.content (get_net enet)


(* NB: assumes normalized enet inputs! *)
fun subtract envdiff eq enet1 enet2 =
  if get_diff_slot_uid enet1 <> get_diff_slot_uid enet2 then
    error "var_exact_net subtract with different origins"
  else
    content enet2 |> Library.subtract (swap #> eq_pair (index_eq envdiff) eq) (content enet1)

(* NB: assumes normalized enet inputs! *)
fun merge envdiff eq (enet1, enet2) =
  if get_diff_slot_uid enet1 <> get_diff_slot_uid enet2 then
    error "var_exact_net merge with different origins"
  else
    enet1 |> fold (insert_term_safe envdiff eq) (content enet2)



end

