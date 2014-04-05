
signature MetaRecData =
sig
  val True: term (* True *)
  val conjunctionE : thm (* P &&& Q ==> (P ==> Q ==> C) ==> C *)

  (* NB: head_terms for define, note, concat have to be most polymorphic *)

  val try_const_name : string
  val tryI : thm (* P ==> try P *)
  val brule_const_name : string
  val brule_const_def : thm (* brule_const P == P *)
  val frule_const_name : string
  val frule_const_def : thm (* frule_const P == P *)

  val constraint_headterm : term
  val constraintI : thm (* P ==> constraint P *)
  val foconstraint_headterm : term
  val foconstraintI : thm (* P ==> foconstraint P *)
  val fresh_unifvar_headterm : term
  val fresh_unifvarI: thm (* fresh_unifvar X *)
  val unify_headterm : term
  val unifyI : thm (* t1 == t2 ==> unify t1 t2 *)

  val note_headterm : term (* Const(note_const_name, ...) *)
  val note_const_def : thm  (* note_const P name == P *)
  val define_headterm : term (* Const(define_const_name, ...) *)
  val defineI : thm (* lhs_out == rhs  ==>  define_const name rhs lhs_out *)
  val concat_names_headterm : term (* Const(concat_names, ...) *)
  val concat_namesI : thm (* concat_names_const n1 n2 n' *)

  val mk_Trueprop : term -> term
  val dest_Trueprop : term -> term

  val unit_ty : typ
  val unit_elem : term

  val proplist_ty : typ
  val mk_prop_cons : term -> term -> term
  val prop_nil : term

  val gen_colljudI : thm  (* t == Trueprop True ==> t *)

  val prf_displayT : typ
  val app_prf_displayt : term -> term -> term

  val protect_eta_redex_var_const : typ -> term
  val protect_eta_redex_var_def : thm (* protect_eta_redex_var t == t *)
end


functor MetaRec(Data : MetaRecData) =
struct



(* TODO(feature): globally track unification variables (those introduced by fresh_unifvar_proc;
     as opposed to matching variables) in run_state and disallow their instantiation during rule matching *)

(* TODO(feature):
     * tracking of originating rule  of constraints and delayed unification problems to allow better error message 
     * tracking von Unifikationen waehrend Constraint-{Propagierung, Vereinfachung}
       (dann braucht man keine on-the-fly Propagierung von Constraints sobald sie entstehen um
       bessere Fehlermeldungen zu kriegen)
*)



(* TODO(feature): err_with_trace hiermit nutzen *)
fun string_of_thm_in_gctxt gctxt =
  case gctxt of
    Context.Proof ctxt => Display.string_of_thm ctxt
  | Context.Theory thy => Display.string_of_thm_global thy

             
(* returns NONE if f always returns NONE on xs and st,
   otherwise returns SOME st' with the first st' which f returned *)
fun fold_upto_first_change f xs st =
  case xs of
    [] => NONE
  | (x :: xs') =>
      (case f x st of
        NONE => fold_upto_first_change f xs' st
      | SOME st2 => SOME st2)

(* returns NONE if f always returns NONE on xs and st,
   otherwise returns SOME st' with the last st' which f returned *)
fun fold_with_change_tracking f xs st =
  case xs of
    [] => NONE
  | (x :: xs') =>
      (case f x st of
        NONE => fold_with_change_tracking f xs' st
      | SOME st2 =>
          (case fold_with_change_tracking f xs' st2 of
            SOME st3 => SOME st3
          | NONE => SOME st2))




infix abeconv
infix abeconvs
fun t1 abeconv t2 = (Envir.beta_eta_contract t1) aconv (Envir.beta_eta_contract t2)
fun t1s abeconvs t2s = forall (op abeconv) (t1s ~~ t2s)
fun aconv_norm norm (t1, t2) = (norm t1) aconv (norm t2)



fun ground t = null (Term.add_vars t []) andalso null (Term.add_tvars t [])

(* NB: Variable.export is not exact w.r.t. indices of re-generalized Vars, they rather get maxidx+1 *)
fun exact_freeze_props_thaw_thms props ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val cert = cterm_of thy
    val certT = ctyp_of thy

    val vars = fold Term.add_vars props []
    val tvars = fold Term.add_tvars props []

    (* NB: we avoid fx_n ending with "_", to avoid problem with
       Name.clean_index generating unexpecting variables
       for the fixed frees in Term_Subst.generalize in Thm.generalize *)
    val ((fxvar_ns, fxTvar_ns), ctxt2) = ctxt |> Variable.set_body false
      |> Variable.variant_fixes (map (fst #> fst #> Name.clean) vars)
      ||>> Variable.variant_fixes (map (fst #> fst #> Name.clean) tvars)
      ||> Variable.restore_body ctxt
    val var_fixing = vars ~~ fxvar_ns
    val tvar_fixing = tvars ~~ fxTvar_ns

    (* val _ = tracing ("exact_freeze_props_thaw_thms: var_fixing is  "
      ^commas (var_fixing |> map (fn ((ixn, T), fx_n) =>
        Syntax.string_of_term ctxt2 (Var (ixn, T)) ^":="^ 
        Syntax.string_of_term ctxt2 (Free(fx_n, T))))) *)

    val tvar_fixing_inst = tvar_fixing |> map (fn ((ixn, S), fx_n) => ((ixn, S), TFree(fx_n, S)))
    val freezeT = Term_Subst.instantiateT tvar_fixing_inst
    val freeze =
      Term_Subst.instantiate
        (tvar_fixing_inst,
         var_fixing |> map (fn ((ixn, T), fx_n) =>
           ((ixn, freezeT T), Free(fx_n, freezeT T))))

    fun thaw_th th = 
      let
        val maxidx' = Thm.maxidx_of th + 1
        val thaw_reinstT = tvar_fixing |> map (fn ((ixn, S), fx_n) => (((fx_n, maxidx'), S), TVar(ixn, S)))
          (* NB: T is already reinstantiated *)
        val thaw_reinst = var_fixing |> map (fn ((ixn, T), fx_n) => (((fx_n, maxidx'), T), Var(ixn, T)))
        val th_gen = th |> Thm.generalize (map snd tvar_fixing, map snd var_fixing) maxidx'
        val th_reinst = th_gen 
          |> Thm.instantiate
               (thaw_reinstT |> map (fn (ixnS, T) => pairself certT (TVar ixnS, T)),
                thaw_reinst |> map (fn (ixnT, t) => pairself cert (Var ixnT, t)))
        (* val _ = tracing ("thaw_th of exact_freeze_props_thaw_thms: thaw_reinst is "
          ^commas (thaw_reinst |> map (fn (ixnT, t) =>
             Syntax.string_of_term ctxt2 (Var ixnT) ^ ":=" ^ Syntax.string_of_term ctxt2 t))
          ^"\n  th is "^Display.string_of_thm ctxt2 th
          ^"\n  maxidx' is "^string_of_int maxidx'
          ^"\n  th_gen is "^Display.string_of_thm ctxt2 th_gen
          ^"\n  th_reinst is "^Display.string_of_thm ctxt2 th_gen) *)
      in
        th_reinst
      end
  in
    ((map freeze props, thaw_th), ctxt2)
  end




fun typ_diff (Type(k1, Ts1)) (Type(k2, Ts2)) =
     if k1 = k2 then
       fold2 typ_diff Ts1 Ts2
     else
       cons (Type(k1, Ts2), Type(k2, Ts2))
  | typ_diff T1 T2 =
      if T1 = T2 then
        cons (T1, T2)
      else
        I

fun term_diff (t1 $ t2) (t1' $ t2') = 
      term_diff t1 t1' #> term_diff t2 t2'
  | term_diff (Abs(_, T1, t1)) (Abs(_, T2, t2)) =
      apsnd (typ_diff T1 T2) #> term_diff t1 t2
  | term_diff t1 t2 =
      if t1 = t2 then I
      else apfst (cons (t1, t2))


val mark_eta_redexes = 
 let
   fun mark_eta_redexes_hlp Ts (t1 $ t2) = mark_eta_redexes_hlp Ts t1 $ mark_eta_redexes_hlp Ts t2
     | mark_eta_redexes_hlp Ts (Abs(x, T, t)) =
         (case mark_eta_redexes_hlp (T :: Ts) t of
           (t' as (t'' $ Bound 0)) =>
             if Term.is_dependent t'' then Abs(x, T, t')
             else
               (let
                  val T2 = fastype_of1 (T :: Ts, t')
                  (* NB: subst_bound decreases loose bnos because it is assumed we drop the lambda,
                      so we take the indirect route via reabstracting a fresh Free instead *)
                  val freshX = Free("x_"^string_of_int (serial ()), T)
                in
                  Const("etaredex", T --> T2)
                  $ Term.lambda_name (x, freshX) (Term.incr_boundvars 1
                      (subst_bound (Const("etavar", T --> T) $ freshX, t')))
                end)
         | t' => Abs(x, T, t'))
     | mark_eta_redexes_hlp Ts x = x
 in
   mark_eta_redexes_hlp []
 end

fun protect_eta_redexes_cv ctxt ct =
  case Thm.term_of ct of
    _ $ _ => ct |> Conv.comb_conv (protect_eta_redexes_cv ctxt)
  | Abs(_, _, _) => ct |>
      (Conv.abs_conv (fn (_, ctxt2) => protect_eta_redexes_cv ctxt2) ctxt
      then_conv (fn ct =>
        case Thm.term_of ct of
          Abs(_, _, t' $ Bound 0) =>
            if Term.is_dependent t' then Conv.all_conv ct
            else
              (ctxt, ct) |-> Conv.abs_conv (fn _ =>
                  Conv.arg_conv (Conv.rewr_conv (Thm.symmetric Data.protect_eta_redex_var_def)))
        | _ => Conv.all_conv ct))
  | _ => Conv.all_conv ct

val unprotect_eta_redexes =
  Conv.bottom_conv (fn _ => Conv.try_conv (Conv.rewr_conv Data.protect_eta_redex_var_def))

fun protected_eta_redexes_thmmap ctxt f th =
  let
    val th_prot = Conv.fconv_rule (protect_eta_redexes_cv ctxt) th
    val th_prot' = f th_prot
  in
    Conv.fconv_rule (unprotect_eta_redexes ctxt) th_prot'
  end




val beta_eta_convert = Conv.fconv_rule Drule.beta_eta_conversion
val beta_convert = Conv.fconv_rule (Thm.beta_conversion true)
val eta_convert = Conv.fconv_rule Thm.eta_conversion
val beta_eta_long_convert = Conv.fconv_rule Thm.eta_long_conversion

val beta_norm_cterm = Thm.beta_conversion true #> Thm.rhs_of


fun instnorm_thm_with_env ctxt env th =
  let
    val vars = Term.add_vars (prop_of th) [] |> map Var
    val tvars = Term.add_tvars (prop_of th) [] |> map TVar
    val thy = Proof_Context.theory_of ctxt
    val normT = Envir.norm_type (Envir.type_env env)
  in
    th
    |> Thm.instantiate (
         tvars |> map (fn v => (v, normT v) |> pairself (ctyp_of thy)),
         vars |> map (fn (v as Var(ixn, T)) => (Var(ixn, normT T), Envir.norm_term env v) |> pairself (cterm_of thy)))
    |> beta_convert
  end

exception InternalInterrupt


 (* (matcher-fun, maker-fun) sollen ueberlappungsfrei sein ! *)
 (* factorization into (primary object, other input objects, output objects) *)
type analyzer_ty =
  (term -> (term * term list * term list) option) * (theory -> term * term list * term list -> term) *
  (cterm -> (cterm * cterm list * cterm list) option)



fun pack_pobj_iobjs pobj iobjs = Term.list_comb (Free("packed_pobj_iobjs", Term.dummyT), pobj :: iobjs)
fun dummy_comb ts = Term.list_comb (Free("dummy", Term.dummyT), ts)





(* TODO: proper solution uses a bijection between certain Frees and bindings.
     scopify then generates concealed bindings *)
fun name_from_const_or_free head_term =
  case head_term of
    Const(n, _) => n
  | Free(n, _) => n
  | _ => error "name_from_const_or_free: head_term not a Constant or Free"
val name_suffix = "_name"
fun name_from_const_or_free_unsuffix head_term =
  let val n0 = (name_from_const_or_free head_term)
  in
    case try (unsuffix name_suffix) n0 of
      SOME x => x
    | _ => error ("name_from_const_or_free_unpostfix: no \"_name\" postfix in "^quote n0)
  end
fun name_from_const_or_free_perhaps_unsuffix head_term =
  case try name_from_const_or_free_unsuffix head_term of
    SOME n => n
  | _ => name_from_const_or_free head_term




 (* proof certification with passing down of ctxt and global instantiation and on-the-fly application of the instantiation *)


(* (#input args (not counting the primary argument), #output args) *)
type mode = int * int
type frule_id = int
datatype frule_kind = ImplicitFRule | ExplicitFRule
datatype depgraph_node = Judgement | FRule of frule_id

fun is_synth_mode (ninput, noutput) = (noutput > 0)
fun synth_objs_from_sec_objs mode sec_objs = drop (fst mode) sec_objs


type run_state = {
    outer_ctxt: Proof.context,
    env : Envir.env,
    (* The delayed unifs are implicit assumptions t1 == t2 (fully lambda lifted into the outer_ctxt)
       during the derivation, which were non-patterns at the time their unification was tried.
       The bool signifies whether the unification problem has been solved by now, due to a reconsideration
       after variables in the problem became instantiated.
       Delayed unifications remain hyps in the proofs during the derivation and are discharged after
       the derivation is complete. *)
    delayed_unifs: ((term * term) * bool) list,  
    (* constraints are implicit assumptions during the derivation that are always exported wrt. outer_ctxt *)
    constraints: term list,
    fo_vars: indexname list
  }

(* TODO(semantics): besser NormalJud in FactJud, RecJud aufteilen? *)
datatype judgement_kind = NormalJud | CollJud | ProcJud | LthyTransfJud
datatype allow_inconsis = AllowInconsis | DisallowInconsis
(* head_term has to be in most general form *)
type judgements_type = (analyzer_ty * term * mode * judgement_kind *
  (thm * string * string option) option * string option * allow_inconsis) Symtab.table
  (* fst = running_expl_frules,   snd = running_on_thy_lvl *)
type run_info_ty = bool * int * run_state option







(* use proofterms to allow unification variables in assumptions
   regarded modulo beta, but not modulo extra computational rules *)
(* TODO: proofterm constructor for normalization with computational rules *)
(* NB: thm in ThmPrf can have hyps (if it is a local ground rule) which are discharged in proof
     replay of surrounding ImpI *)
datatype proofterm = Assumption of term | AllI of (string * typ) * proofterm | ImpI of term * proofterm
  | ThmPrf of thm * ((indexname * sort) * typ) list * ((indexname * typ) * term) list
  | MP of proofterm * proofterm | AllE of proofterm * term


(* proofterm with its proposition and open assumptions *)
datatype proof_pack = ProofPack of term * proofterm * term list   

fun prop_of_proofp (ProofPack (prop, _, _)) = prop
fun proof_of_proofp (ProofPack (_, proof, _)) = proof
fun assms_of_proofp (ProofPack (_, _, assms)) = assms

fun map_prop_of_proofp f (ProofPack (prop, proof, assms)) =
  ProofPack (f prop, proof, assms)

(* some of the prf combinators need to access the env in the run_state of the context, so they are defined later when
   context manipulation functions are available *)




(* DirectRules are freshified before their applications, whereas unification
   variables in LocalRules are shared in the derivation.
   LocalRules can be quantified and those quantified variables get instantiated with fresh unification
   variables before rule matching *)
datatype rule_ty = DirectRule of thm | LocalRule of proof_pack




  (* stands for an arbitrary judgement, i.e. depends on all available
     judgements *)
val arb_judgement = "ARB_JUDGEMENT"
val arb_head_term = Free(arb_judgement, Term.dummyT --> @{typ prop})


  (* werden spaeter noch explizit hinzugefuegt, deshalb nicht in den
     initialen Datenstrukturen vorhanden *)
val define_jud = "define_jud"
val note_jud = "note_jud"
val concat_names_jud = "concat_names_jud"
val fresh_unifvar_jud = "fresh_unifvar_jud"
val unify_jud = "unify_jud"
val constraint_jud = "constraint_jud"
val foconstraint_jud = "foconstraint_jud"

(* define, note, concat_names are added in setup *)
val judgements_start : judgements_type =
  let
    val head = Free(arb_judgement^"_DUMMY_POBJ", Term.dummyT)
    val chead = cterm_of @{theory} head
    fun matcher t =
      case head_of t of
        Free(n, _) =>
          if n = arb_judgement then
            SOME (head, [], [])
          else NONE
      | _ => NONE
    fun cmatcher ct =
      case matcher (Thm.term_of ct) of
        SOME _ => SOME (chead, [], [])
      | NONE => NONE
    val maker = (fn _ => error "tried to assemble arb judgement")
    val mode = (0, 0)
  in
    Symtab.empty
    |> Symtab.update (arb_judgement, ((matcher, maker, cmatcher), arb_head_term, mode, NormalJud, NONE, NONE, DisallowInconsis))
  end
val depgraph_start = Graph.empty
  |> Graph.new_node (arb_judgement, Judgement)


fun get_frule_id depgraph key = 
  case Graph.get_node depgraph key of
    FRule id => SOME id
  | _ => NONE
fun calc_frule_key id = "FRule" ^ Library.string_of_int id
fun get_frule frules id =
  case Inttab.lookup frules id of
    SOME (frule, _, _, _, _) => frule
  | NONE => error "get_frule"





fun gen_decompose_judgement term_to_jud (judgements : judgements_type) string_of_term prop =
  (* TODO(opt): eta normalisierung immer unnoetig weil Judgementapplikationen rigide Atome sind? *)
  case Net.match_term term_to_jud (Envir.eta_contract prop) of
    [jid] =>
      (case Symtab.lookup judgements jid of
        SOME ((matcher, _, _), _, _, _, _, _, _) =>
          (case matcher prop of
            SOME args => SOME (jid, args)
          | NONE => error ("decompose_judgement: matcher failed on "^string_of_term prop))
      | NONE => error ("decompose_judgement: jid "^quote jid^" is not valid"))
  | _ => NONE

(* NB: we index local rules under their conclusion in the *present* instantiation (which
   might be more partial than the instantiation in the current context, but in the only
   relevant call from add_assm_terms_internal this is not the case). If it gets more
   instantiated later on, the rule matching will only be less precise.
   Local rules can get coinciding conclusions when unification variables in them are further
   instantiated. In that case they were always in the same Net-Leaf anyway and are always retrieved together *)
fun rule_net_index (judgements : judgements_type) term_to_jud (rule, prior) =
  (case rule of DirectRule th => prop_of th | LocalRule prf => prop_of_proofp prf)
  |> Logic.strip_imp_concl
  |> gen_decompose_judgement term_to_jud judgements (fn _ => "<term (no term printer)>")
  |> Option.map (fn (_, (pobj, iobjs, oobjs)) => pack_pobj_iobjs pobj iobjs)
  |> the_list

(* NB: eq_for_net should only be called on theory merge, because otherwise don't use the
      Item_Net2.{member, member_match, remove, merge} functions.
      If we ever need one of those, this needs a current ctxt parameter (and Item_Net2 needs
      to be generalized accordingly) and should then be
         (rule1, rule2) |> pairself prop_of_rule ctxt |> (op aconv)
      (note that prop_of_rule norms LocalRules wrt their current instantiation in ctxt) *)
fun eq_for_net ((rule1, _), (rule2, _)) =
  case rule1 of
    DirectRule th1 =>
      (case rule2 of
        DirectRule th2 => Thm.eq_thm_prop (th1, th2)
      | LocalRule _ => error "internal error: eq_for_net was on a local rule")
  | LocalRule _ => error "internal error: eq_for_net was on a local rule"




local
  fun scc_err string_of_thm scc_frules victim_frule mod_jud evil_frules badpath =
    let
      fun nice_cat to_str thms =
        cat_lines (map (fn th => "  *  "^to_str th^"\n") thms)
    in
      error
        ("gen_add_frule: resulting dependency graph would exhibit a scc of frules\n\n"
           ^nice_cat string_of_thm scc_frules
           ^"\n\ncontaining \n\n"^string_of_thm victim_frule
           ^"\n\nwhich depends on judgement "^quote mod_jud
           ^" and is therefore affected by the (transitive) modification of this judgement by frules\n\n\n"
           ^nice_cat string_of_thm evil_frules
           ^"\n\n\nvia path\n\n\n"
           ^nice_cat I badpath
           ^"\n\n\nin this scc. This might make saturation in phases impossible!")
    end
in
  fun check_depgraph string_of_thm frules depgraph = () |> fold (fn scc =>
       fold (fn key =>
           case Graph.get_node depgraph key of
             FRule id =>
              Graph.Keys.fold (fn key' =>
                  case Graph.get_node depgraph key' of
                    FRule _ => I
                    (* TODO(brittle): nutzt aus das frule -> judgement Abhaengigkeiten
                        immer bedeuten das das Judgement in einem Goal vorkommt und nicht
                        etwa nur in einem Head *)
                  | _ =>
                      (* judgement key' is therefore contained in a premise of frule id
                         because of the dependency graph invariant *)
                      let
                        val trans_deps = Graph.all_succs depgraph [key']
                        val inter = Library.inter (op =) trans_deps scc
                      in
                        if null inter then I
                        else 
                          let
                            val fstinter = hd inter
                            val badpath = Graph.irreducible_paths depgraph (key', fstinter)
                              |> hd |> map (fn key2 =>
                                case get_frule_id depgraph key2 of
                                  SOME rid => "frule   "^string_of_thm (get_frule frules rid)
                                | NONE => "judgement   "^quote key2)
                            val scc_frules = scc
                              |> map_filter (get_frule_id depgraph #> Option.map (get_frule frules))
                            val evil_frules = inter
                              |> map_filter (get_frule_id depgraph #> Option.map (get_frule frules))
                          in scc_err string_of_thm scc_frules (get_frule frules id) key' evil_frules badpath end
                      end)
                (Graph.imm_succs depgraph key)
           | _ => I)
         scc)
     (Graph.strong_conn depgraph)
end



type ruledata_type = {
    (* net for backward rules indexed by non-wellformed term combination  pack_pobj_iobjs pobj iobjs
       when retrieving backward rules are sorted by given priority first, 
       then by reverse order of their addition (i.e. latest additions get priority) *)
    rules: ((rule_ty * int) Item_Net2.T) Symtab.table,
    judgements: judgements_type,
    term_to_jud: string Net.net,
    assms: term list, (* TODO(refactor?): better move assms to run_state? but they are not threaded linearly ... *)

      (* synthesis procedures indexed by the judgement name
         if invoked in frule-applications the current theory
         is only available via the generic context.
         possibly results in an updated run state (esp. new constraints, delayed unification problems).
         in the official interface such syn_procs are called general syn_procs *)
    syn_procs: (string * (Proof.context -> (Proof.context -> string -> (proof_pack * term list) * run_state option)
      -> (term * term list * term list) -> (proof_pack * term list) * run_state option)) Symtab.table,
    comp_rules: simpset option,
    trace_depth: int * int,
    trace: ((unit -> term) list) * ((unit -> string) list),

    facts: thm Net.net,
      (* facts indexed by non-wellformed term combination  pack_pobj_iobjs pobj iobjs *)
    facts_lhs_idx: thm Net.net,
      (* konservative Approx der Abhaengigkeiten zwischen Judgements und frules
         enthaelt auch die Abhaengigkeiten, die durch (aus bestehenden frules)
         generierbare brules induziert werden *)
    depgraph: depgraph_node Graph.T,
      (* frules indexed by their id   contains the facts the frule has already been applied on, concatenated in the net *)
      (* the string list is the list of judgements of the heads, the bool toggles tracing *)
    frules: (thm * frule_kind * string list * term list Net.net * bool) Inttab.table,
      (* net contains a forward rule reference, indexed by all of its heads respectively;
         the zero-based position of the head which indexes is also stored *)
    frules_hdidx: (frule_id * int) Net.net,
      (* frules indexed by the judgements of the facts they generate *)
    frules_factgen: frule_id Net.net,
      (* *generated* brules, indexed by their conclusion, for overlap checking
         (overlap with static brules may be wanted) *)
    gen_brule_concls: thm Net.net,
    
      (* indexed by judgement *)
    lthy_transforms: (string * ((cterm * cterm list) -> local_theory -> (thm * cterm list) * local_theory)) Symtab.table,
    lthy_transform_log: string list,
    
    (* new_facts indexed by their judgement   *)
    new_facts: thm list Symtab.table,

      (* constraint {propagation, simplification} rules indexed by all of their heads respectively;
         the zero-based position of the head which indexes is also stored *)
    constraint_propag_rules_hdidx: (thm * int) Net.net,
    constraint_simp_rules_hdidx: (thm * int) Net.net
  }

val empty_ruledata : ruledata_type = {
     rules = Symtab.empty, judgements = judgements_start,
     term_to_jud = Net.empty, assms = [],
     syn_procs = Symtab.empty,
     comp_rules = NONE, trace_depth = (3, 3), trace=([], []),
     facts = Net.empty, facts_lhs_idx = Net.empty,
     depgraph = depgraph_start, frules = Inttab.empty,
     frules_hdidx = Net.empty, frules_factgen = Net.empty,
     gen_brule_concls = Net.empty,
     lthy_transforms = Symtab.empty, lthy_transform_log = [],
     new_facts = Symtab.empty,
     constraint_propag_rules_hdidx = Net.empty,
     constraint_simp_rules_hdidx = Net.empty
   }

val base_scope = 0
val init_run_info = (false, 0, NONE)

(* Daten aus der Hintergrundtheorie werden bei init von Beweiskontexten
   automatisch uebernommen *)
structure RuleData = Generic_Data(
  type T = int * ruledata_type Inttab.table * run_info_ty
  val empty = (base_scope, Inttab.empty |> Inttab.update_new (base_scope, empty_ruledata), init_run_info)
  val extend = I

  fun merge ((scope1, tab1, run_info1) : T, (scope2, tab2, run_info2) : T) =
    let
      val _ =
        if scope1 = base_scope andalso scope2 = base_scope then ()
        else
          error ("RuleData.merge: scopes are nontrivial")

      fun merge_ruledata (data1 : ruledata_type, data2 : ruledata_type) =
        let
          val {rules=rules1, judgements=judgements1, term_to_jud=term_to_jud1, assms=assms1, syn_procs=syn_procs1,
            comp_rules=comp_rules1, trace_depth=trace_depth1, trace=trace1, facts=facts1, facts_lhs_idx=facts_lhs_idx1,
            depgraph=depgraph1, frules=frules1, frules_hdidx=frules_hdidx1, frules_factgen=frules_factgen1,
            gen_brule_concls=gen_brule_concls1, lthy_transforms=lthy_transforms1, lthy_transform_log=lthy_transform_log1,
            new_facts=new_facts1, constraint_propag_rules_hdidx=constraint_propag_rules_hdidx1,
            constraint_simp_rules_hdidx=constraint_simp_rules_hdidx1} = data1
          val {rules=rules2, judgements=judgements2, term_to_jud=term_to_jud2, assms=assms2, syn_procs=syn_procs2,
            comp_rules=comp_rules2, trace_depth=trace_depth2, trace=trace2,
            facts=facts2, facts_lhs_idx=facts_lhs_idx2, depgraph=depgraph2, frules=frules2, frules_hdidx=frules_hdidx2,
            frules_factgen=frules_factgen2, gen_brule_concls=gen_brule_concls2, lthy_transforms=lthy_transforms2,
            lthy_transform_log=lthy_transform_log2, new_facts=new_facts2,
            constraint_propag_rules_hdidx=constraint_propag_rules_hdidx2,
            constraint_simp_rules_hdidx=constraint_simp_rules_hdidx2} = data2
          val judgements' : judgements_type = Symtab.merge (K true) (judgements1, judgements2)
          val term_to_jud' = Net.merge (op =) (term_to_jud1, term_to_jud2)
          val frules' = frules1 |> Inttab.fold (fn (id, (th, kind, headjuds, applied_to_facts, traced)) =>
              Inttab.map_default (id, (th, kind, headjuds, applied_to_facts, traced)) (fn (th2, kind2, headjuds2, applied_to_facts2, traced2) =>
                if Thm.eq_thm_prop (th, th2) andalso kind = kind2 andalso headjuds = headjuds2 then
                  (th, kind, headjuds,
                   Net.merge (fn (fs1, fs2) => forall2 (curry (op aconv)) fs1 fs2) (applied_to_facts, applied_to_facts2),
                   traced2)
                else
                  error ("RuleData.merge: frule with same id "^string_of_int id^" but different proposition or kind or headjuds\n"
                    ^Display.string_of_thm_without_context th)))
            frules2
          val depgraph' = Graph.merge (op =) (depgraph1, depgraph2)
          val _ = check_depgraph Display.string_of_thm_without_context frules' depgraph'
        in
          {
            rules = rules1 |> Symtab.fold (fn (jud2, net2) =>
                Symtab.map_default (jud2, net2) (fn net =>
                  Item_Net2.merge (rule_net_index judgements' term_to_jud') (net, net2)))
              rules2,
            judgements = judgements', term_to_jud = term_to_jud', assms = [],
            syn_procs = Symtab.merge (K true) (syn_procs1, syn_procs2),
            comp_rules =
              case comp_rules2 of
                NONE => comp_rules1
              | SOME y =>
                  (case comp_rules1 of
                    NONE => SOME y
                  | SOME x => merge_ss (x,y) |> SOME),
            trace_depth = pairself (uncurry Integer.max) ((fst trace_depth1, fst trace_depth2), (snd trace_depth1, snd trace_depth2)),
            trace = ([], []),
            facts = Net.merge Thm.eq_thm_prop (facts1, facts2),
            facts_lhs_idx = Net.merge Thm.eq_thm_prop (facts_lhs_idx1, facts_lhs_idx2),
            depgraph = depgraph', frules = frules', 
            frules_hdidx = Net.merge (op = o pairself fst) (frules_hdidx1, frules_hdidx2),
            frules_factgen = Net.merge (op =) (frules_factgen1, frules_factgen2),
            gen_brule_concls = Net.merge Thm.eq_thm_prop (gen_brule_concls1, gen_brule_concls2),
            lthy_transforms = Symtab.merge (K true) (lthy_transforms1, lthy_transforms2),
            lthy_transform_log = [],
            new_facts = Symtab.empty,
            constraint_propag_rules_hdidx = Net.merge (Thm.eq_thm_prop o pairself fst)
              (constraint_propag_rules_hdidx1, constraint_propag_rules_hdidx2),
            constraint_simp_rules_hdidx = Net.merge (Thm.eq_thm_prop o pairself fst)
              (constraint_simp_rules_hdidx1, constraint_simp_rules_hdidx2)
          }
        end
    in
      (base_scope, Inttab.join (K merge_ruledata) (tab1, tab2), init_run_info)
    end
);

fun map_current_ruledata f = RuleData.map (fn (scope, tab, run_info) =>
    if Inttab.defined tab scope then
      (scope, Inttab.map_entry scope f tab, run_info)
    else
      error "map_current_ruledata: current scope is not defined")

fun get_current_ruledata gctxt =
  let val (scope, tab, _) = RuleData.get gctxt
  in
    case Inttab.lookup tab scope of
      SOME ruledata => ruledata
    | NONE => error "get_current_ruledata: current scope is not defined"
  end
  

fun new_scope inherit_from_base scope' gctxt =
  let
    val (_, tab, run_info) = RuleData.get gctxt
    val ruledata =
      if inherit_from_base then
         (case Inttab.lookup tab base_scope of
           SOME ruledata => ruledata
         | NONE => error "new_scope: base scope undefined")
      else
          empty_ruledata
    val gctxt' = gctxt
      |> RuleData.put (scope', tab |> Inttab.update_new (scope', ruledata), run_info)
  in
    gctxt'
  end

fun set_scope scope = RuleData.map (fn (_, tab, run_info) =>
  (scope, tab, run_info))

fun get_run_info gctxt =
  let val (scope, ruledata, run_info) = RuleData.get gctxt
  in run_info end

fun map_run_info f = RuleData.map (fn (scope, tab, run_info) => (scope, tab, f run_info))

    



fun map_rule_stuff f_rules f_depgraph = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules = f_rules rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = f_depgraph depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_judgement_stuff f_judgements f_term_to_jud f_depgraph = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements = f_judgements judgements,
     term_to_jud = f_term_to_jud term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = f_depgraph depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_term_to_jud f_term_to_jud = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements = judgements,
     term_to_jud = f_term_to_jud term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_assms f_assms = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements = judgements,
     term_to_jud=term_to_jud, assms = f_assms assms, syn_procs=syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_syn_procs f_syn_procs = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements = judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs = f_syn_procs syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_comp_rules f_comp_rules = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules = f_comp_rules comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun set_trace_depth d = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth = d, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_trace f_trace = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth = trace_depth, trace = f_trace trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_fact_stuff f_facts f_facts_lhs_idx f_new_facts = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts = f_facts facts, facts_lhs_idx= f_facts_lhs_idx facts_lhs_idx,
     depgraph=depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log,
     new_facts = f_new_facts new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_frule_stuff f_depgraph f_frules f_frules_hdidx f_frules_factgen = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = f_depgraph depgraph,
     frules = f_frules frules,
     frules_hdidx = f_frules_hdidx frules_hdidx, frules_factgen = f_frules_factgen frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_gen_brule_concls f_gen_brule_concls = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules,
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=f_gen_brule_concls gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_lthy_transforms f_lthy_transforms = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms = f_lthy_transforms lthy_transforms,
     lthy_transform_log = lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})

fun map_lthy_transforms_log f_lthy_transform_log =
  Local_Theory.target (Context.proof_map (map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms = lthy_transforms,
     lthy_transform_log = f_lthy_transform_log lthy_transform_log,
     new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})))

fun map_constraint_propag_rules_hdidx f = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms,
     lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx = f constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx=constraint_simp_rules_hdidx})
 
fun map_constraint_simp_rules_hdidx f = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts,
       constraint_propag_rules_hdidx, constraint_simp_rules_hdidx} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms,
     lthy_transform_log=lthy_transform_log, new_facts=new_facts,
     constraint_propag_rules_hdidx=constraint_propag_rules_hdidx,
     constraint_simp_rules_hdidx = f constraint_simp_rules_hdidx})


fun get_lthy_transform_log lthy =
  let val {lthy_transform_log = log, ...} =
    get_current_ruledata (Context.Proof (Local_Theory.target_of lthy))
  in log end

fun set_running_expl_frules running_expl_frules =
  Local_Theory.target (Context.proof_map (RuleData.map (fn (scope, ruledata, run_info) =>
    (scope, ruledata,
     run_info |> (fn (_, running_on_thy_lvl, run_state) =>
       (running_expl_frules, running_on_thy_lvl, run_state))))))

val get_run_state = get_run_info #> (fn (_, _, run_state) => run_state)
fun get_the_run_state gctxt =
  case get_run_state gctxt of
    SOME st => st
  | NONE => error ("get_the_run_state: no run_state has been set")
fun map_run_state f = map_run_info (fn (running_expl_frules, running_on_thy_lvl, run_state) =>
  (running_expl_frules, running_on_thy_lvl, f run_state))
fun set_run_state st2 = map_run_state (K st2)
fun init_run_state ctxt =
  SOME { outer_ctxt=ctxt, env=Envir.empty (Variable.maxidx_of ctxt),
    delayed_unifs=[], constraints=[], fo_vars=[] }
fun map_constraints_in_run_state f =
  map_run_state (Option.map (fn {outer_ctxt, env, delayed_unifs, constraints, fo_vars} =>
    {outer_ctxt=outer_ctxt, env=env, delayed_unifs=delayed_unifs, constraints=f constraints,
     fo_vars=fo_vars}))
fun map_env_in_run_state f =
  map_run_state (Option.map (fn {outer_ctxt, env, delayed_unifs, constraints, fo_vars} =>
    {outer_ctxt=outer_ctxt, env=f env, delayed_unifs=delayed_unifs, constraints=constraints,
    fo_vars=fo_vars}))
fun map_fovars_in_run_state f =
  map_run_state (Option.map (fn {outer_ctxt, env, delayed_unifs, constraints, fo_vars} =>
    {outer_ctxt=outer_ctxt, env=env, delayed_unifs=delayed_unifs, constraints=constraints,
     fo_vars=f fo_vars}))
fun map_delayed_unifs_in_run_state f =
  map_run_state (Option.map (fn {outer_ctxt, env, delayed_unifs, constraints, fo_vars} =>
    {outer_ctxt=outer_ctxt, env=env, delayed_unifs=f delayed_unifs, constraints=constraints,
    fo_vars=fo_vars}))
fun get_the_env_in_run_state ctxt = Context.Proof ctxt |> get_the_run_state |> (fn { env, ... } => env)
fun get_constraints_in_run_state ctxt = Context.Proof ctxt |> get_the_run_state
  |> (fn { constraints, ... } => constraints)
fun get_delayed_unifs_in_run_state ctxt = Context.Proof ctxt |> get_the_run_state
  |> (fn { delayed_unifs, ... } => delayed_unifs)
fun norm_with_env_in_run_state ctxt t =
  Envir.norm_term (get_the_env_in_run_state ctxt) t
  handle TYPE (msg, Ts, ts) =>
    raise TYPE ("exception while norming "^Syntax.string_of_term ctxt t^":  "^msg, Ts, ts)
    
  


fun str_of_normed_term ctxt = Syntax.string_of_term ctxt o norm_with_env_in_run_state ctxt

fun get_running_expl_frules ctxt =
  if can Local_Theory.assert ctxt then
     let val (_, _, (running_expl_frules, _, _)) =
       RuleData.get (Context.Proof (Local_Theory.target_of ctxt))
     in running_expl_frules end
  else
    false


fun update_running_on_thy push thy =
  thy |> Context.theory_map (RuleData.map (fn (scope, ruledata, run_info) =>
    (scope, ruledata,
     run_info |> (fn (running_expl_frules, running_on_thy_lvl, run_state) =>
       let
         val running_on_thy_lvl' =
           if push then running_on_thy_lvl + 1
           else if running_on_thy_lvl = 0 then error "update_running_on_thy: pop not possible"
           else running_on_thy_lvl - 1
       in 
         (running_expl_frules, running_on_thy_lvl', run_state)
       end))))
val push_running_on_thy = update_running_on_thy true
val pop_running_on_thy = update_running_on_thy false

fun is_running_on_thy ctxt =
  let val (_, _, (_, running_on_thy_lvl, _)) =
    RuleData.get (Context.Theory (Proof_Context.theory_of ctxt))
  in running_on_thy_lvl > 0 end




(* with new semantics, e.g. as in 11d9c2768729 *)
fun add_non_pervasive_declaration decl lthy =
  Local_Theory.declaration {syntax=false, pervasive=false} decl lthy
  (* let
    val lthy2 = lthy
      |> Local_Theory.declaration false decl
          (* decl on identity morphism applied to aux ctxt of lthy *)
      |> Context.proof_map (Morphism.form decl)
  in lthy2 end *)

fun map_pot_lthy decl ctxt =
  if is_running_on_thy ctxt then
    ctxt |> Proof_Context.theory_of
    |> Context.theory_map (Morphism.form decl)
    (* TODO(opt): init_global teuer  *)
    |> Proof_Context.init_global
  else if get_running_expl_frules ctxt then (* ctxt is a lthy *)
    ctxt |> add_non_pervasive_declaration decl
  else
    ctxt |> Context.proof_map (Morphism.form decl)

fun run_on_ctxt run gctxt =
  case gctxt of
    Context.Proof ctxt => ctxt |> run |> Context.Proof
  | Context.Theory thy =>
     thy 
     |> push_running_on_thy |> Proof_Context.init_global
     |> run |> Proof_Context.theory_of
     |> pop_running_on_thy |> Context.Theory


fun get_assms gctxt = 
  let val {assms, ...} = get_current_ruledata gctxt
  in assms end
fun set_assms assms = map_assms (K assms)


fun get_judgements (gctxt : Context.generic) : judgements_type =
  let val {judgements, ...} = get_current_ruledata gctxt
  in judgements end
fun get_judgement_head_term gctxt jud = 
  case Symtab.lookup (get_judgements gctxt) jud of
    SOME (_, head_term, _, _, _, _, _) => head_term
  | NONE => error ("get_judgement_head_term: "^quote jud^" is not a judgement")
fun get_judgement_kind gctxt jud : judgement_kind =
  case Symtab.lookup (get_judgements gctxt) jud of
    SOME (_, _, _, kind, _, _, _) => kind
  | NONE => error ("get_judgement_kind: "^quote jud^" is not a judgement")
fun get_judgement_mode gctxt jud : mode =
  case Symtab.lookup (get_judgements gctxt) jud of
    SOME (_, _, mode, _, _, _, _) => mode
  | NONE => error ("get_judgements_mode: "^quote jud^" is not a judgement")
fun get_judgement_higherjud gctxt jud =
  case Symtab.lookup (get_judgements gctxt) jud of
    SOME (_, _, _, _, _, higherjud_opt, _) => higherjud_opt
  | NONE => error ("get_judgements_higherjud: "^quote jud^" is not a judgement")
fun get_judgement_coll_info gctxt jud = 
  case Symtab.lookup (get_judgements gctxt) jud of
    SOME (_, _, _, _, SOME coll_info, _, _) => coll_info
  | _ => error ("get_judgements_coll_info: "^quote jud^" not a collector judgement")
fun get_judgement_inconsis_allowed gctxt jud = 
  case Symtab.lookup (get_judgements gctxt) jud of
    SOME (_, _, _, _, _, _, allow_inconsis) => (allow_inconsis = AllowInconsis)
  | _ => error ("get_judgements_coll_info: "^quote jud^" not a judgement")

fun get_judgement_for_headterm gctxt head_term' =
 Symtab.get_first (fn (jud, (_, head_term, _, _, _, _, _)) =>
     if Pattern.matches (Context.theory_of gctxt) (head_term, head_term') then
       SOME jud
     else NONE)
   (get_judgements gctxt)

fun lookup_judgement_analyzer judgement_graph jud = 
  Symtab.lookup judgement_graph jud
  |> Option.map #1
 
fun decompose_judgement gctxt prop =
  gen_decompose_judgement (#term_to_jud (get_current_ruledata gctxt)) (get_judgements gctxt)
    (fn t => Syntax.string_of_term (Context.proof_of gctxt) t) prop

fun decompose_judgement_cterm gctxt cprop =
  (* TODO(opt): eta normalisierung immer unnoetig weil Judgementapplikationen rigide Atome sind? *)
  case Net.match_term (#term_to_jud (get_current_ruledata gctxt)) (Envir.eta_contract (Thm.term_of cprop)) of
    [jid] =>
      (case Symtab.lookup (get_judgements gctxt) jid of
        SOME ((_, _, cmatcher), _, _, _, _, _, _) =>
          (case cmatcher cprop of
            SOME cargs => SOME (jid, cargs)
          | NONE => error ("decompose_judgement: matcher failed on "^
              Syntax.string_of_term (Context.proof_of gctxt) (Thm.term_of cprop)))
      | NONE => error ("decompose_judgement: jid "^quote jid^" is not valid"))
  | _ => NONE














fun cert_standalone_term_inst thy tenv =
  Vartab.dest tenv |> map (fn (ixn, (T, t)) => (Var (ixn, T), t) |> pairself (cterm_of thy))

(* After matching we check if any unification variables have been instantiated
   and fail then.  *)
fun gen_pattern_matches_opt match ctxt (pat,  term) =
  (let
    val thy = Proof_Context.theory_of ctxt
    val (tyenv, tenv) = match thy (pat, term) (Vartab.empty, Vartab.empty)
    val Tinst = Vartab.dest tyenv |> map (fn (ixn, (sort, ty)) => ((ixn, sort), ty))
    val inst = Vartab.dest tenv |> map (fn (ixn, (T, t)) => ((ixn, Envir.norm_type tyenv T), t))
   in SOME (Tinst, inst) end)
   (* NB: DecompPattern.decompose_match also raises Pattern.MATCH and not a distinct exception *)
  handle Pattern.MATCH => NONE

fun gen_pattern_match_opt match ctxt (pat, term) =
  gen_pattern_matches_opt (fn thy => fn ([pat'], [term']) => match thy (pat', term')) ctxt ([pat], [term])


(* nimmt beta-normale HO-Patterns pat und term an, eta-expandiert on-the-fly
   BTW: Typen von pat, term werden von Pattern.match selbst gematcht *)
val pattern_match_opt = gen_pattern_match_opt Pattern.match
val pattern_matches_opt =
  let fun match thy (pats, terms) = fold (Pattern.match thy) (pats ~~ terms)
  in gen_pattern_matches_opt match end
fun cpattern_matches_opt ctxt (cpats, cterms) =
  ([], []) |> fold (fn (cpat, cterm) => fn inst =>
      let
        val (cpat', cterm') = (cpat, cterm) |> pairself (Thm.instantiate_cterm inst)
        val inst2 = Thm.match (cpat', cterm')
      in (fst inst @ fst inst2, snd inst @ snd inst2) end)
    (cpats ~~ cterms)
  |> SOME
  handle Pattern.MATCH => NONE
fun cpattern_match_opt ctxt (cpat, cterm) = cpattern_matches_opt ctxt ([cpat], [cterm])
  

val decompose_pattern_match_opt = gen_pattern_match_opt DecompPattern.decompose_match

fun cert_inst thy (Tinst, inst) =
  (Tinst |> map ((fn ((ixn, S), T) => (TVar (ixn, S), T)) #> pairself (ctyp_of thy)),
   inst |> map ((fn ((ixn, T), t) => (Var (ixn, T), t)) #> pairself (cterm_of thy)))

fun no_lambdas (t1 $ t2) = no_lambdas t1 andalso no_lambdas t2
  | no_lambdas (Abs(_,_,_)) = false
  | no_lambdas _ = true

(* TODO(opt): decomposing pattern matching mit cterm verwaltung *)
fun cdecompose_pattern_match_opt ctxt (cpat, cterm) =
  (* TODO: nimmt die einfache Semantik von decompose pattern matching an,
      ohne Verschraenkung von first-order und higher-order pattern matching *)
  (* der no_lambdas Fall ist 70-80 Mal haeufiger *)
  if no_lambdas (Thm.term_of cpat) then (* so no implicit eta expansion of cterm can happen *)
    cpattern_match_opt ctxt (cpat, cterm)
  else
    decompose_pattern_match_opt ctxt (Thm.term_of cpat, Thm.term_of cterm)
    |> Option.map (cert_inst (Proof_Context.theory_of ctxt))



fun pattern_fun_to_env_mapper f input env =
  let val (tyenv2, tenv2) = f input (Envir.type_env env, Envir.term_env env)
  in Envir.Envir { maxidx = Envir.maxidx_of env, tenv = tenv2, tyenv = tyenv2 } end

fun envdiff_str ctxt env1 env2 =
  env2 |> Envir.term_env |> fold Vartab.delete (Vartab.keys (Envir.term_env env1))
  |> Vartab.dest |> map (fn (ixn, (T, t)) =>
    Syntax.string_of_term ctxt (Var(ixn, T))^":="^Syntax.string_of_term ctxt t)
  |> commas

(* NB: normalization of term to be matched is necessary now (compared to old metarec) because we don't
     keep terms fully normed per default anymore and Pattern.match does not norm while
     analysing terms.
     We don't norm pattern to avoid deep instantiations on iterating pattern matching
     that would correspond to unification. we therefore also avoid normalization of pattern
     in call sites *)
fun gen_pattern_match_envctxt match norm ctxt (pat, term0) =
  (let 
    val env = get_the_env_in_run_state ctxt

    (* val _ = tracing ("pattern matching: "^Syntax.string_of_term ctxt term0
      ^" against "^Syntax.string_of_term ctxt pat) *)
    val term = norm ctxt term0
    (* val _ = tracing ("  (normed): "^Syntax.string_of_term ctxt term
      ^" against "^Syntax.string_of_term ctxt pat) *)
    val env2 = env
      |> pattern_fun_to_env_mapper (match (Proof_Context.theory_of ctxt))
           (pat, term)
    (* val _ = tracing ("new bindings: "^envdiff_str ctxt env env2) *)
  in
    ctxt |> Context.proof_map (map_env_in_run_state (K env2))
    |> SOME
  end)
  handle Pattern.MATCH => NONE

val pattern_match_envctxt =
  gen_pattern_match_envctxt DecompPattern.match_w_shared_vars norm_with_env_in_run_state
fun pattern_matches_envctxt ctxt (pats, terms) =
  SOME ctxt |> fold (fn (pat, term) => fn ctxt_opt =>
      case ctxt_opt of
        SOME ctxt_ => pattern_match_envctxt ctxt_ (pat, term)
      | NONE => NONE)
    (pats ~~ terms)
(* FIXME: decompose_match with identification of variables that are shared in object and pattern,
     as in pattern_match_envctxt ?! *)
val decompose_pattern_match_envctxt =
  gen_pattern_match_envctxt DecompPattern.decompose_match norm_with_env_in_run_state


fun pattern_unifies thy (t1, t2) =
  (let
    val t1_maxidx = Term.maxidx_term t1 (~1)
      (* disjointify vars *)
    val t2' = Logic.incr_indexes ([], t1_maxidx+1) t2
    val maxidx = ~1 |> fold Term.maxidx_term [t1, t2']
    val (tyenv, maxidx2) = Sign.typ_unify thy (fastype_of t1, fastype_of t2') (Vartab.empty, maxidx)
    val env0 = Envir.Envir {maxidx = maxidx2, tenv = Vartab.empty, tyenv = tyenv}
  in
    (Pattern.unify thy (t1, t2') env0; true)
  end)
    handle Pattern.Unif => false
         | Type.TUNIFY => false

fun unifies thy (t1, t2) =
  let
    val t1_maxidx = Term.maxidx_term t1 (~1)
      (* disjointify vars *)
    val t2' = Logic.incr_indexes ([], t1_maxidx+1) t2
    val maxidx = ~1 |> fold Term.maxidx_term [t1, t2']
    val (tyenv, maxidx2) = Sign.typ_unify thy (fastype_of t1, fastype_of t2') (Vartab.empty, maxidx)
    val env0 = Envir.Envir {maxidx = maxidx2, tenv = Vartab.empty, tyenv = tyenv}
  in
    case Seq.pull (Unify.unifiers (thy, env0, [(t1, t2')])) of
      SOME _ => true
    | NONE => false
  end




exception TryPatUnify of Proof.context * (term * term) * string
exception TryStructUnify of Proof.context * (term * term) * string


fun strip_abss t =
  case t of
    (abs as Abs(n, T, body)) =>
      let
        val (x, fixed_body) = Term.dest_abs (n, T, body)
        val fix = Free(x, T)
      in
        strip_abss fixed_body |> apfst (cons fix)
      end
  | _ => ([], t)

(* TODO(refactor): collect fixed bounds and pass to f. then use this in patternify instead of strip_abss *)
(* t is assumed to be beta normal *)
fun fold_varapps f fixes t =
  case Term.strip_comb t of
    (Var(ixn, T), ts) => f fixes (ixn, T) ts
  | (Abs (n, T, t2), []) =>
      let val (x, fixed_t2) = Term.dest_abs (n, T, t2)
      in fold_varapps f (cons (Free (x, T)) fixes) fixed_t2 end
  | (a, ts) => fold (fold_varapps f fixes) ts


(* term is assumed to be normal wrt env *)
fun patternify ctxt term env =
  env |> fold_varapps (fn fixes => fn v0 => fn ts => fn env_ =>
      case Envir.norm_term env_ (Var v0) of
        Var (ixn, T) =>
          let
            fun fixes_in t = Term.add_frees t [] |> map Free |> inter (op aconv) fixes
            val app_fxs = inter (op aconv) fixes ts
            val (ts', app_fxs') = [] |> fold_map (fn t => fn app_fxs' =>
                if member (op aconv) app_fxs' t then (NONE, app_fxs')
                else if member (op aconv) app_fxs t then (NONE, cons t app_fxs')
                else if subset (op aconv) (fixes_in t, app_fxs) then (NONE, app_fxs')
                else (SOME t, app_fxs'))
              ts
          in
            if ts ~~ ts' |> forall (fn (t, t') => is_some t' orelse member (op aconv) app_fxs t) then
              env_
            else
              let
                (* val tostr = Syntax.string_of_term ctxt
                val _ = tracing ("patternify on varapp "^Syntax.string_of_term ctxt
                    (list_comb (Var (ixn,T), ts)) ^" results in:\n"
                  ^"\n  fixes: "^commas (map tostr fixes)
                  ^"\n  app_fxs: "^commas (map tostr app_fxs)
                  ^"\n  app_fxs': "^commas (map tostr app_fxs')
                  ^"\n  ts': "^commas (map (fn t'_opt =>
                    case t'_opt of SOME t' => tostr t' | NONE => "NONE") ts')) *)
                val T' = map fastype_of app_fxs'
                  ---> map_filter (Option.map fastype_of) ts'
                  ---> drop (length ts) (binder_types T) ---> body_type T
                val (env_2, v') = Envir.genvar (fst ixn) (env_, T')
                val v'_abs = list_comb (v', app_fxs' @ map_filter I ts')
                  |> fold_rev Term.lambda ts
              in
                env_2 |> curry Envir.update ((ixn, T), v'_abs)
              end
          end
      | t => patternify ctxt t env_)
    [] term

(* TODO(feature?): structural (oder sogar auch pattern?) unification modulo ZF-beta
       wobei wir Mischformen wie  ?f(args) ` otherargs  ignorieren
     dazu:
       * die Terme ZF-beta-normalisieren
         (braucht dann metarec typechecking im Kontext des Unifikationsproblems,
          der dann auch als Premissen mitverwaltet werden muss)
         (optional weil wir ja nur ueber contextual discharge von type constraints
          ZF-normale ZF-beta Applikationen einfuehren)
       * Subterme ?f ` args durch ?F(args) ersetzen
       * strukturelle Unifikation durchfuehren
       * wenn ?F instantiiert wurde
         dann setzen wir ?f := (lam x_i : A_i .. . ?F(xs))
         wobei   arg_i :> A_i
         (A_i := {arg_i} hilft nicht viel wenn ?f auch andere Vorkommen hat)

     Hauptanwendungszweck ist Verarbeitung der ZF-Applikationen die durch die
     mengenwertige contextual discharge Regel entstehen. Das :> judgement muss
     also input des metarec functors werden.
*)
fun try_struct_unify ctxt (t1_0, t2_0) env = 
  let
    fun unif_failed () = raise TryStructUnify(ctxt, (t1_0, t2_0), "try_struct_unify: structural unification of "
          ^str_of_normed_term ctxt t1_0^" and "^str_of_normed_term ctxt t2_0^" failed")
    val (t1, t2) = pairself (Envir.norm_term env) (t1_0, t2_0)
  in
    let
      val thy = Proof_Context.theory_of ctxt
      val (tyenv2, maxidx2) = (Envir.type_env env, Envir.maxidx_of env)
        |> Sign.typ_unify thy (fastype_of t1, fastype_of t2) 
      val env2 = Envir.Envir { maxidx = maxidx2, tenv = Envir.term_env env, tyenv = tyenv2 }
      val env3 = StructUnify.unify thy (t1, t2) env2
    in
      SOME env3
    end
      handle
          StructUnify.Unif => unif_failed ()
        | Type.TUNIFY => unif_failed ()
  end

fun try_pat_unify ctxt (t1_0, t2_0) env =
  let
    fun unif_failed () = raise TryPatUnify(ctxt, (t1_0, t2_0), "try_pat_unify: pattern unification of "
          ^str_of_normed_term ctxt t1_0^" and "^str_of_normed_term ctxt t2_0^" failed")
    val (t1_1, t2_1) = pairself (Envir.norm_term env) (t1_0, t2_0)
    (* val relfrees = [] |> fold Term.add_frees [t1_1, t2_1] |> map Free *)
    val (t1_2, t2_2) = (t1_1, t2_1) (* |> pairself (fold Term.lambda relfrees) *)
    val tostr = Syntax.string_of_term ctxt
    (* val _ = tracing ("try_pat_unify on"
      ^"\n  "^tostr t1_1 ^"  lifted to "^tostr t1_2
      ^"\n  "^tostr t2_1 ^"  lifted to "^tostr t2_2) *)
  in
    let
      (* FIXME?: patternify buggy? structural unification seems more useful
           than patternification anyway and they interact badly *)
      val env2 = env (* |> fold (patternify ctxt) [t1_2, t2_2] *)
      val (t1, t2) = pairself (Envir.norm_term env2) (t1_2, t2_2)
      val _ =
        if t1 abeconv t1_2 andalso t2 abeconv t2_2 then ()
        else
          tracing ("try_pat_unify: patternified:"
            ^"\n"^tostr t1_0 ^" = "^ tostr t1_2 ^"  ->  "^tostr t1
            ^"\n"^tostr t2_0 ^" = "^ tostr t2_2 ^"  ->  "^tostr t2)
      val thy = Proof_Context.theory_of ctxt
      val (tyenv3, maxidx3) = (Envir.type_env env2, Envir.maxidx_of env2)
        |> Sign.typ_unify thy (fastype_of t1, fastype_of t2) 
      val env3 = Envir.Envir { maxidx = maxidx3, tenv = Envir.term_env env2, tyenv = tyenv3 }
      val env4 = Pattern.unify thy (t1, t2) env3
    in
      SOME env4
    end
      handle
          Pattern.Pattern => NONE
        | Pattern.Unif => unif_failed ()
        | Type.TUNIFY => unif_failed ()
  end

fun try_solve_delayed_unifs structural ctxt delayed_unifs env =
  let val unif = if structural then try_struct_unify else try_pat_unify
  in
    ([], env)
    |> fold_rev (fn ((t1_, t2_), solved) => fn (ufs, env_) =>
           if solved then
             (cons ((t1_, t2_), true) ufs, env_)
           else
             case unif ctxt (t1_, t2_) env_ of
               SOME env_2 => (cons ((t1_, t2_), true) ufs, env_2)
             | NONE => (cons ((t1_, t2_), false) ufs, env_))
         delayed_unifs
  end






fun check_same_prior l =
  let
    fun aux prio ((_, prio') :: l') = prio = prio' andalso aux prio l'
      | aux prio [] = true
  in
    case l of
      [] => true
    | (_, prio) :: l' => aux prio l'
  end
  

fun order_by_priority l =
  if check_same_prior l then
    l |> map fst
  else
    (* TODO(opt): waere zB insertion sort schneller weil Listen klein? *)
    l |> sort (fn ((_, prio1), (_, prio2)) => rev_order (int_ord (prio1, prio2))) |> map fst





fun prop_of_rule ctxt (DirectRule th) = prop_of th
  | prop_of_rule ctxt (LocalRule proofp) =
      norm_with_env_in_run_state ctxt (prop_of_proofp proofp)





(* TODO(opt):
     macht es Sinn nur die letzten n Regeln-Tracing-Closures auf dem Trace
     zu haben damit die anderen GC'ed werden koennen?
     Aber die werden dann ja von weiter oben im Call-Stack referenziert???
*)
fun gen_add_to_trace trace_sel trace_depth_sel updater newobj =
  Context.proof_map (fn gctxt =>
    let
      val {trace, trace_depth, ...} = get_current_ruledata gctxt
      val my_trace = trace_sel trace
      val my_trace' = newobj :: my_trace |> take (trace_depth_sel trace_depth)
    in
      gctxt |> map_trace (updater my_trace')
    end)
fun add_to_rule_trace rule = gen_add_to_trace fst fst (fn new => apfst (K new)) rule
fun add_to_msg_trace msg = gen_add_to_trace snd snd (fn new => apsnd (K new)) msg


fun compose_err_from_trace ctxt msg =
  let val {trace=(rule_trace, msg_trace), trace_depth=(rule_trace_depth, msg_trace_depth), ...} =
    get_current_ruledata (Context.Proof ctxt)
  in
    (msg
     ^"\n\nrule trace is\n"
       ^cat_lines (take rule_trace_depth rule_trace |> map (fn t_delayed =>
         "\n"^str_of_normed_term ctxt (t_delayed ())))
     ^"\n\nmessage trace is\n"
       ^cat_lines (take msg_trace_depth msg_trace |> map (fn msg => msg ())))
  end
fun err_with_trace ctxt msg = error (compose_err_from_trace ctxt msg)

 (* NB: d.h. suche Fakten die gegen pat *matchen*, weil Fakten Var-frei *)
fun lookup_facts gctxt pat = 
  let val {facts, ...} = get_current_ruledata gctxt
  in
    Net.unify_term facts (Envir.eta_contract pat)
    |> filter (fn fact' => Pattern.matches (Context.theory_of gctxt) (pat, Thm.prop_of fact'))
  end

fun gen_msg_with_facts ctxt msg =
  let val {facts, rules, ...} = get_current_ruledata (Context.Proof ctxt)
  in
    (msg
      ^"\n\n========================================================"
      ^"\ncurrent facts are:\n"
      ^cat_lines (Net.content facts |> map (Display.string_of_thm ctxt))
      ^"\n\n========================================================"
      ^"\ncurrent rules are:\n"
      ^cat_lines (Symtab.dest rules |> maps (snd #> Item_Net2.content
         #> map (fst #> prop_of_rule ctxt #> Syntax.string_of_term ctxt))))
   end
fun err_with_facts ctxt msg = error (gen_msg_with_facts ctxt msg)
fun err_with_trace_and_facts ctxt msg =
  error (gen_msg_with_facts ctxt (compose_err_from_trace ctxt msg))
fun trace_with_facts ctxt msg = tracing (gen_msg_with_facts ctxt msg)



fun wrapper_const name args = 
  let val Ts = map fastype_of args
  in list_comb (Const(name, Ts ---> Data.prf_displayT), args) end

fun prf_to_display_term ctxt prfp =
  let
    val norm = norm_with_env_in_run_state ctxt
    fun normT T = norm (Free("dummy", T)) |> fastype_of

    fun transf (Assumption t) = wrapper_const "Hyp" [norm t]
      | transf (AllI ((x, T), prf)) =
          wrapper_const "AllI" [norm (Free (x, T)), transf prf]
      | transf (ImpI (t, prf)) =
          wrapper_const "ImpI" [norm t, transf prf]
      | transf (ThmPrf (th, Tinst, inst)) =
          let
            val Tinst' = map (apsnd normT) Tinst
            val inst' = map (apfst (apsnd normT) #> apsnd norm) inst
            fun inst_to_str (str1, str2) = str1 ^ " := " ^ str2
            (* val _ = tracing ("prf_to_display_term: instantiating theorem "^Display.string_of_thm ctxt th
              ^" with\n  "
              ^commas ((Tinst' |> map (fn (ixnS, T') => pairself (Syntax.string_of_typ ctxt) (TVar ixnS, T') |> inst_to_str))
                @ (inst' |> map (fn (ixnT, t') => pairself (Syntax.string_of_term ctxt) (Var ixnT, t') |> inst_to_str)))) *)
          in
            wrapper_const "Thm"
            [ th |> Thm.instantiate (Thm.certify_inst (Proof_Context.theory_of ctxt) (Tinst', inst'))
              |> prop_of ]
          end
      | transf (MP (prf1, prf2)) =
          Data.app_prf_displayt (transf prf1) (transf prf2)
      | transf (AllE (prf, t)) =
          Data.app_prf_displayt (transf prf) (norm t)
    fun err msg = err_with_trace ctxt ("prf_to_display_term: failed while transforming proof of "
      ^str_of_normed_term ctxt (prop_of_proofp prfp)
      ^":\n"^msg)

  in
    transf (proof_of_proofp prfp)
    handle
      THM(msg, _, _) => err ("THM: "^msg)
    | TERM(msg, _) => err ("TERM: "^msg)
    | TYPE(msg, _, _) => err ("TYPE: "^msg)
  end






(* TODO(opt): if we combine Thm-proofs, generate a new Thm-proof directly.
   Convert assumption_prf with ground proposition prop to Thm-proof of Thm.assume prop directly. *)

fun genvar_on_run_state name T ctxt =
  let
    val env = get_the_env_in_run_state ctxt
    val (env2, v) = Envir.genvar name (env, T)
    val ctxt2 = ctxt |> Context.proof_map (map_env_in_run_state (K env2))
    (* val _ = tracing ("generated fresh var: "^Syntax.string_of_term ctxt2 v) *)
  in
    (v, ctxt2)
  end


fun fresh_thm_prf th ctxt =
  let
    val env = get_the_env_in_run_state ctxt

    val tvars = Term.add_tvars (prop_of th) [] |> rev
    val (tvars', ctxt2) = ctxt |> fold_map (fn ((n, _), S) =>
        genvar_on_run_state n (Term.aT []) #>> (fn Var(ixn', _) => TVar(ixn', S)))
      tvars

    val tvars_inst = tvars ~~ tvars'
    val instT = (Term_Subst.instantiateT tvars_inst)


    val vars = Term.add_vars (prop_of th) [] |> rev
    val vars' = (vars |> map (apsnd instT))
    val (vars'', ctxt3) = ctxt2 |> fold_map (fn ((n, _), T') =>
      genvar_on_run_state n T') vars'

    (* val _ = tracing ("fresh_thm_prf generated fresh vars: "^
      commas (map (Syntax.string_of_term ctxt3) vars'')) *)

    val vars_inst = vars' ~~ vars''
  in
    (ProofPack (Term_Subst.instantiate (tvars_inst, vars_inst) (prop_of th),
       ThmPrf (th, tvars_inst, vars_inst), []),
     ctxt3)
  end


(* NB: using non-ground theorems requires need that th has to instantiated wrt.
     to the current env !
   since Isabelle resolution (also OF in matching-use) can rename unification variables
     it is easy to make mistakes here *)
fun unsafe_exact_thm_prf th =
  let 
    val prop = prop_of th
    val tvars = Term.add_tvars prop [] |> rev
    val vars = Term.add_vars prop [] |> rev
  in
    ProofPack (prop,
     ThmPrf (th, tvars |> map (fn v => (v, TVar v)), vars |> map (fn v => (v, Var v))),
     Thm.hyps_of th)
  end

fun grnd_exact_thm_prf th =
  let
    val prop = prop_of th
    val tvars = Term.add_tvars prop [] |> rev
    val vars = Term.add_vars prop [] |> rev
    val _ =
      if null vars andalso null tvars then ()
      else error ("grnd_exact_thm_prf on non-ground theorem "
        ^Display.string_of_thm_global (Thm.theory_of_thm th) th)
  in unsafe_exact_thm_prf th end


(* with smart constructors for LCF-style on-construction checking *)
fun assumption_prf t = ProofPack (t, Assumption t, [t])

fun allI_prf ctxt (x, T) (ProofPack (prop, prf, assms)) =
  let
    val env = get_the_env_in_run_state ctxt
    val norm = norm_with_env_in_run_state ctxt
    val normT = Envir.norm_type (Envir.type_env env)
    val free = Free (x, normT T)
  in
    case assms |> find_first (fn assm => member (op =) (Term.add_frees (norm assm) []) (x, normT T)) of
      SOME bad_assm =>
        err_with_trace ctxt ("internal error: fix over "^Syntax.string_of_term ctxt free^" failed: "
          ^"assumption "^str_of_normed_term ctxt bad_assm^" contains it\n"
          ^"proposition is "^str_of_normed_term ctxt prop)
    | NONE =>
        (* NB: we have to norm T and prop because prop can contain matching
           variables of rules that have been instantiated already (and matching
           variables are not lifted over the fixes, so no chance for abstracting then!) *)
        ProofPack (Logic.all free (norm prop), AllI ((x,T), prf), assms)
  end


fun impI_prf ctxt t (ProofPack (prop, prf, assms)) =
  let
    val norm = norm_with_env_in_run_state ctxt
  in 
    ProofPack (Logic.mk_implies (t, prop), ImpI (t, prf), assms |> remove (aconv_norm norm) t)
  end


(* NB: no global substitution of prop1 before implication check *)
fun mp_prf ctxt (prfp1 as ProofPack (prop1, prf1, assms1)) (prfp2 as ProofPack (prop2, prf2, assms2)) =
  let
    val (prop11, prop12) = Logic.dest_implies prop1
      handle TERM _ => err_with_trace ctxt ("internal error: MP failed: prop1 is not an implication "
        ^str_of_normed_term ctxt prop1)
    val norm = norm_with_env_in_run_state ctxt
  in
    if prop11 aconv prop2 orelse aconv_norm norm (prop11, prop2) then
      ProofPack (prop12, MP (prf1, prf2), assms1 |> union (aconv_norm norm) assms2)
    else
      let
        val prf1_t = prf_to_display_term ctxt prfp1
        val prf2_t = prf_to_display_term ctxt prfp2
      in
        err_with_trace ctxt ("internal error: MP failed: premise of prop1 is not the same as prop2:\n"
          ^str_of_normed_term ctxt prop1
          ^"\n"^str_of_normed_term ctxt prop2
          ^"\n\nproofs are\n"
          ^str_of_normed_term ctxt prf1_t
          ^"\nand\n"^str_of_normed_term ctxt prf2_t)
      end
  end

fun mp_rev_prf ctxt proofp1 proofp2 = mp_prf ctxt proofp2 proofp1

(* NB: no global substitution of prop1 before forall check *)
fun allE_prf ctxt (ProofPack (prop, prf, assms)) t =
  case prop of
    Const ("all", _) $ (bodyabs as Abs (_, T, _)) =>
      let
        val T2 = fastype_of t
        val env = get_the_env_in_run_state ctxt
        val normty = Envir.norm_type (Envir.type_env env)
      in
        if T = T2 orelse normty T = normty T2 then
          ProofPack (Term.betapply (bodyabs, t), AllE (prf, t), assms)
        else
          err_with_trace ctxt ("internal error: AllE failed: forall proposition of wrong type "
            ^Syntax.string_of_typ ctxt (normty T)
            ^" and argument has type "^Syntax.string_of_typ ctxt (normty T2)
            ^"\nproposition is: "^str_of_normed_term ctxt prop)
      end
  | _ =>
    err_with_trace ctxt ("internal error: AllE failed: not a (eta-expanded) forall: "
      ^str_of_normed_term ctxt prop)

fun allE_rev_prf ctxt t prf = allE_prf ctxt prf t



fun fresh_proofp_of_rule (DirectRule th) ctxt = fresh_thm_prf th ctxt 
  | fresh_proofp_of_rule (LocalRule proofp) ctxt =  
      let
        val quant_bounds = prop_of_proofp proofp |> Logic.strip_params
        val (quant_vars, ctxt2) = ctxt |> fold_map (fn (n, T) => genvar_on_run_state n T) quant_bounds
        val proofp' = proofp |> fold (allE_rev_prf ctxt2) quant_vars
      in
        (proofp', ctxt2)
      end





fun mp_match_prf (proofp1 as (ProofPack (prop1, _, _))) (proofp2 as (ProofPack (prop2, _, _))) ctxt =
  let
    val (prop11, prop12) = Logic.dest_implies prop1
      handle TERM _ => err_with_trace ctxt ("internal error: MP match failed: prop1 is not an implication "
        ^str_of_normed_term ctxt prop1)
  in
    case pattern_match_envctxt ctxt (prop11, prop2) of
      SOME ctxt2 => (mp_prf ctxt2 proofp1 proofp2, ctxt2)
    | NONE => 
        err_with_trace ctxt ("internal error: MP match failed: failed to match:\n"
          ^str_of_normed_term ctxt prop11
          ^"\nagainst  "^str_of_normed_term ctxt prop2)
  end
fun mps_match_prf prf prfs ctxt =
  (prf, ctxt) |> fold (fn p => fn (prf_, ctxt_) => mp_match_prf prf_ p ctxt_) prfs

fun mps_match_on_freshthm_prf th prfs ctxt =
  let
    val (prf1, ctxt2) = fresh_thm_prf th ctxt
    val (res, ctxt3) = mps_match_prf prf1 prfs ctxt2
  in
    (res, ctxt3)
  end

fun inst_match_on_freshthm_prf th inst ctxt =
  let
    val (prf, ctxt2) = fresh_thm_prf th ctxt
    val vars = Term.add_vars (prop_of_proofp prf) [] |> rev |> map Var
  in
    case pattern_matches_envctxt ctxt2
      (vars, (inst ~~ vars |> map (fn (t_opt, var) => the_default var t_opt)))
    of
      SOME ctxt3 => (prf, ctxt3)
    | NONE =>
        err_with_trace ctxt2 ("internal error: inst_match_on_freshthm_prf failed on "
          ^Display.string_of_thm ctxt2 th)
  end


val combination_thm = Thm.axiom @{theory} "Pure.combination"
val reflexive_thm = Thm.axiom @{theory} "Pure.reflexive"

fun combination_prf prf1 prf2 ctxt =
  mps_match_on_freshthm_prf combination_thm [prf1, prf2] ctxt

fun reflexive_prf t =
  inst_match_on_freshthm_prf reflexive_thm [SOME t]

fun fun_cong_prf prf t ctxt =
  let val (refl_prf, ctxt2) = reflexive_prf t ctxt
  in combination_prf prf refl_prf ctxt2 end




(* TODO(opt): sharing of prf in resulting proofterms *)
fun conj_extr_prfs prf ctxt =
  let val prop = prop_of_proofp prf
  in
    case try Logic.dest_conjunction prop of
      NONE => ([(prop, prf)], ctxt)
    | SOME (prop1, prop2) =>
        let
          val (prf1, ctxt2) = mps_match_on_freshthm_prf Conjunction.conjunctionD1 [prf] ctxt
          val (res1, ctxt3) = conj_extr_prfs prf1 ctxt2
          val (prf2, ctxt4) = mps_match_on_freshthm_prf Conjunction.conjunctionD2 [prf] ctxt3
          val (res2, ctxt5) = conj_extr_prfs prf2 ctxt4
        in
          (res1 @ res2, ctxt5)
        end
  end

fun conj_concl_extr_prfs prf ctxt =
  let
    val prems = Logic.strip_imp_prems (prop_of_proofp prf)
    val concl_prf = prf |> fold (mp_rev_prf ctxt o assumption_prf) prems
    val (concl_ress, ctxt2) = conj_extr_prfs concl_prf ctxt
    val disch_prf = fold_rev (impI_prf ctxt2) prems
  in
    (map (apsnd disch_prf) concl_ress, ctxt2)
  end



fun fold_terms_prf f ctxt prfp =
  let
    fun foldp (Assumption t) = f (norm_with_env_in_run_state ctxt t)
      | foldp (AllI ((x, T), prf)) = f (Free(x, T)) #> foldp prf
      | foldp (ImpI (t, prf)) =
          f (norm_with_env_in_run_state ctxt t) #> foldp prf
      | foldp (ThmPrf (th, Tinst, inst)) =
          fold (f o norm_with_env_in_run_state ctxt)
            (map (Logic.mk_type o snd) Tinst @ map snd inst)
      | foldp (MP (prf1, prf2)) =
          foldp prf1 #> foldp prf2
      | foldp (AllE (prf, t)) =
          foldp prf #> f (norm_with_env_in_run_state ctxt t)
  in
    f (norm_with_env_in_run_state ctxt (prop_of_proofp prfp))
    #> foldp (proof_of_proofp prfp)
  end

val add_vars_prf = fold_terms_prf Term.add_vars
val add_tvars_prf = fold_terms_prf Term.add_tvars
fun declare_prf prfp ctxt = fold_terms_prf Variable.declare_term ctxt prfp ctxt



(* TODO(opt): sharing of certified terms as they are shared in env *)
fun replay_prf ctxt prfp =
  let
    val prf = proof_of_proofp prfp
    val cert = cterm_of (Proof_Context.theory_of ctxt)
    val certT = ctyp_of (Proof_Context.theory_of ctxt)

    val vars = add_vars_prf ctxt prfp []
    val tvars = add_tvars_prf ctxt prfp []
    val ctxt2 = ctxt |> declare_prf prfp

    (* NB: we avoid fx_n ending with "_", to avoid problem with
       Name.clean_index generating unexpecting variables
       for the fixed frees in Term_Subst.generalize in Thm.generalize *)
    val ((fxvar_ns, fxTvar_ns), _) = ctxt2 |> Variable.set_body false
      |> Variable.variant_fixes (map (fst #> fst #> Name.clean) vars)
      ||>> Variable.variant_fixes (map (fst #> fst #> Name.clean) tvars)
      ||> Variable.restore_body ctxt2
    val var_fixing = vars ~~ fxvar_ns
    val tvar_fixing = tvars ~~ fxTvar_ns
    val fxenv = Envir.merge (get_the_env_in_run_state ctxt2,
      Envir.Envir { maxidx = 0, tenv = Vartab.empty,
        tyenv = Vartab.empty |> fold (fn ((ixn, S), fx_n) =>
          Vartab.update_new (ixn, (S, TFree(fx_n, S)))) tvar_fixing }
      (* FIXME?: normalize T wrt tvar fixing env?
         might be fine because of deep normalization in Envir.norm_term *)
      |> fold (fn ((ixn, T), fx_n) => curry Envir.update ((ixn, T), (Free (fx_n, T)))) var_fixing)

    val certnorm = cert o Envir.norm_term fxenv
    val normT = Envir.norm_type (Envir.type_env fxenv)
    val certnormT = certT o normT

    fun replay (Assumption t) = Thm.assume (certnorm t)
      | replay (AllI ((x, T), prf)) =
        let val th = replay prf
        in Thm.forall_intr (certnorm (Free (x, T))) th end
      | replay (ImpI (t, prf)) =
          let val th = replay prf
          in Thm.implies_intr (certnorm t) th end
      | replay (ThmPrf (th, Tinst, inst)) =
          let
            val cTinst = Tinst |> map (fn (v, T) => (certT (TVar v), certnormT T))
            val cinst = inst |> map (fn (v, t) => (cert (Var (apsnd normT v)), certnorm t))
          in
            Thm.instantiate (cTinst, cinst) th |> beta_convert
          end
      | replay (MP (prf1, prf2)) =
         let
           (* TODO(opt): beta conversion necessary here if done at Assumption, ImpI, AllE proof replay? *)
           val th1 = replay prf1 |> beta_convert
           val th2 = replay prf2 |> beta_convert
         in
           Thm.implies_elim th1 th2
         end
      | replay (AllE (prf, t)) =
          let
            val th = replay prf
          in
            Thm.forall_elim (certnorm t) th |> beta_convert
          end
            

    val th_fxd = replay prf
      handle THM(msg, _, ths) => err_with_trace ctxt2 ("replay_prf: exception while replaying proof of "
        ^str_of_normed_term ctxt2 (prop_of_proofp prfp)
        ^":\n"^msg
        ^"\n"^cat_lines (map (Display.string_of_thm ctxt2) ths)
        ^"\n\nproof is\n"
        ^str_of_normed_term ctxt2 (prf_to_display_term ctxt2 prfp))

    val maxidx' = Thm.maxidx_of th_fxd + 1
    val T_reinst = tvar_fixing |> map (fn ((ixn, S), fx_n) => (((fx_n, maxidx'), S), TVar(ixn, S)))
    val reinstT = Term_Subst.instantiateT T_reinst

    (* NB: if th_fxd has hyps containing tvar_fixing or var_fixing we get the
         usual generaliziation exception here *)
    val th = th_fxd
      |> Thm.generalize (map snd tvar_fixing, map snd var_fixing) maxidx'
      |> Thm.instantiate
           (T_reinst |> map (fn (ixnS, T') => pairself certT (TVar ixnS, T')),
             (* NB: T is already reinstantiated *)
            var_fixing |> map (fn ((ixn, T), fx_n) => pairself cert (Var((fx_n, maxidx'), T), Var(ixn, T))))
      handle THM(msg, _, _) => err_with_trace ctxt2 ("replay_prf: exception while instantiating replayed proof of "
        ^str_of_normed_term ctxt2 (prop_of_proofp prfp)
        ^":\n"^msg
        ^"\n\ngeneralizing over: "^commas (map snd tvar_fixing @ map snd var_fixing)
        ^"\n\nhyps are: "^commas (Thm.hyps_of th_fxd |> map (Syntax.string_of_term ctxt2)))
  in
    th
  end





















fun strip_alls ns t =
  case t of
    Const("all", _) $ (abs as Abs(n0, T, body)) =>
      let
        val (n, ns') = if null ns then (n0, []) else (hd ns, drop 1 ns)
        val (x, fixed_body) = Term.dest_abs (n, T, body)
        val fix = Free(x, T)
      in
        strip_alls ns' fixed_body |> apfst (cons fix)
      end
  | _ => ([], t)


fun cdest_all n ct =
  case Thm.term_of ct of
    Const("all", _) $ Abs(_, _, _) =>
      let
        val (quant, lam) = Thm.dest_comb ct
        val (free, fixed_body) = Thm.dest_abs (SOME n) lam
      in
        (free, fixed_body)
      end
  | _ => raise CTERM ("dest_all_cterm: not a quantification", [ct])

fun strip_alls_cterm ns ct =
  ct |> fold_map cdest_all ns
(* use Drule.strip_imp_prems, Drule.strip_imp_concl ? *)
fun strip_horn_cterm ct =
  case try Thm.dest_implies ct of
    SOME (cprem, ct') => strip_horn_cterm ct' |> apfst (cons cprem)
  | NONE => ([], ct)


fun cdest_of_unary_propconst errmsg n cprop =
  let val (h, _) = Term.strip_comb (Thm.term_of cprop)
  in
    case h of
      Const(n', _) =>
        if n = n' then
          Thm.dest_arg cprop
        else error errmsg
    | _ => error errmsg
  end

val cdest_try = cdest_of_unary_propconst "cdest_try" Data.try_const_name
val cdest_brule = cdest_of_unary_propconst "cdest_brule" Data.brule_const_name

fun cconcl_of th = Thm.cprop_of th |> Drule.strip_imp_concl



fun dest_of_unary_propconst errmsg n prop =
  let val (h, ts) = Term.strip_comb prop
  in
    case h of
      Const(n', _) =>
        if n = n' then
          the_single ts
        else error errmsg
    | _ => error errmsg
  end

val dest_try = dest_of_unary_propconst "dest_try" Data.try_const_name
val dest_brule = dest_of_unary_propconst "dest_brule" Data.brule_const_name




(* TODO(feature):
  * jedes synthese-Judgement sollte ein extensional gleiches
    refinement-Judgement mit switch-Regel zugeordnet sein
  * Attribut add_jud einfuehren das man auf Definitionen
    anwendet mit Moding als Attribut-Parameter und die
    definierte Konstante dann als entsprechendes Judgement hinzufuegt *)
(* schmeisst Symtab.DUP wenn es das Judgement schon gab *)
fun gen_add_judgement opt_colljud_info extradeps allow_inconsis jud head_term analyzer_data mode jud_kind
    higher_jud_opt gctxt =
  let
    val {judgements, term_to_jud, depgraph, ...} = get_current_ruledata gctxt
    val _ =
      if jud = arb_judgement then
        error "add_judgement: please choose a less funny judgement name"
      else ()
    val _ = 
      case higher_jud_opt of
        SOME higher_jud =>
          if snd (get_judgement_mode gctxt higher_jud) <> 0 then
            error ("add_judgement: higher judgement "^quote higher_jud^" has outputs")
          else if fst mode + snd mode <> fst (get_judgement_mode gctxt higher_jud) then
            error ("add_judgement: higher judgement "^quote higher_jud^" has wrong number of inputs")
          else
            ()
      | NONE => ()

    val thy = Context.theory_of gctxt
    val ctxt = Context.proof_of gctxt
    val num_args = (fst mode + snd mode + 1)
    val head_args = map2 (fn n => fn T => Var ((n,0), T))
      (Name.invent (Variable.names_of ctxt) "x" num_args)
      (fastype_of head_term |> binder_types |> take num_args)
    val jud_term = #2 analyzer_data thy
      (hd head_args, take (fst mode) (tl head_args), drop (fst mode + 1) head_args)

    val judgements' = judgements
      |> Symtab.update_new (jud, (analyzer_data, head_term, mode, jud_kind, opt_colljud_info, higher_jud_opt, allow_inconsis))
    val term_to_jud' = term_to_jud |> Net.insert_term (op =) (jud_term, jud)
    val depgraph' = depgraph
      |> Graph.new_node (jud, Judgement)
      |> Graph.add_edge (arb_judgement, jud)
      |> fold (fn jud' => Graph.add_edge (jud, jud')) extradeps
  in
    gctxt |> map_judgement_stuff (K judgements') (K term_to_jud') (K depgraph')
  end

val add_judgement = gen_add_judgement NONE []
 (* colljudI proves "jud ?proplist" *)
fun add_coll_jud basejud colljudI triggerjud_opt =
  gen_add_judgement (SOME (colljudI, basejud, triggerjud_opt)) (basejud :: the_list triggerjud_opt) DisallowInconsis


fun add_general_syn_proc jud proc_id proc = map_syn_procs (Symtab.update (jud, (proc_id, proc)))
(* TODO(feature)?: allow unification variables in input but provide fixing/unfixing logic? *)
fun add_syn_proc jud proc_id proc = add_general_syn_proc jud proc_id 
    (fn ctxt => fn fail_cont => fn input_terms =>
      let
        val (pobj, iobjs, oobjs) = input_terms
        (* TODO(opt): give uncertified inputs to normal synth procs? *)
        val [[c_pobj], c_iobjs, c_oobjs] = [[pobj], iobjs, oobjs]
          |> burrow (map (norm_with_env_in_run_state ctxt #> cterm_of (Proof_Context.theory_of ctxt)))
        val ts = map Thm.term_of (c_pobj :: c_iobjs)
        val vars = [] |> fold Term.add_vars ts
        val tvars = [] |> fold Term.add_tvars ts
        val _ =
          if null vars andalso null tvars then ()
          else
            err_with_trace ctxt ("synthesis proc "^proc_id^" called on input terms\n  "
              ^commas (map (Syntax.string_of_term ctxt) ts)
              ^"\nwhich contain unification variables  "
              ^commas (map (Syntax.string_of_term ctxt o Var) vars)
              ^" and type unification variables "
              ^commas (map (Syntax.string_of_typ ctxt o TVar) tvars))
        val (th, out_cts) = proc ctxt (c_pobj, c_iobjs, c_oobjs)
        (* val _ =
          if null (Thm.hyps_of th) then ()
          else
            err_with_trace ctxt ("synthesis proc "^proc_id^" called on input terms\n  "
              ^commas (map (Syntax.string_of_term ctxt) ts)
              ^"\nreturned theorem with assumptions\n"
              ^commas (Thm.hyps_of th |> map (Syntax.string_of_term ctxt))) *)

        val vars' = Term.add_vars (prop_of th) []
        val tvars' = Term.add_tvars (prop_of th) []
        val _ = 
          if null vars' andalso null tvars' then ()
          else
            err_with_trace ctxt ("synthesis proc "^proc_id^" called on input terms\n  "
              ^commas (map (Syntax.string_of_term ctxt) ts)
              ^"\nreturned theorem with vars and/or tvars\n"
              ^commas (map (Syntax.string_of_term ctxt o Var) vars'
                @ map (Syntax.string_of_typ ctxt o TVar) tvars'))
      in
        ((grnd_exact_thm_prf th, map Thm.term_of out_cts), NONE)
      end)

fun add_tactic_proc jid tac =
  let
    val proc_id = "tactic_for_"^jid
    fun proc ctxt (pobj, iobjs, oobj_pats) =
      let
        val thy = Proof_Context.theory_of ctxt
        val {judgements, ...} = get_current_ruledata (Context.Proof ctxt)
        val maker = lookup_judgement_analyzer judgements jid |> the |> #2

        val _ =
          if null oobj_pats then ()
          else error ("add_tactic_proc: judgement "^quote jid^" has outputs")
        val goal = maker thy (Thm.term_of pobj, map Thm.term_of iobjs, [])
        val tac_res = Goal.init (cterm_of thy goal) |> tac ctxt 1
        val _ = case Seq.pull tac_res of
            SOME _ => ()
          | NONE =>
                err_with_trace ctxt ("add_tactic_proc: tactic for "^quote jid^" failed on goal "
                  ^"\n    "^Syntax.string_of_term ctxt goal)
        val th = tac_res |> Seq.hd |> Goal.conclude

        val _ =
          (* TODO(semantics): normalize modulo comp_rules ?!
               may solver change goal at all? *)
          if (prop_of th |> Envir.beta_eta_contract)
            aconv (Envir.beta_eta_contract goal)
          then ()
          else err_with_trace ctxt ("solve_prems: tactic for "^quote jid^" changed goal from "
            ^Syntax.string_of_term ctxt goal^" to "
            ^Syntax.string_of_term ctxt (prop_of th))
     in
       (th, [])
     end
  in
    add_syn_proc jid proc_id proc
  end




fun add_lthy_transform jud id transf =
  map_lthy_transforms (Symtab.update_new (jud, (id, transf)))








fun higher_judgement ctxt t =
  let val gctxt = Context.Proof ctxt
  in
    case decompose_judgement gctxt t of
      SOME (jud, (pobj, iobjs, oobjs)) =>
        (case get_judgement_higherjud gctxt jud of
          SOME jud' =>
            let
              val maker = case lookup_judgement_analyzer (get_judgements gctxt) jud' of
                  SOME (_, maker, _) => maker
                | NONE =>  error ("higher_judgement_outfixes: higher jud "^quote jud'^" not a judgement?!")
              val iobjs' = iobjs @ oobjs
            in
              ((jud', (pobj, iobjs')), maker (Proof_Context.theory_of ctxt) (pobj, iobjs', []))
              |> SOME
            end
        | NONE => NONE)
    | NONE => NONE 
  end


fun abstr_inst (avail_vars, avail_tvars) =
  Term.map_aterms (fn t => case t of
      Var (ixn as (n, _), T) =>
        if member (op =) avail_vars (ixn, T) then Free (n, T)
        else t
    | _ => t)
  #> Term.map_types (Term.map_atyps (fn T => case T of
      TVar (ixn as (n, _), S) =>
        if member (op =) avail_tvars (ixn, S) then TFree (n, S)
        else T
    | _ => T))



(* TODO(refactor): realize with fold_varapps; but normalization on each step is in the way.
     necessary if variables are sometimes partially applied, but this should not be the case
     for freshunifvar-generated ones.  *)
fun unlift_unifvar_occs t0 ctxt =
  let
    (* from Pure/term.ML *)
    fun term_name (Const (x, _)) = Long_Name.base_name x
      | term_name (Free (x, _)) = x
      | term_name (Var ((x, _), _)) = x
      | term_name _ = Name.uu;

    fun unlift boundsTs t0 ctxt =
      let val t = norm_with_env_in_run_state ctxt t0
      in
        case Term.strip_comb t of
          (v as Var(ixn as (n, _), T), ts) =>
            if forall Term.is_Bound ts then ctxt
            else 
              let
                (* TODO(feature?): more generally only unlift over those arguments that
                   correspond to local fixes? *)
                val typeof = curry Term.fastype_of1 (map snd boundsTs)
                fun name_of_bnd (Bound i) = nth boundsTs i |> fst
                  | name_of_bnd _ = error "internal error: name_of_bnd: not a bound"

                val ts_bnds = ts |> filter Term.is_Bound
                val ts_bnds_ns = Name.context
                  |> fold Term.declare_term_names (v :: ts @ map Logic.mk_type (map snd boundsTs))
                  |> fold_map Name.variant (map name_of_bnd ts_bnds)
                  |> fst
                val bnds_frees = ts_bnds_ns ~~ map typeof ts_bnds |> map Free
                val ts_bnds_to_frees = ts_bnds ~~ bnds_frees

                val T' = map typeof ts_bnds ---> drop (length ts) (binder_types T) ---> body_type T
                val (v', ctxt2) = genvar_on_run_state n T' ctxt
                (* NB: ts_nonbnds do not occur in v' of course, so this corresponds to unlifting and
                   loose bounds in ts don't matter *)
                val v'_abs = Term.list_comb(v', bnds_frees) |> fold_rev (fn t => fn body =>
                    let val t' = case AList.lookup (op =) ts_bnds_to_frees t of
                        SOME free => free
                      | NONE => t
                    in
                      Abs(term_name t', typeof t', Term.abstract_over (t', body))
                    end)
                  ts
              in
                ctxt2 |> Context.proof_map (map_env_in_run_state (curry Envir.update ((ixn, T), v'_abs)))
              end
        | (Abs(n, T, t2), []) => unlift ((n,T) :: boundsTs) t2 ctxt
        | (Abs _, _) => error ("unlift_unifvar_occs: internal error: term not beta normal")
        | (a, ts) => ctxt |> fold (unlift boundsTs) ts
      end
  in
    unlift [] t0 ctxt
  end













(* IMPORTANT: if the lhs of comp_rule is well-typed with any (!) judgement j
  (possibly different from the ones in the premises)
  then the premises of comp_rule have to be solvable by refinement
  
  the standard way of achieving this is to have a basis judgement :>_{j1}
  with  lhs :>_{j1} ty  and this derivation guarateeing solvable premises
  and any judgement  :>_{j2}  which can type the operators
    op_n  :>_{j1} A_n   in lhs as   op_n :>_{j2} B_n
  is realized as
    op_n :>_{j2} B_n := op_n :>_{j1} A_n /\ op_n :>_{j2'} B'_n
  on those operators *)
(* TODO(correctness): 
   check auf lokale subject reduction 
   bei check_local_ty_wf die Typen der gefixten Typisierungspremissen im Kontext der Premissen
     synthetisieren und damit Wohlgeformtheit checken *)
fun gen_add_comp_rule check_local_ty_wf comp_rule gctxt =
  let
    val ctxt0 = Context.proof_of gctxt
    val ctxt = ctxt0 |> add_to_msg_trace (fn () =>
      "add_comp_rule on "^Display.string_of_thm ctxt0 comp_rule)
    val prop = Thm.prop_of comp_rule
    val prems = Logic.strip_imp_prems prop
    val concl = Logic.strip_imp_concl prop
    val (lhs, rhs) = Logic.dest_equals concl

    val lhs_vars = Term.add_vars lhs []
    val lhs_tvars = Term.add_tvars lhs []
    val rhs_vars = Term.add_vars rhs []
    val rhs_tvars = Term.add_tvars rhs []

    val _ =
      if subset (op =) (rhs_vars, lhs_vars)
         andalso subset (op =) (rhs_tvars, lhs_tvars) 
      then ()
      else err_with_trace ctxt "add_comp_rule: rhs contains extra Vars or TVars"

    val _ = prems |> map (fn prem =>
      let
        val _ = case decompose_judgement gctxt prem of
            SOME (jid, _) =>
              (* TODO(correctness): will man hier nur synthese-Premissen zulassen ?!
                    auf Wohlgeformtheit von Judgements der Premissen checken? *)
              ()
          | NONE => err_with_trace ctxt ("add_comp_rule: prem "^Syntax.string_of_term ctxt prem^" is unknown judgement")

        val vars = Term.add_vars prem []
        val tvars = Term.add_tvars prem []
        val _ =
          if subset (op =) (vars, lhs_vars)
            andalso subset (op =) (tvars, lhs_tvars)
          then ()
          else err_with_trace ctxt ("add_comp_rule: prem "^Syntax.string_of_term ctxt prem^" has extra Vars or TVars")
      in () end)
  in
    (* TODO(correctness): check if comp_rule is present already *)
    gctxt |> map_comp_rules (the_default Raw_Simplifier.empty_ss
      #> Raw_Simplifier.add_simp comp_rule #> SOME)
  end

val add_comp_rule = gen_add_comp_rule false









fun balanced_conjuncts_to_thms th =
  th |> Conjunction.elim_balanced (Conjunction.dest_conjunctions (Thm.cprop_of th) |> length)
fun unbalanced_conjuncts_to_thms th = 
  [th] |> ImpConv.saturate_pool (
    ImpConv.collect_rewrs_iconv [Conjunction.conjunctionD1, Conjunction.conjunctionD2])
  

fun balance_conj_conv thy ct =
  let
    val t = Thm.term_of ct
    val conjs = Logic.dest_conjunctions t
    val t' = Logic.mk_conjunction_balanced conjs
  in
    Goal.init (cterm_of thy (Logic.mk_equals (t, t')))
    |> (match_tac [Drule.equal_intr_rule] 1
        THEN (REPEAT_DETERM_FIRST
          (eq_assume_tac
           ORELSE' ematch_tac [Data.conjunctionE]
           ORELSE' match_tac [Conjunction.conjunctionI])))
    |> Seq.hd |> Goal.conclude
  end


fun balance_majprem_and_concl thy th =
  let
    val whole_conv = (Conv.implies_conv (balance_conj_conv thy) Conv.all_conv)
      then_conv (Conv.concl_conv (Thm.nprems_of th) (balance_conj_conv thy))
  in
    Conv.fconv_rule whole_conv th
  end





(* given a list of position-dependent choices generates all lists of that length with elements
choosen by position, e.g.  list_amb [[0,1],[2]] == [[0,2],[1,2]] *)
fun list_amb [] = [[]]
  | list_amb ((ch::chs) : ('a list) list) : ('a list) list =
      map (fn a => map (cons a) (list_amb chs)) ch |> flat



fun pot_note_in_lthy fact ctxt =
  if get_running_expl_frules ctxt then
    let
      val lthy = ctxt
      val name = case decompose_judgement (Context.Proof lthy) (prop_of fact) of
          SOME (jud, (_, [name_t], _)) =>
            if jud = note_jud then
              (case try name_from_const_or_free_unsuffix name_t of
                SOME n' => n'
              | NONE => err_with_facts lthy ("pot_note_in_lthy: strange term for name "
                  ^Syntax.string_of_term lthy name_t))
            else
              err_with_facts lthy ("pot_note_in_lthy: strange fact "
                ^Display.string_of_thm lthy fact)
        | _ =>
            err_with_facts lthy ("pot_note_in_lthy: strange fact "
              ^Display.string_of_thm lthy fact)

      val ths = fact |> Conv.fconv_rule (Conv.rewr_conv Data.note_const_def)
        |> unbalanced_conjuncts_to_thms
        |> filter_out (fn th => (Thm.prop_of th) aconv (Data.mk_Trueprop Data.True))
        |> map (Thm.forall_elim_vars 0)
      val bnd = Binding.name (Long_Name.base_name name)
      val ((_, output_ths), lthy2) = lthy
        |> Local_Theory.note ((bnd, []), ths)
      val note_msg = "noted "^Pretty.str_of (Binding.pretty bnd)^": "^
        (output_ths |> map (Display.string_of_thm lthy2)
        |> (if length output_ths = 1 then the_single
            else (fn strs => "\n"^cat_lines (map (fn str => "    "^str) strs))))
      (* val _ = tracing note_msg *)
    in
      lthy2
      |> map_lthy_transforms_log (cons note_msg)
    end
  else
    (* TODO(feature): warning ausgeben?? *)
    ctxt





and add_assm_terms_internal assms0 ctxt =
  let
    val {judgements, term_to_jud, ...} = get_current_ruledata (Context.Proof ctxt)
    val cert = cterm_of (Proof_Context.theory_of ctxt)

    (* TODO(opt): assms0 are normalized already in the call from solve_prems *)
    val assms = map (norm_with_env_in_run_state ctxt) assms0
    val g_assms = filter ground assms
    val ng_assms = filter_out ground assms

    (* NB: nur fuer non-ground assms diesen Kontext-Extraktions-Hack machen damit
        ground-assms die auch Fakten sind weiterhin im Fakten-Pool bleiben *)
    (* TODO(opt): certification is slow here. can we do anything about this?
         probably only if we can guarantee no implicit forward rules will match
         on the ground assumption, so we don't have to add it via the normal
         mechanism that expects thms *)
    (* NB: discharge of these assumptions (which become hyps of the DirectRule ths)
         happens in normal ImpI proof replay *)
    val (g_assm_ths, ctxt2) = ctxt |> Assumption.add_assumes (map cert g_assms)
    val ctxt3 = fold (add_assm false) g_assm_ths ctxt2

    val ((ng_assms_fxd, thaw_th), ctxt4) = exact_freeze_props_thaw_thms ng_assms ctxt3
    val (ng_assm_fxd_ths, ctxt5) = ctxt4 |> Assumption.add_assumes (map cert ng_assms_fxd)
    val ctxt6 = fold (add_assm false) ng_assm_fxd_ths ctxt5


    fun construct_local_rule R_th ctxt_ = 
      let
          (* as an optimization we only discharge the assumptions that have actually been used in the derivation of the rule *)
        val rule_hyps = Thm.hyps_of R_th
        val cassms_used = Assumption.local_assms_of ctxt6 ctxt3
          |> filter (fn cassm_fxd => member (op aconv) rule_hyps (Thm.term_of cassm_fxd))

          (* NB: vars (but no TVars) can be present in R_th because add_assm does Thm.forall_elim_vars *)
          (* NB: loc_vars cannot occur in the cassms_used because they are ground *)
        val loc_vars = Term.add_vars (prop_of R_th) []
        val (loc_vars_fxns, ctxt_2) = ctxt_ |> Variable.variant_fixes (map (fst #> fst) loc_vars)
        val loc_var_fixing = loc_vars ~~ loc_vars_fxns |> map (fn ((ixn, T), n') => (Var (ixn, T), Free(n', T)))

        val R_th_disch = R_th
          |> Drule.implies_intr_list cassms_used
          |> Thm.instantiate ([], loc_var_fixing |> map (pairself (cterm_of (Proof_Context.theory_of ctxt_2))))
          |> thaw_th

        val assms_used_thawed = Thm.prems_of R_th_disch |> take (length cassms_used)
        (* TODO(opt): if R_th_disch is of the form  P ==> P, then just give back the allI-closed assumption_prf P *)
        (* NB: exact_thm_prf is safe here because thaw_th constructed theorem with instantation into current env *)
        val prf = unsafe_exact_thm_prf R_th_disch
          |> fold (mp_rev_prf ctxt3 o assumption_prf) assms_used_thawed
          |> fold_rev (allI_prf ctxt_2) (map (snd #> Term.dest_Free) loc_var_fixing)

        (* val _ = tracing ("constructed local rule "^str_of_normed_term ctxt_2 (prop_of_proofp prf)
          ^"\n  out of forall-elimd rule generated from fixed assumptions "^Display.string_of_thm ctxt_2 R_th
          ^"\n  R_th_disch is "^Display.string_of_thm ctxt_2 R_th_disch
          ^"\n  ng_assms are "^commas (map (str_of_normed_term ctxt_2) ng_assms)
          ^"\n  ng_assms_fxd are "^commas (map (str_of_normed_term ctxt_2) ng_assms_fxd)) *)
      in
        (LocalRule prf, ctxt_2)
      end
    
    val {rules, ...} = get_current_ruledata (Context.Proof ctxt3)
    val {rules=rules2, ...} = get_current_ruledata (Context.Proof ctxt6)
      (* NB: we rely on the fact that the item net content is managed like a stack *)
      (* TODO(opt): this is very slow?! *)
    val new_rules = Symtab.dest rules2 |> maps (fn (jud_, itemnet) =>
      Item_Net2.content itemnet |> rev |> drop (Symtab.lookup rules jud_ |> Option.map Item_Net2.content |> the_default [] |> length)
      |> map (fn (ruleref, prior) => case ruleref of
             DirectRule th => (th, jud_, prior)
           | LocalRule prfp => err_with_trace ctxt6 ("add_assm_terms_internal: internal error: locally generated rule is not direct: "
              ^Syntax.string_of_term ctxt6 (prop_of_proofp prfp))))
  in
    ctxt3
    |> Context.proof_map (map_assms (append assms))
    |> fold (fn (new_rule, rule_jud, prior) => fn ctxt_ =>
        let
          val (rule', ctxt_2) = construct_local_rule new_rule ctxt_
        in
          (* minor FIXME: we don't update the depgraph. this is already in anticipation of removal of
               the automatic dependency tracking feature *)
          (* NB: if a local rule gets instantiated further, we do not update the net indexing.
             this is ok because the net matching will then just be more approximative than necessary *)
          ctxt_2 |> Context.proof_map (map_rule_stuff
            (Symtab.map_default (rule_jud, Item_Net2.init eq_for_net)
              (* NB: the local rule rule' is normed wrt current run state, since assms are normed *)
              (Item_Net2.cons (rule', prior) (rule_net_index judgements term_to_jud)))
            I)
        end)
      new_rules
  end

(* TODO(semantics): dynamisch auf Wohlgeformtheit der entstehenden Metafunktion
     pruefen, dh zu jedem Atom und inputs gibt es hoechstens eine Annahme
     fuer ein Judgement *)
(* TODO(opt): add_fact auf lokale Fakten optimieren
     vllt auch nur dann als lokales Faktum hinzufuegen
     wenn das Judgement bestimmte Form hat? *)
(* TODO(opt): wenn Annahme keine Unifikationsvariablen hat als thm reingeben
   lassen und als DirectRule statt als LocalRule auffassen *)
(* NB: darf zugruendeliegende thy des ctxts nicht veraendern,
    insbesondere auch keine declarations erlaubt (weil die checkpoints
    emittieren) *)
and add_assm checked th ctxt =
  let
    (* TODO: wenn assm quantifiziert ist und ausserdem Unifvar hat,
         muessen wird es als lokale Regel betrachten bei deren Benutzung ihre
         quantifizierte Variablen immer zu frischen Unifvar instantiiert werden
         und die bereits bestehenden Unifvar geshared werden *)
    val rule =
      if null (Logic.strip_params (prop_of th)) then th
      else
        (* TODO(correctness): should we use maxidx from ctxt?
          but (local) rules are freshified right before their application anyway *)
        Thm.forall_elim_vars 0 th
    val prop = prop_of rule
    val is_rule = gen_check_rule checked checked ctxt prop |> is_some
    val is_fact = is_rule andalso null (Logic.strip_imp_prems prop) andalso ground prop 
    val frule_opt = 
      case Term.head_of prop of
        Const (n, _) =>
          if n = Data.frule_const_name then
            rule |> Conv.fconv_rule (Conv.rewr_conv Data.frule_const_def) |> SOME
          else NONE
      | _ => NONE

    val ctxt' = ctxt
      |> (if is_fact then (* Fakten werden automatisch brules *)
            add_local_fact rule 
          else if is_rule then
            Context.proof_map (gen_add_rule true checked ctxt 0 rule)
          else case frule_opt of
            SOME frule => 
              Context.proof_map (gen_add_frule checked true false false frule)
          | NONE => I)
  in
    ctxt'
  end


(* prems are assumed to be ground
   (therefore the replay of their proofs is possible without hyp discharge) *)
(* NB: local forward rule execution works on ctxt with non-trivial instantiation in run-state
   from surrounding metarec-state but ignores this instantiation because it should
   not interfere with the instantiation calculated by solving the premises of the frule.
   In particular the uninstantiated variables in locally generated brules should be
   interpreted as generalization variables and not be accidentally instantiated from the
   surrounding metarec state.  *)
and solve_prems_standalone global_fail_cont local_fail_cont rule prems ctxt0 =
  let
    val run_st0_opt = get_run_state (Context.Proof ctxt0)
    val ctxt0_decld_prems = ctxt0 |> fold Variable.declare_term prems (* NB: for correct maxidx *)
    val ctxt = ctxt0 |> Context.proof_map (set_run_state (init_run_state ctxt0_decld_prems) #> set_assms [])
    val (prfps, ctxt2) = solve_prems true true global_fail_cont local_fail_cont (prop_of rule) prems ctxt
    val ths = map (replay_prf ctxt2) prfps

    val env = get_the_env_in_run_state ctxt2
    val ctxt3 = ctxt2 |> Context.proof_map (set_run_state run_st0_opt)
  in
    ((ths, env), ctxt3)
  end

(* prems have to be normal, rule is only used for printing *)
 (* ctxt is the thy-transferred version of ctxt0 corresponding to 
    lthy transformations potentially done on gctxt
    NB: ctxt is not really propagated linearly here, everything starts from
      a theory transferred ctxt0, which is also the first output
 *)
and solve_prems topcall allow_lthy_transf global_fail_cont local_fail_cont rule_prop prems ctxt0 =
  let
    exception LocalFail of Proof.context * string
    exception GlobalFail of Proof.context * string

    fun solve_prem prem ctxt =
      let
        val thy = Proof_Context.theory_of ctxt
        val gctxt = Context.Proof ctxt
        val {judgements, syn_procs, lthy_transforms, ...} = get_current_ruledata gctxt
        (* TODO(feature): ctxt um vorige Premissen (ohne Bounds?) der Regel
             erweitern und durchfaedeln damit rewriten Soft-Typisierungspremissen
             loesen kann die von vorigen Premissen der Regel abhaengen

             wenn der User das braucht kann er aber auch einfach
             explizite Context-Erweiterungen um die vorigen Premissen
             fuer diesen Premissen vornehmen:
               also als   [| P1 ; P1 ==> P2 |] ==> C   formulieren
               statt als  [| P1 ; P2 |] ==> C
               wenn P2 von P1 abhaengt
             BTW: C wird automatisch im um die Pi erweiterten Kontext gerewritet *)
        val prem2 = norm_with_env_in_run_state ctxt prem
        fun act_rule () = norm_with_env_in_run_state ctxt rule_prop
        (* val _ = tracing ("solve_prem on "^Syntax.string_of_term ctxt prem2
          ^"\n  towards  "^Syntax.string_of_term ctxt (act_rule ())) *)

        (* TODO(tuning): use Subgoal.focus to prove prem
             but how to deal with implicit normalization?
               normalize prem2 instead!
             (will probably degrade performance, so not really a good idea?) *)
        val params_raw = Logic.strip_params prem2
        val (param_names, ctxt_rec0) = Variable.variant_fixes (map fst params_raw) ctxt 
        val (params, prem2_body) = prem2 |> strip_alls param_names 
          (* noetig weil durch Parameterfixierung non-Patterns entstehen *)
        val param_lam_lift = fold_rev Term.lambda params
        val (prem2_assms, prem2_concl) = Logic.strip_horn prem2_body 
        val ctxt_rec = ctxt_rec0
          (* necessary so that we can retrieve the types of fixes when generating unification variables: *)
          |> fold (Variable.declare_constraints) params  
          |> add_assm_terms_internal prem2_assms

        (* val _ = tracing ("solve_prems: declared constraints of "^commas (map (str_of_normed_term ctxt_rec) params)
          ^" are "^(Variable.constraints_of ctxt_rec |> fst |> Vartab.dest |> filter (fn ((n, ix), _) => ix = ~1)
            |> map (fn ((n, _), t) => Free(n,t) |> Syntax.string_of_term ctxt_rec) |> commas)) *)

        val (fail_ex, prem2_concl', pot_wrap_try) =
          case try dest_try prem2_concl of
            SOME x => (LocalFail, x, mps_match_on_freshthm_prf Data.tryI o single)
          | NONE => (GlobalFail, prem2_concl, pair)
        fun discharge prf ctxt_ = 
          let
            val (prf2, ctxt_2) = (prf, ctxt_) |-> pot_wrap_try
              handle THM (msg, _, _) => err_with_trace ctxt_
                ("error while discharging proof of "^str_of_normed_term ctxt_ (prop_of_proofp prf))
            val prf3 = prf2 |> fold_rev (impI_prf ctxt_2) prem2_assms
            val prf4 = prf3 |> fold_rev (allI_prf ctxt_2 o Term.dest_Free) params
            (* val _ = tracing ("discharging "^str_of_normed_term ctxt_2 (prop_of_proofp prf2)
              ^"\n  (uninstantiated "^Syntax.string_of_term ctxt_2 (prop_of_proofp prf2)^")"
              ^"\nunder "^commas (map (str_of_normed_term ctxt_2) (params @ prem2_assms))
              ^"\n  (uninstantiated "^commas (map (Syntax.string_of_term ctxt_2) (params @ prem2_assms))^")"
              ^"\ngives "^str_of_normed_term ctxt_2 (prop_of_proofp prf4)) *)
          in
            (prf4, ctxt_2)
          end

        (* val _ = tracing ("solve_prems: prem2_concl' is "^
          Syntax.string_of_term ctxt_rec (mark_eta_redexes prem2_concl')) *)
      in

        (* TODO: we need to apply the global substitution to get a rigid head to decide the judgement *)
        case decompose_judgement gctxt prem2_concl' of
          SOME (jid, (pobj_of_prem, iobjs_of_prem, oobj_pats_of_prem)) => 
            let
              (* val _ = tracing ("solve_prems: pobj_of_prem is "^
                Syntax.string_of_term ctxt_rec (mark_eta_redexes pobj_of_prem)) *)
              val ctxt_rec' = add_to_rule_trace act_rule ctxt_rec
              val ((disch_prf, oobjs), disch_ctxt2) =
                (case Symtab.lookup syn_procs jid of
                  SOME (_, proc) =>
                    let
                      (* val _ = tracing ("calling synproc on "^str_of_normed_term ctxt_rec' prem2_concl') *)
                      val ((prf, oobjs), st2_opt) = proc ctxt_rec' (fn ctxt => fn msg => raise fail_ex (ctxt, msg))
                        (pobj_of_prem, iobjs_of_prem, oobj_pats_of_prem)
                      val _ =
                        if is_some st2_opt andalso allow_lthy_transf then
                          err_with_trace ctxt_rec' ("solve_prems: called synthesis proc returned new state "
                            ^"which is not allowed in this execution mode (lthy transformations are allowed)")
                        else
                          ()
                      val disch_ctxt2 =
                        if is_some st2_opt then
                          ctxt |> Context.proof_map (set_run_state st2_opt)
                        else
                          ctxt
                      (* val _ = tracing ("synproc returned "^str_of_normed_term disch_ctxt2 (prop_of_proofp prf)) *)
                    in
                      ((prf, oobjs), disch_ctxt2)
                    end
                | NONE =>
                    (case Symtab.lookup lthy_transforms jid of
                      SOME (lthy_transform_id, lthy_transform) =>
                        if (not allow_lthy_transf) then
                          err_with_trace ctxt_rec' ("solve_prems: lthy transformation not allowed")
                        else if not (null params andalso null prem2_assms) then
                          err_with_trace ctxt_rec' ("solve_prems: lthy transformation under fixes or assumes not allowed")
                        else if not (ground pobj_of_prem andalso forall ground iobjs_of_prem) then
                          err_with_trace ctxt_rec' ("solve_prems: lthy transformation with arguments containing "
                            ^"unification variables not allowed")
                        else if get_running_expl_frules ctxt then
                          (* ctxt = ctxt_rec' (bis auf rule trace), weil keine Param oder Annahmen
                             ctxt ist eine lthy *)
                          let
                            (* locally unsetting run state only for cleanness *)
                            val lthy = ctxt |> Context.proof_map (set_run_state NONE) 
                            val certnorm = norm_with_env_in_run_state ctxt
                              #> cterm_of (Proof_Context.theory_of lthy)
                            val ((resth, couts), lthy2) = lthy
                              |> lthy_transform (certnorm pobj_of_prem, map certnorm iobjs_of_prem)
                            val lthy3 = lthy2 |> Context.proof_map (set_run_state (get_run_state (Context.Proof ctxt)))
                          in
                            ((grnd_exact_thm_prf resth, map Thm.term_of couts), lthy3)
                          end
                        else
                          err_with_trace ctxt_rec' ("solve_prems: expected local theory to do lthy transformation "
                            ^quote lthy_transform_id^" on "^Syntax.string_of_term ctxt_rec' prem2_concl')
                    | NONE =>
                        (* NB: recursive calls to solve_prems in metarec_worker are not
                            allowed to do lthy transformations; ctxt_rec' always contains generated
                            brules of gctxt, cf. gen_with_pot_frules *)
                        metarec_worker topcall ctxt_rec'
                          (SOME (fn ctxt => fn msg => raise fail_ex (ctxt, msg)))
                          jid (pobj_of_prem, iobjs_of_prem)
                        ||> (fn ctxt2 => ctxt |> Context.proof_map (set_run_state (get_run_state (Context.Proof ctxt2))))))
                |> (fn ((prf, oobjs), disch_ctxt2) =>
                     let val (prf', disch_ctxt2') = discharge prf disch_ctxt2
                     in
                     (* FIXME: wenn lthy transformation Local_Defs nutzt will man diese Assumptions nicht exporten! *)
                       ((prf', map (norm_with_env_in_run_state disch_ctxt2') oobjs), disch_ctxt2')
                     end)

              (* NB: since oobj_pats_of_prem are normed, this can constitute a unification
                 due to deep matching, if a matching variable in one of the patterns has 
                 already been instantiated to a unification variable *)
              (* TODO(feature): allow selective control over this unification behaviour
                   or move to purely matching semantics *)
              val disch_ctxt3 =
                case pattern_matches_envctxt disch_ctxt2 (map param_lam_lift oobj_pats_of_prem, map param_lam_lift oobjs) of
                  SOME disch_ctxt3 => disch_ctxt3
                | NONE =>
                    let
                      val maker' = lookup_judgement_analyzer judgements jid |> the |> #2
                      val t = maker' (Proof_Context.theory_of disch_ctxt2) (pobj_of_prem, iobjs_of_prem, oobjs)
                    in
                      raise fail_ex (disch_ctxt2, "solve_prems: recursive synthesized judgement "  
                      ^"\n     "^Syntax.string_of_term disch_ctxt2 t
                      ^"\ndoes not match premise (with lifting parameters ["
                        ^Library.commas (map (Syntax.string_of_term disch_ctxt2) params)
                      ^"])\n     "^Syntax.string_of_term disch_ctxt2 prem2_concl'
                      ^"\nof instantiated rule "
                      ^"\n     "^Syntax.string_of_term disch_ctxt2 (act_rule ())
                      ^"\n\n raw oobjs: \n" ^cat_lines (map PolyML.makestring oobjs)
                      ^"\n\n raw oobj_pats: \n"^cat_lines (map PolyML.makestring oobj_pats_of_prem))
                    end

              (* TODO(opt): this check only helps debugging *)
              val _ =
                if aconv_norm (norm_with_env_in_run_state disch_ctxt3) (prop_of_proofp disch_prf, prem) then ()
                else
                  ( tracing ("solve_prems: wanted to solve prem "
                    ^str_of_normed_term disch_ctxt3 prem
                    ^"\nbut constructed proof for\n"
                    ^str_of_normed_term disch_ctxt3 (prop_of_proofp disch_prf)) ;

                  err_with_trace ctxt_rec' ("solve_prems: wanted to solve prem "
                    ^str_of_normed_term disch_ctxt3 prem
                    ^"\nbut constructed proof for\n"
                    ^str_of_normed_term disch_ctxt3 (prop_of_proofp disch_prf)
                    ^"\nproof is:\n"
                    ^str_of_normed_term disch_ctxt3 (prf_to_display_term disch_ctxt3 disch_prf)))

              (* val _ = tracing ("solved premise "^str_of_normed_term disch_ctxt3 prem) *)
            in
              (disch_prf, disch_ctxt3)
            end
        | NONE =>
            err_with_trace ctxt_rec ("solve_prems: not a known judgement in instantiated premise"
                 ^"\n      "^Syntax.string_of_term ctxt_rec prem2_concl'
                 ^"\nof instantiated rule"
                 ^"\n      "^Syntax.string_of_term ctxt_rec (act_rule ()))
      end
  in
    ctxt0 |> fold_map solve_prem prems
      handle
        LocalFail (ctxt, msg) => local_fail_cont ctxt msg
      | GlobalFail (ctxt, msg) => global_fail_cont ctxt msg
  end





(* pobj, iobjs may not contain any Vars and have to be beta,comp_rules-normal *)
and metarec_worker topcall ctxt global_fail_cont_opt jid (pobj, iobjs) =
  let
    val gctxt = Context.Proof ctxt
    val {rules, judgements, ...} = get_current_ruledata gctxt

    exception LocalFail of Proof.context * string
    exception GlobalFail of Proof.context * string
    val global_fail_cont =
      case global_fail_cont_opt of
        SOME fc => fc
      | NONE => err_with_trace

    val _ =
      if length iobjs = fst (get_judgement_mode gctxt jid) then ()
      else err_with_trace ctxt ("metarec_worker: judgement "^quote jid
         ^" has wrong number of input objects "^Library.commas (map (Syntax.string_of_term ctxt) iobjs))

    val thy = Proof_Context.theory_of ctxt
    val jud_matcher =
      case lookup_judgement_analyzer judgements jid of
        SOME (jud_matcher, _, _) => jud_matcher
      | NONE => err_with_trace ctxt ("metarec_worker: judgment "^quote jid^" not known")

    val pot_rules = case Symtab.lookup rules jid of
        SOME inet =>
          Item_Net2.retrieve_match inet
            (pack_pobj_iobjs pobj iobjs |> Envir.eta_contract)
          |> order_by_priority
      | NONE => [] (* error ("metarec_worker: no rules registered for judgement "^quote jid) *)

    fun no_match failed_rules =
      let val no_match_msg =
        "metarec_worker: no matching rule for animation of judgement "
        ^quote jid^" for primary object\n"^Syntax.string_of_term ctxt pobj
         ^"\nand further inputs\n"^cat_lines (map (Syntax.string_of_term ctxt) iobjs)
         ^(if null failed_rules then
             ""
           else
             "\nfailed rules:\n"^cat_lines (map (Syntax.string_of_term ctxt o prop_of_proofp) failed_rules))
         ^"\npotential rules:\n"^cat_lines (map (Syntax.string_of_term ctxt o prop_of_rule ctxt) pot_rules)
      in
        raise GlobalFail (ctxt, no_match_msg)
      end



    fun rulematch () =
      let
        fun rename_proofp proofp ctxt4 = 
          proofp |> map_prop_of_proofp (fn prop =>
            let
              (* val _ = tracing ("before renaming and inst: "^Syntax.string_of_term ctxt4 (mark_eta_redexes (prop_of rule))) *)
                (* rename bound variables for better error messages *)
                (* use uninstantiated rule to avoid confusion with var:=abstraction instantiations *)
                (* pobj_of_rule, iobjs_of_rule  und  obj, iobjs  beta-normal wg add_rule *)
              val (pobj_of_rule, iobjs_of_rule, _) = prop |> Logic.strip_imp_concl |> jud_matcher |> the
              (* FIXME: bound variable name that we first descend into is not shared ?!?! should pobj, iobjs be normed ?! *)
              val prop2 = prop
                |> Term.rename_abs (pack_pobj_iobjs pobj_of_rule iobjs_of_rule)
                     (pack_pobj_iobjs pobj iobjs)
                |> the_default prop
              (* val _ = tracing ("after renaming and inst: "^Syntax.string_of_term ctxt4 (mark_eta_redexes (prop_of res))) *)
            in
              prop2
            end)

        fun app_rule proofp' ctxt4 = 
          let
            val prems' = prop_of_proofp proofp' |> Logic.strip_imp_prems
            val (solved_prems, ctxt5) =
              solve_prems false false
                (fn ctxt_ => fn msg => raise GlobalFail (ctxt_, msg))
                (fn ctxt_ => fn msg => raise LocalFail (ctxt_, msg))
                (prop_of_proofp proofp') prems' ctxt4

            (* val _ = tracing ("metarec_worker: solved rule premises \n"
              ^cat_lines (map (str_of_normed_term ctxt5 o prop_of_proofp) solved_prems)
              ^"\nof instantiated rule\n"^str_of_normed_term ctxt5 (prop_of_proofp proofp')) *)

            (* val _ = tracing ("solved prems are: "^commas
              (solved_prems |> map (Syntax.string_of_term ctxt5 o mark_eta_redexes o prop_of)))

            val _ = tracing ("concl-matching-instantiated rule is: "
              ^Syntax.string_of_term ctxt5 (prop_of rule' |> mark_eta_redexes)) *)

            val prop' = prop_of_proofp proofp'

            (* val _ = tracing ("premise-solving-instantiated and normalized rule is: "
              ^Syntax.string_of_term ctxt5 (prop_of rule'' |> mark_eta_redexes)) *)


            val (_, iobjs_of_rule', oobjs_of_rule') =
              Logic.strip_imp_concl prop' |> jud_matcher |> the

            fun ext_rl_tr ctxt_ = add_to_rule_trace (K (prop_of_proofp proofp')) ctxt

            val res = proofp' |> fold (mp_rev_prf ctxt5) solved_prems
            (* val _ = tracing ("metarec_worker: after discharge of rule premises \n"
              ^str_of_normed_term ctxt5 (prop_of_proofp res)) *)
            val oobjs_of_rule'' = oobjs_of_rule' |> map (norm_with_env_in_run_state ctxt5)
          in
            ((res, oobjs_of_rule''), ctxt5)
          end


          (* TODO(feature)
               * structural matching und higher-order pattern matching
                 verschraenken, so das auch matching mit non-Patterns
                 flexibler ist und Dinge wie  (gmlam x:A. t_1(x)) $ t_2
                 funktionieren (ist aber ziemlich selten!)
               * auf primaeren Objekten wahlweise auch normales statt
                 decompose higher-oder pattern matching erlauben
          *)
          (*     decompose higher-oder pattern matching auf primaeren Objekten
                 ist wie higher-order pattern matching nur das Objekte nicht
                 on-the-fly eta-expandiert werden, um Termination bei sowas wie
                    (!! x. t(x) subsimpto t'(x)) ==> (% x. t(x)) subsimpto (%x. t'(x))
                 zu kriegen. Was man braucht wenn zusaetzlich ne Regel wie
                     ... ==> (t1 t2) subsimpto t'
                 da ist die nur first-order-matching betreibt.
                 Dabei ist dann sehr wichtig das Regel nicht eta-kontrahiert wird, 
                 vllt also besser mit nem Spezial-Lambda schreiben?
                 Aktivieren ueber DECOMPOSE marker vor den Patterns gegen die man
                 nur decompose-matchen will *)
        fun first_succ [] failed_rules = no_match failed_rules
          | first_succ (rule :: rem_rules) failed_rules = 
              let
                (* beta normal wg add_rule *)
                val (proofp, ctxt2) = ctxt |> fresh_proofp_of_rule rule
                (* val _ = tracing ("freshified rule: "^str_of_normed_term ctxt2 (prop_of_proofp proofp)) *)
                val (pobj_pat, iobj_pats, _) = proofp |> prop_of_proofp
                  |> Logic.strip_imp_concl |> jud_matcher |> the

                fun match_iter [] [] succ_cont ctxt_ = succ_cont ctxt_
                  | match_iter (iobj_pat :: rem_iobj_pats) (iobj :: rem_iobjs) succ_cont ctxt_ =
                      (* TODO(feature): only check normalized iobj_pat for pattern-ness.
                         But Decomp.match_w_shared_vars should be tolerant regarding pattern-ness
                         for instantiated variable heads then. *)
                      if Pattern.pattern iobj_pat then
                         (* kein eta, wird on-the-fly expandiert *)
                         (case pattern_match_envctxt ctxt_ (iobj_pat, iobj) of
                           NONE => first_succ rem_rules failed_rules
                         | SOME ctxt_2 =>
                             match_iter rem_iobj_pats rem_iobjs succ_cont ctxt_2)
                      else
                        let
                          (* NB: we do not avoid deep pattern matching against unification variables ATM.
                               For this we would have to make sure that only those matching variables
                               that only occur in arguments of non-patterns are normed wrt the
                               current instantiation *)
                          val iobj_pat' = norm_with_env_in_run_state ctxt_ iobj_pat
                          val frees = Term.add_frees iobj_pat' []
                          val abs_frees = fold_rev (Term.lambda o Free) frees
                          val iobj_pat'_absd = abs_frees iobj_pat'
                        in
                          if Pattern.pattern iobj_pat'_absd then
                            match_iter (iobj_pat'_absd :: rem_iobj_pats) (abs_frees iobj :: rem_iobjs)
                              succ_cont ctxt_
                          else
                            first_succ rem_rules failed_rules
                            (* NB: kein verzoegertes Matching auf non-pattern Inputs in
                               nicht-primaerer Position mehr. Machte Probleme wegen
                               Nachinstantiierung von in den Premissen der Regel
                               generierten Constraints fuehren was ggf. zur
                               unvollstaendigen Quantifikation ueber ihre relevanten Fixes fuehrt.
                               Kann man bei Bedarf ja mit
                                 [| ... ; match non_pat against B |] ==> J .. B outs
                               in Regeln simulieren *)
                        end
              in
                (* Implicitly degrades to structural first-order matching (which is also
                   decompose in this sense) if pobj_pat is not a pattern. *)
                case decompose_pattern_match_envctxt ctxt2 (pobj_pat, pobj) of
                  NONE => first_succ rem_rules failed_rules
                | SOME ctxt3 =>
                    ctxt3 |> match_iter iobj_pats iobjs (fn ctxt4 =>
                      let val proofp' = rename_proofp proofp ctxt4
                      in
                        app_rule proofp' ctxt4
                        handle LocalFail (ctxt_, msg) =>
                          let val _ = () (* tracing ("application of rule\n  "
                            ^str_of_normed_term ctxt_ (prop_of_proofp proofp')
                            ^"\nfailed:\n"^msg) *)
                          in first_succ rem_rules (proofp' :: failed_rules) end
                      end)
              end
      in
        first_succ pot_rules []
      end
  in
    if topcall then
      rulematch ()
      handle GlobalFail (ctxt, msg) => global_fail_cont ctxt msg
           | InternalInterrupt => raise Exn.Interrupt
    else
      rulematch ()
      handle GlobalFail (ctxt, msg) => global_fail_cont ctxt msg
             (* TODO(correctness): nicht i.A. Interrupts spezialbehandeln sondern nur auf User-setzbares Flag hin *)
           | Exn.Interrupt =>
              let val _ = tracing ("Interrupt raised in metarec_worker\nInfos:" ^ compose_err_from_trace ctxt "")
              in raise InternalInterrupt end
  end







and comp_rules_in_ctxt ctxt =
  let
    val {comp_rules, ...} = get_current_ruledata (Context.Proof ctxt)
    val comp_rules' = 
      case comp_rules of
        NONE => empty_ss
      | SOME comp_rules' => comp_rules'
  in 
     Raw_Simplifier.context ctxt comp_rules'
     |> Raw_Simplifier.set_mksimps (fn ss => fn th => [])
  end
  
and metarec_simp_prover ss =
  let
    val ctxt0 = Raw_Simplifier.the_context ss
    val ctxt = ctxt0 |> fold (add_assm false) (Raw_Simplifier.prems_of ss)
  in 
      (* wichtig fuer cong-Regeln das immer rekursiver Simplifier im
         prover/subgoaler dabei ist*)
    SINGLE (ALLGOALS (SUBGOAL (fn (goal, i) =>
      (if can Logic.dest_equals (Logic.strip_assums_concl goal) then
          (* TODO(correctness): braucht reflexivity solver ? *)
         CHANGED_PROP (Simplifier.full_simp_tac (comp_rules_in_ctxt ctxt) i)
      else
         no_tac)
      ORELSE 
        (case decompose_judgement (Context.Proof ctxt) goal of
          NONE => no_tac
        | SOME (jid, (pobj, iobjs, oobjs)) =>
            let
              val ctxt_rec = ctxt |> add_to_msg_trace (fn () =>
                "metarec_simp_prover: trying to prove "^Syntax.string_of_term ctxt goal
                  ^" via meta recursion")
              val ((th, _), (delayed_unifs, constraints)) = metarec ctxt_rec jid (pobj, iobjs)
            in
              if null delayed_unifs andalso null constraints then
                rtac th i
              else
                no_tac
            end))))
  end

(* weil Net.is_empty nicht exportiert und Net.content potentiell teuer ist
   verwalten wir lieber selber ob es computational rules gibt statt das
   simpset auf Leerheit zu pruefen *)
and no_comp_rules ctxt =
  let val {comp_rules, ...} = get_current_ruledata (Context.Proof ctxt)
  in is_none comp_rules end

and rewrite_thm ctxt =
  if no_comp_rules ctxt then
    beta_convert
  else
    Raw_Simplifier.rewrite_thm (true, true, false)
      metarec_simp_prover (comp_rules_in_ctxt ctxt)
and rewrite_cterm ctxt = 
  if no_comp_rules ctxt then
    Thm.beta_conversion true
  else
    Raw_Simplifier.rewrite_cterm (true, true, false)
      metarec_simp_prover (comp_rules_in_ctxt ctxt)
 (* then_conv Thm.eta_conversion *)
  

and normalize_lesseta ctxt th =
  let val ctxt' = ctxt |> add_to_msg_trace (fn () =>
    "normalize_lesseta on "^Display.string_of_thm ctxt th)
  in rewrite_thm ctxt' th end
(*TODO(semantics): eventuell doch irgendwie eta-Normalisierung interessant ausserhalb
    von Netzmatching?? Lasse ich ja momentan nur weg weil non-eta-normale Regeln mit
    decomposing pattern matching dann iA nicht mehr passen wuerden.
    Die koennte man ja anbieten wenn klar ist das sie auch in eta-normalerer Form
    terminieren, was meistens der Fall sein sollte.
    Oder eta einfach selektiv dazuschalten, quasi als computational rule?
    Ist dann Aufgabe des Benutzers sicherzustellen das alles noch terminiert. *)
and normalize ctxt th =
  let val ctxt' = ctxt |> add_to_msg_trace (fn () =>
    "normalize on "^Display.string_of_thm ctxt th)
  in
    th |> rewrite_thm ctxt' 
    (* |> eta_convert *)
  end
and normalize_lesseta_withvars ctxt th =
  let val ctxt' = ctxt |> Variable.declare_thm th
  in th |> singleton (Variable.trade (fn ctxt'' => map (normalize_lesseta ctxt'')) ctxt') end
and normalize_withvars ctxt th =
  if no_comp_rules ctxt then
    normalize ctxt th
  else
    let val ctxt' = ctxt |> Variable.declare_thm th
    in th |> singleton (Variable.trade (fn ctxt'' => map (normalize ctxt'')) ctxt') end
  
and normalize_cterm ctxt ct =
  let val ctxt' = ctxt |> add_to_msg_trace (fn () =>
    "normalize_cterm on "^Syntax.string_of_term ctxt (Thm.term_of ct))
  in
    ct |> rewrite_cterm ctxt' |> Thm.rhs_of
  end
and normalize_term_conv ctxt t = 
  let val ctxt' = ctxt |> add_to_msg_trace (fn () =>
    "normalize_term_conv on "^Syntax.string_of_term ctxt t)
  in
    t |> cterm_of (Proof_Context.theory_of ctxt')
    |> rewrite_cterm ctxt'
  end
and normalize_term ctxt t = normalize_term_conv ctxt t
  |> Thm.rhs_of |> Thm.term_of




  
  

    (* TODO(feature): allgemeine Constraintmengen-Minimierung
          (reicht fuer Typklassen und Universenlevel-Inferenz)
      * vereinfache die aus metarec-Ableitungen entstandenen Constraints mit metarec zu implikational
        elementareren Constraints C_0
      * bilde schrittweisen Abschluss unter mehrkoepfigen Constraint-Propagierungsregeln
        (ggf. mit metarec Judgements als weiteren Annahmen die geloest werden muessen,
         insbes auch (globale) Unifikation die wie bei CHRs nicht backtrackbar ist)
        (ggf. artificially bounded Fixpunktbildung, aber Constraint-Propagierungsregeln
        sollten fuer gewoehnlich terminieren)
        (est unzertifizierte Termableitung wegen Unifvar in Constraints
        die bei Erfolg als Thmableitung rekonstruiert wird)
      * *urspruengliche* Constraints nochmal (implikational) vereinfachen, weil Unifikationen erfolgt sein koennen
        und jetzt unter Annahme der anderen *vervollstaendigten* Constraints, womit mehr
        bedingte Vereinfachungsregeln anspringen koennen
        (bei CHRs wuerden alle Constraints mit mehrkoepfigen Vereinfachungsregeln waehrend dem
        Propagierungsprozess vereinfacht; die mehrkoepfigen Vereinfachungsregeln muessten dann
        hier als Varianten dargestellt werden)
      * zu denjenigen Constraints c aus C_0 die durch Abschluss-Generierung ohne Nutzung von c "neu"
        erzeugt werden koennen, protokollieren wir das minimale (soweit innerhalb des bounds erreichte)
        C'_c mit C'_c ==> c
      * die vereinfachten Constraints <= C_0 sind dann diejenigen die nicht durch Abschluss-Generierung
        neu erzeugt werden koennen oder in einem C'_c vorkommen.
        Warnung an User bei Constraints die sich wechselseitig implizieren.
        Diese werden ja gemaess obigem beibehalten.  
        (Es gaebe hier natuerlich auch die Alternative nur den "ergiebigsten" der Constraints beizubehalten
        die sich wechselseitig implizieren, naemlich den der am meisten impliziert und dabei moeglichst
        wenig andere Constraints braucht.)

        Das Tracking welche constraints welche anderen implizieren muss wohl in der Form
        eine Tabellierung
          Constraint C |-> optional (wird impliziert von Constraints C_n und Theorem C_n ==> C dazu)
        erfolgen.
        Das deckt dann Forwaerts-Propagierungs und Vereinfachungsschritte ab:
          * bei Forwaerts-Propagierung werden die neuen Constraints vom alten Constraint impliziert
          * bei Vereinfachungs-Schritten wird das alte Constraint von den neuen impliziert.
        Um letztendlich die resultierende minimierte Constraintmenge zu berechnen geht man von
        urspruenglichen Constraints aus, und entfernt bzw. ersetzt (bei Vereinfachung)
        Constraints aus dieser Menge wenn Tracking eine nicht-wechselseitige Implizierung des
        Constraints ergeben hat. Dazu betrachten wir die transitiven Nachfolger-Mengen der
        urspruenglichlen Constraints im Hypergraphen des Implikations-Trackings
        (wobei wir die Implikationen dabei zusammenschalten): wenn diese Nachfolger-Menge zu
        einem Constraint C1 nicht ein anderes urspruengliches Constraint C2 enthaelt das C1 als
        Nachfolger hat, dann koennen wir C1 ersetzen durch seine Nachfolger-Menge.




        BEACHTEN: die Constraints die durch metarec-Ableitung generiert werden sind i.A. ja in HHF-Form
            !! fixes. assms ==> Constraint(fixes)
          also muss die Constraint-Propagierung und Vereinfachung unter fixes und assms stattfinden!!!

          Preprocessing: wenn sich Constraints nur in den Annahmen
          unterscheiden, dann schneidet man die Annahme-Mengen und nimmt nur
          eines der Constraints. Wenn sich Constraints nur in Fixes
          unterscheiden die nur in uninstantiierten
          Unifikationsvariablen-Applikationen genutzt werden, dann schneidet
          man die Fixes-Mengen und nimmst nur eines der Constraints.

          Propagierung: bei Anwendung einer Propagierungregel auf mehrere Constraints
          werden deren Fixes- und Annahme-Mengen vereinigt und die neu entstehenden
          Constraints erhalten diese vereinigten Fixes und Annahmen. Die Propagierungsregel
            [| G1 ;  ... ; Gk |] ==> H1 &&& .. &&& Hm ==> R1 &&& ... &&& Rn
          wird also gelifted zu
            [| lftd G1 ; ... ; lftd Gk |] ==> lftd H1 &&& .. &&& lftd Hm ==> lftd R1 &&& ... &&& lftd Rn
          wobei lftd die vereinigten Fixes und Annahmen voranstellt und vorkommende Unifvar
          ueber die vereinigten Fixes lifted.
          Die H1, .., Hm werden vor Regelanwendung dann so *abgeschwaecht*, dass sie die vereinigten Fixes und
          Annahmen aufweisen.

          Vereinfachung(dual zu Propagierung): bei Anwendung einer Vereinfacungsregel auf mehrere Constraints
          werden deren Fixes vereinigt und deren Annahme-Mengen geschnitten und die vereinfachten Constraints
          erhalten diese vereinigten Fixes und geschnittenen Annahmen. Die Vereinfachungsregel
            [| G1 ;  ... ; Gk ; constraint R1 ; ... ; constraint Rn |] ==> H1 &&& .. &&& Hm 
          wird also geliftet zu
            [| lftd G1 ;  ... ; lftd Gk ; lftd (constraint R1) ; ... ; lftd (constraint Rn) |]
            ==> lftd H1 &&& .. &&& lftd Hm 
          wobei lftd die vereinigten Fixes und geschnittenen Annahmen voranstellt und vorkommende Unifvar
          ueber die vereinigten Fixes lifted.
          Die H1, .., Hm werden vor Regelanwendung dann so *verstaerkt*, dass sie die vereinigten Fixes und
          geschnittenen Annahmen aufweisen.

          In der tracking-Tabelle stehen die Constraints dann ohne Fixes und Annahmen, d.h. mit loose bounds.

          ABER ERSTMAL behandeln wir nur den haeufigen Fall der scheinbar immer bei
          Universenlevel- und Typklassen-Inferenz vorliegt:
            die Annahmen werden nur zur Vereinfachung von Constraints genutzt die waehrend der metarec-Ableitung
            weiter instantiiert wurden und die Fixes von Constraints werden nur in Unifvar-Applikationen genutzt.
              Vermutlich ist das damit zu erklaeren das Constraints nur fuer universen-level, die immer
            als first-order betrachten werden koennen, oder fuer die Typisierung von freie Variablen im Input
            generiert werden, wo also lokale Annahmen und Fixes keine Rollen spielen duerfen.

            Also gehen wir wie folgt vor:
              * Vereinfachung der Constraints unter ihren Fixes und Annahmen.
              * Entfernung der Annahmen der resultierenden vereinfachten Constraints.
              * Unliften der Unifvar in den resultierenden Constraints (durch Instantiierung mit frischen
                ungelifteten Unifvar)
              * Check das Fixes nicht mehr in den resultierenden Constraints vorkommen und anschliessender
                Entfernung der Fixes-Quantifikationen.
              * Propagierung, Minimierung, weitere Vereinfachung der resultierenden Constraints
                ohne Fixes und Annahmen


            Mal probieren ob es nicht noch einfacher geht:
              beim Absetzen von constraints die vorkommenden Unifvar immer komplett unliften (d.h. mit ungelifteten
              Unifvar instantiieren) keine Fixes und Annahmen davor.





        Mehrkoepfige Vereinfachungsregeln sind bei mir reverse Implikationen und nicht Gleichheiten
        wie bei CHR, also allgemeiner:
          statt
            H1, .., Hm <=> G1, .., Gn | R1, .., Rk
          nutze ich
            [| G1 ; ... ; Gn ; constraint R1 ; ... ; constraint Rn |] ==> H1 &&& ... &&& Hm 

        Vorteil gegenueber CHRs:
          * Vereinfachungsregeln sind semantisch keine Gleichheiten sondern reverse Implikationen.
            Das brauchen wir fuer rekursive Dictionary-Konstruktions-Regeln.
            Sulzman et al nutzen das auch so!
          * CHRs leisten kurioserweise i.A. keine Minimierung der urspruenglichen Constraintmenge,
            sondern reichern diese an und vereinfachen lokal mehrkoepfig, d.h. vereinfachen
            nicht unter transitiver Propagierung.

            Wenn man Regeln A ==> B, B ==> C, A &&& B == A, B &&& C == B hat und mit
            Constraintmenge { A, C } startet, dann erhaelt man nach CHR-Saettigung { A, C }
              (bzw. Nicht-Termination weil { A, C } -> { A, B, C } == { A, C }
                oder auch { A, C } -> { A, B, C } == { A, B } -> { A, B, C } == { A, C })
            statt dem minimalen Resultatet { A }. Es fehlt die Vereinfachungsregel A &&& C == A.
    *)
    (* TODO(feature): Narrowing zur Constraint-Vereinfachung
         * Das bloede an Narrowing im Vgl zu CHRs ist das Narrowing nur funktioniert wenn mindestens
           ein Constraint eine lokal-eindeutige Loesung hat (d.h. Loesung dieses Constraints ist eindeutig,
           auch wenn man die anderen Constraints ausser Acht laesst).
           Nicht-konfluentes nicht-terminierendes verallgemeinertes Narrowing,
           also bounded, nicht-determ, mit Eindeutigkeitscheck und
           mit mehrkoepfigen Propagierungsregeln (?) waere wohl das coolste.
         * das Bloede an CHRs ist das man ein spezialisiertes Regelsystem braucht.
    *)
(* TODO(refactor): this contains an adaptation of the frules computation mechanism to propagation rules;
     can perhaps be realized with a common implementation, but the frules computation is completely ground *)

and constraint_simplification allow_propagation ctxt0 =
  let
    val gctxt0 = Context.Proof ctxt0
    val { constraint_propag_rules_hdidx, constraint_simp_rules_hdidx, ...} =
      get_current_ruledata gctxt0
    val { constraints=constraints0, ...} = get_the_run_state gctxt0

    val _ = tracing ("started constraint simplification on constraints\n  "
      ^commas (map (str_of_normed_term ctxt0) constraints0))

    (* simplification step (muessen konfluent sein):   prems ==> subgoals ==> conjunctioned heads
         * match simprule conclusion-heads against input constraints
         * solve premises of instantiated simprule (including subgoals)
           which potentially generates new constraints
         * form
             (% new_constraints. instantiated_simprule MP solved_premises(new_constraints))
             : new_constraints ==> conjunctioned input constraints
         * new constraints generated are added to constraint store
         * add new entries to tracking table:
             input constraint |-> new_constraints
               with proof
                 conj_concl_extr_prf (instantiated_simprule MP solved_premises)
                 : new_constraints ==> input constraint
           where
             conj_concl_extr_prf = (% R. (% new_constraint_prfs. conjDk_1 (... (conjDk_m (R new_constraint_prfs)) ..)))

      propagation step:   prems ==> conjunctioned heads ==> conjunctioned new constraints
         * rotate conjunctioned heads premise to front and curry proprule to format
             heads ==> prems ==> conjunctioned new constraints
           and rotate heads back to "implicational form"
             prems ==> heads ==> conjunctioned new constraints
         * match proprule heads against input constraints
         * solve premises of instantiated proprule and discharge to
             proprule' : input constraints ==> conjunctioned new constraints
         * add instantiated new constraints to constraint store
         * add new entries to tracking table:
             new constraint |-> input constraints
               with proof
                 conj_concl_extr_prf proprule' : input constraints ==> new constraint
           where
             conj_concl_extr_prf = (% R. (% inputCs. conjDk_1 (... (conjDk_m (R inputCs)) ..)))

      wenn neues constraint C hinzukommt:
        * versuchen *einen* simplification Schritt auszufuehren der C nutzt
        * wenn dies nicht geklappt hat, versuchen propagation Schritte auszufuehren die C nutzen
          (TODO: kann es interessant sein auch nicht maximal vereinfachte Constraints zu propagieren?)

      minimization
         * zu jedem urspruengliche Constraint die azyklische terminale Nachfolgermenge im
           tracking-Graphen mit Tiefensuche bilden (und dabei die Beweise verzahnen sodass ein Beweis
             Nachfolger ==> Constraint entsteht).
           Beachte das selbst-Abhaengigkeiten ignoriert werden sollen, was schon
           dadurch gegen sein sollte das man den tracking Graphen azyklisch ablaeuft.
           Breitensuche waere schlecht weil wir dann bei Tracking-Graph
             A -> {B, C}, B -> {C};  C -> {B}
           die Nachfolgermenge {B, C} fuer A ermitteln. Tiefensuche nutzt hier A -> B-> C um
           auf die minimalere Nachfolgermenge {C} zu kommen.
         * wenn die Nachfolgermenge zu einem Constraint C kein anderes Constraint C2 enthaelt
           das C als Nachfolger hat, dann kann man C durch seine Nachfolger ersetzen.
           Die Nachfolger werden also neue Constraints, C faellt raus und wir registrieren
             C |-> Nachfolger ==> C
           als Grund dafuer in Output-Tabelle 

    *)


    fun gen_with_pot_rules is_propagation
        pot_rules_with_C4head (constraint_graph0, ctxt0) = 
      let
        (* NB: only the first successful simplification rule is applied *)
        (* NB: eta-expanded for local polymorphism *)
        (* TODO(feature?): consider all head combinations and all potential rules when
             simplifying constraints. At least those that lead to simplifications of
             unsimplified constraints. But this is a performance cost and performance
             is the only reason to prefer simplification rules
               prems ==> (constraint new_C_i)_i ==> heads conj
             over propagations rules
               prems ==> heads conj ==> (new_C_i)_i conj *)
        fun fold_poss_rule_ress f =
          if is_propagation then fold_with_change_tracking f
          else fold_upto_first_change f

        fun do_pot_rule (rule, C4head) (constraint_graph, ctxt) =
          let
            exception UnsolvablePrem

            (* val _ = tracing ("considering constraint propagation rule\n  "
              ^Display.string_of_thm ctxt rule
              ^"\non selected input constraint\n  "
              ^string_of_int (fst C4head)^": "^str_of_normed_term ctxt (snd C4head)) *)

            val nprems =
              if is_propagation then Thm.nprems_of rule - 1
              else Thm.nprems_of rule
            val nheads =
              let val ct = 
                  if is_propagation then
                    Drule.cprems_of rule |> List.last
                  else
                    cconcl_of rule
              in
                Conjunction.dest_conjunctions ct |> length
              end

            (* prems ==> [ propagation rule heads as implications ]
                ==> new constraints for propag rules  or  conjunction heads for simp rules *)
            val implicational_rule =
              if is_propagation then
                (* transform  prems ==> conj heads ==> conj concl  into  prems ==> heads ==> conj concl  *)
                rule |> Drule.rotate_prems nprems |> Conjunction.curry_balanced nheads
                |> Drule.rotate_prems (~ nprems)
              else
                rule

            fun fresh_rule_in_ctxt ctxt_ =
              let
                val (prf, ctxt_2) = fresh_thm_prf implicational_rule ctxt_
                val rl_prop = prop_of_proofp prf

                val ((prems, heads), static_new_constraints_opt) =
                  let val concl_conjs_dest = Logic.strip_imp_concl #> Logic.dest_conjunctions
                  in
                    if is_propagation then
                      (Logic.strip_imp_prems rl_prop |> chop nprems, SOME (concl_conjs_dest rl_prop))
                    else 
                      ((Logic.strip_imp_prems rl_prop, concl_conjs_dest rl_prop), NONE)
                  end
              in ((prf, prems, heads, static_new_constraints_opt), ctxt_2) end

            val ((_, _, heads0, _), ctxt2) = fresh_rule_in_ctxt ctxt
               
            fun lookup head =
              let
                val res = 
                  Net.unify_term constraint_graph (Envir.eta_contract head)
                  |> filter (fn (C', _) => pattern_match_envctxt ctxt2 (head, C') |> is_some)
                  |> map fst
                (* val _ = tracing ("lookup for head "^Syntax.string_of_term ctxt2 head
                  ^" returned\n  "^commas (map (str_of_normed_term ctxt2) res)) *)
              in res end
            val cs_for_heads_posprod = heads0 |> map_index (fn (i,head) =>
                 let val (headidx, C) = C4head
                 in
                   if headidx = i then [C]
                   else lookup head
                 end)
               |> list_amb
            (* val _ = tracing ("cs_for_heads_posprod: \n"
              ^cat_lines (cs_for_heads_posprod |> map (commas o (map (str_of_normed_term ctxt2))))) *)


            fun inst_and_apply_rule cs_for_heads i (constraint_graph, ctxt2) =
              let
                val ((prf, prems, heads, static_new_constraints_opt), ctxt3) = fresh_rule_in_ctxt ctxt2
                val rl_prop = prop_of_proofp prf
              in
              case pattern_matches_envctxt ctxt3 (heads, cs_for_heads) of
                NONE =>
                  let
                    val _ = () (* tracing (string_of_int i^":  tried application of constraint propagation rule\n  "
                          ^Display.string_of_thm ctxt3 rule
                          ^"\nto input constraints\n  "
                          ^commas (map (str_of_normed_term ctxt3) cs_for_heads)
                          ^"\nbut inputs did not match heads\n  "
                          ^commas (map (Syntax.string_of_term ctxt3) heads)
                          ^"\n(normalized heads) are\n  "
                          ^commas (map (str_of_normed_term ctxt3) heads)) *)
                  in NONE end
              | SOME ctxt4 => 
                  (* TODO(feature): renaming of bound variables in rule to share them with input constraints *)
                  let
                    (* val _ = tracing (string_of_int i^":  applying constraint "
                          ^(if is_propagation then "propagation" else "simplification")^" rule\n  "
                          ^Display.string_of_thm ctxt4 rule
                          ^"\nto input constraints\n  "
                          ^commas (map (str_of_normed_term ctxt4) cs_for_heads)
                          ^"\nSolving the following prems now:\n"
                          ^commas (map (str_of_normed_term ctxt4) prems)) *)

                    fun global_fail_cont ctxt_ msg = 
                      err_with_trace_and_facts ctxt_
                        ("failed to solve a premise in an instantiated constraint "
                          ^(if is_propagation then "propagation" else "simplification")
                          ^" rule\n"
                          ^str_of_normed_term ctxt_ rl_prop
                          ^"\n\nbecause:\n"^msg)
                    fun local_fail_cont _ _ = raise UnsolvablePrem


                    val ctxt4_ = ctxt4 |> Context.proof_map (map_constraints_in_run_state
                      (K (these static_new_constraints_opt)))
                    val (solved_prems, ctxt5_) = solve_prems false false global_fail_cont local_fail_cont
                      rl_prop prems ctxt4_
                    val new_constraints = get_constraints_in_run_state ctxt5_
                    val new_dynamic_constraints = new_constraints
                      |> subtract (aconv_norm (norm_with_env_in_run_state ctxt5_))
                           (these static_new_constraints_opt)
                    val _ =
                      if is_propagation andalso not (null new_dynamic_constraints) then
                        err_with_trace ctxt5_ ("application of constraint propagation rule\n  "
                          ^Display.string_of_thm ctxt5_ rule
                          ^"\nto input constraints\n  "
                          ^commas (map (str_of_normed_term ctxt5_) cs_for_heads)
                          ^"\nresulted in new dynamic constraints\n  "
                          ^commas (map (str_of_normed_term ctxt5_)  new_dynamic_constraints))
                      else ()
                    val ctxt5 = ctxt5_ |> Context.proof_map (map_constraints_in_run_state
                      (K (get_constraints_in_run_state ctxt4)))

                    (* val _ = tracing ("applied constraint "
                          ^(if is_propagation then "propagation" else "simplification")^" rule\n  "
                          ^Display.string_of_thm ctxt5_ rule
                          ^"\nto input constraints\n  "
                          ^commas (map (str_of_normed_term ctxt4) cs_for_heads)
                          ^"\nresulted in new constraints\n  "
                          ^commas (map (str_of_normed_term ctxt5_) new_constraints)) *)

                    (* for propag rules:  input constraints ==> conjunctioned new constraints
                       for simp rules:  new_constraints ==> conjunctioned input constraints *)
                    val disch_prf = prf |> fold (mp_rev_prf ctxt5) solved_prems
                      |> fold_rev (impI_prf ctxt5) new_dynamic_constraints

                    (* for propag rules:  (new constraint i, proof of (input constraints ==> new constraint i))_i
                       for simp rules:  (input constraint i, proof of (new_constraints ==> input constraint i))_i *)
                    val (concls_prfs, ctxt6) = conj_concl_extr_prfs disch_prf ctxt5

                    (* NB: determination of existing constraints that have been instantiated now relies on the facts that
                         * constraints in the constraint graph are fully normalized 
                         * type unification variables are not instantiated during this derivation process *)
                    val inst_old_Cs = constraint_graph |> Net.content |> map fst
                      |> filter (fn C => Term.add_vars C [] |> exists (fn ixnT =>
                           Envir.lookup (get_the_env_in_run_state ctxt6, ixnT) |> is_some))

                    (* val _ = if null inst_old_Cs then ()
                      else
                        tracing ("the following existing constraints have been instantiated:\n"
                          ^commas (inst_old_Cs |> map (Syntax.string_of_term ctxt6))) *)
                    
                    val (constraint_graph2, ctxt7) = (constraint_graph, ctxt6)
                      |> fold (fn inst_old_C => reg_constraint true inst_old_C NONE NONE)
                           inst_old_Cs
                  in
                    if is_propagation then
                      (constraint_graph2, ctxt7)
                      |> fold (fn (new_constr, new_constr_prf) => 
                             if new_constr aconv (Data.mk_Trueprop Data.True) then
                               I
                             else
                               reg_constraint false new_constr (SOME rl_prop) (SOME new_constr_prf))
                           concls_prfs
                      |> SOME
                    else
                      (constraint_graph2, ctxt7)
                      |> fold (fn (inp_constr, inp_constr_prf) =>
                             (* NB: since inp_constr always already exists in the constraint graph,
                                this just ensures a proof for it is registered *)
                             reg_constraint false inp_constr (SOME rl_prop) (SOME inp_constr_prf))
                           concls_prfs
                      |> fold (fn new_constr => reg_constraint false new_constr (SOME rl_prop) NONE)
                           new_constraints
                      |> SOME
                  end
              end
          in
            (constraint_graph, ctxt2)
            |> fold_poss_rule_ress (fn (cs_for_heads, i) => fn (constraint_graph_, ctxt_) =>
                   inst_and_apply_rule cs_for_heads i (constraint_graph_, ctxt_)
                   handle UnsolvablePrem => NONE)
                 (cs_for_heads_posprod ~~ (1 upto (length cs_for_heads_posprod)))
          end
      in
        (constraint_graph0, ctxt0)
        |> fold_poss_rule_ress do_pot_rule pot_rules_with_C4head
      end


    (* TODO(feature): tracking of serveral implications leading to a constraint *)
    (* NB: force_reconsideration does *NOT* affect the constraints that are generated from this one,
         because the ones that are affected by an instantiation after their generation are all
         collected determined directly from the constraint graph *)
    and reg_constraint force_reconsideration C0
        origin_rule_app_opt implied_by_opt (constraint_graph, ctxt) = 
      let
        val C = norm_with_env_in_run_state ctxt C0
        val C_eta = C |> Envir.eta_contract
        (* val _ = tracing ((if force_reconsideration then "forced to re" else "")
          ^"considering constraint "^Syntax.string_of_term ctxt C) *)
          (*^"\n  constraint graph contains\n "
          ^commas (Net.content constraint_graph |> map (fst #> Syntax.string_of_term ctxt))*)

        val eq_C = aconv_norm (norm_with_env_in_run_state ctxt)
        val existing_C_entries = Net.match_term constraint_graph C_eta
          |> filter (fn (C', _) => eq_C (C', C))
        (* val _ = tracing ("existing_C_entries are:\n"
          ^cat_lines (existing_C_entries |> map (fst #> str_of_normed_term ctxt))) *)
        val exists_already = not (null existing_C_entries)
        val implied_by_already_opt = existing_C_entries |> map_filter snd |> try hd 

        fun readd_C_with implied_by_opt_ =
          constraint_graph
          |> fold (fn (C', _) =>
               (* NB: deletion from net expects precise term, not an instantiation of it,
                    so we cannot use C_eta for this.
                  We use deletion that is tolerant of non-existing C' because there can be serveral
                  distinct C' with the same key-approximation, which are now identified with C and are
                  thus all pruned by the first such net deletion *)
               Net.delete_term_safe (apsnd fst #> eq_C) (Envir.eta_contract C', C'))
             existing_C_entries
          |> Net.insert_term (pairself fst #> eq_C) (C_eta, (C, implied_by_opt_))

        val constraint_graph' =
          if exists_already then
            (if is_some implied_by_already_opt orelse not (is_some implied_by_opt) then
              (if force_reconsideration then
                (* to keep C normalized in net and to achieve absorption after instantiation *)
                readd_C_with implied_by_already_opt
              else
                constraint_graph)
            else
              readd_C_with implied_by_opt)
          else
            constraint_graph |> Net.insert_term (pairself fst #> eq_C) (C_eta, (C, implied_by_opt))
      in
        if exists_already andalso not force_reconsideration then
          let val _ = () (* tracing ("constraint "^Syntax.string_of_term ctxt C^" exists already") *)
          in
            (constraint_graph', ctxt)
          end
        else
          let
            (* val _ = tracing ("generated new constraint "^Syntax.string_of_term ctxt C
              ^" implied by \n  "^
                (case implied_by_opt of
                  SOME prf => str_of_normed_term ctxt (prop_of_proofp prf)
                | NONE => "nothing")
              ^"\n  originating from "
                ^(case origin_rule_app_opt of
                   SOME rl => str_of_normed_term ctxt rl
                 | NONE => "initial constraints or instantiation of existing constraint")) *)
            val ext_with_C0 = map (fn (rl, head_idx) => (rl, (head_idx, C0)))
            val pot_simp_rls = Net.match_term constraint_simp_rules_hdidx C_eta |> ext_with_C0
            val pot_propag_rls =
              if allow_propagation then
                Net.match_term constraint_propag_rules_hdidx C_eta |> ext_with_C0
              else []

            (* val _ = tracing ("reg_constraint: considering \"new\" fact\n    "^Display.string_of_thm ctxt2 fact) *)

            (* val _ = tracing ("pot_frules for new fact \n"
              ^ Display.string_of_thm ctxt2 fact
              ^"\nare\n"^cat_lines (map (Display.string_of_thm ctxt2 o get_frule frules o fst) pot_frules)) *)
            val res1_opt = (constraint_graph', ctxt)
              |> gen_with_pot_rules false pot_simp_rls
          in
            (* only apply propagation rule if no simplification rule was successful *)
            case res1_opt of
              SOME res1 => res1
            | _ =>
                (constraint_graph', ctxt)
                |> gen_with_pot_rules true pot_propag_rls 
                |> the_default (constraint_graph', ctxt)
          end
      end


     (* constraint store with tracking which other constraints optionally imply this constraint *)
    val constraint_graph0 = Net.empty : (term * proof_pack option) Net.net
    val (constraint_graph', ctxt') = (constraint_graph0, ctxt0)
      |> fold (fn C => reg_constraint false C NONE NONE) constraints0
    val eq_C = aconv_norm (norm_with_env_in_run_state ctxt')


    val constraints0_varixns = [] |> fold Term.add_vars constraints0 |> map fst
    val envdiff = get_the_run_state (Context.Proof ctxt') |> #env |> Envir.term_env |> Vartab.dest
      |> filter (fn (ixn, _) => member (op =) constraints0_varixns ixn)
      |> subtract (pairself fst #> (op =))
           (get_the_run_state (Context.Proof ctxt0) |> #env |> Envir.term_env |> Vartab.dest)
    val _ = tracing ("resulting instantiation is:\n  "
      ^commas (envdiff |> map (fn (ixn, (T, t)) =>
         Syntax.string_of_term ctxt' (Var(ixn,T)) ^ " := "
         ^ str_of_normed_term ctxt' t)))
    val _ = tracing ("resulting constraint graph is:\n"
      ^cat_lines (Net.content constraint_graph'
        |> map (fn (C, implied_by_opt) =>
             "  "^str_of_normed_term ctxt' C ^"  implied by  "
             ^(case implied_by_opt of
                NONE => "nothing"
              | SOME prf => str_of_normed_term ctxt' (prop_of_proofp prf)))))

    (* returns (constraints that C0 depends on, proof of C0 based on assumed dependencies)
       if a constraint is not simplified according to the constraint graph, it has a self-dependency;
       when discovering cycles we locally give up and share dependency results *)
    fun calc_dependencies C0 (walked, calced) =
      let
        val C = norm_with_env_in_run_state ctxt' C0
        val C_eta = C |> Envir.eta_contract
        fun triv_dep C2 = ([C2], assumption_prf C2)
      in
        case 
          Net.match_term walked C_eta
          |> filter (fn C' => eq_C (C', C))
        of
          _ :: _ => (triv_dep C0, (walked, calced)) (* encountered cycle *)
        | [] => 
            case
              Net.match_term calced C_eta
              |> filter (fn (C', _) => eq_C (C', C))
            of
              (_, res) :: _ => (res, (walked, calced))
            | [] =>
                let
                 (* TODO(correctness): constraints koennen durch unification waehrend der Propagierung
                      zusammenfallen.
                        Deshalb beruecksichtigen wir bei der Dependency-Berechnung nicht nur den ersten,
                      sondern auch die weiteren matchenden Eintraege im constraint Netz, bis wir einen
                      Eintrag mit Vereinfachungsbeweis zum Constraint finden.
                      Sollte das auch beim Anlegen dieser Eintraege waehrend der Propagierung so gemacht werden? 
                      Ist mittlerweile schon so? *)
                  val implied_by_opt =
                    case Net.match_term constraint_graph' C_eta
                      |> filter (fn (C', _) => eq_C (C', C))
                    of
                      [] => err_with_trace ctxt' ("internal error when calculating dependencies: constraint "
                        ^str_of_normed_term ctxt' C^" was not found in constraint graph")
                    | C'_and_implied_by_opts => C'_and_implied_by_opts |> map_filter snd |> try hd

                  val (res, (walked3, calced2)) =
                    case implied_by_opt of
                      NONE => (triv_dep C0, (walked, calced))
                    | SOME implied_by_prf =>
                       let
                         val walked2 = walked |> Net.insert_term eq_C (C_eta, C)
                         val Cs = Logic.strip_imp_prems (prop_of_proofp implied_by_prf)
                         val (Cs_ress, (walked3, calced2)) = (walked2, calced)
                           |> fold_map calc_dependencies Cs
                         val deps = [] |> fold (union eq_C) (map fst Cs_ress)
                         val prf = implied_by_prf |> fold (mp_rev_prf ctxt' o snd) Cs_ress
                       in
                         ((deps, prf), (walked3, calced2))
                       end

                   val calced3 = calced2 |> Net.insert_term (pairself fst #> eq_C) (C_eta, (C, res))
                in
                  (res, (walked3, calced3))
                end
      end


    val constraints0_nodups = constraints0 |> distinct eq_C

    val constraints0_deps = constraints0_nodups |> map (fn C =>
      let
        val ((deps, prf), (walked, _)) = calc_dependencies C (Net.empty, Net.empty)
        val used = union eq_C deps (Net.content walked)
      in (C, (deps, prf, used)) end)

    val implied_constraints = constraints0_deps |> map_filter (fn (C, (deps, prf, used)) =>
      if member eq_C deps C
      then (* C is not implied by other constraints *)
        NONE
      else if constraints0_deps |> exists (fn (C', (_, _, used')) =>
          not (eq_C (C, C')) andalso member eq_C used' C andalso member eq_C used C')
      then
        (* mutually dependent *original* constraints C, C' are both retained,
           even if they have both been simplified further
           (i.e. they are both not terminal in the constraint graph) *)
        NONE
      else
        SOME (C, (deps, prf)))

    val constraints' = constraints0_nodups |> subtract eq_C (map fst implied_constraints)
      |> fold (union eq_C) (map (fn (_, (deps, _)) => deps) implied_constraints)

    val implied_constraints_res = implied_constraints
      |> map (fn (C, (_, prf)) => (C, prf (* |> fold_rev (impI_prf ctxt') constraints' *)))
  in
    ((constraints', implied_constraints_res), ctxt')
  end


and metarec_constraint_simp final_C_simp prf ctxt =
  let
    val {constraints, ...} = get_the_run_state (Context.Proof ctxt)
    (* TODO: If the newly generated constraints still carry fixes or assumes then
         provide an error message. *)
    (* NB: try to simplify constraints with fixes or assumes by solve_prems and replace them with the newly
         generated constraints.  Note that constraint_gen_proc automatically generates constraints
         with as few fixes and assumes as possible.  *)
    (* NB: checking if fixes and assumes of constraints have become non-relevant due to later unifications
         eliminating them in this case already happens if they are newly generated from their solve_prems call *)

    val _ = tracing ("metarec_constraint_simp started on constraints  "^
      commas (map (str_of_normed_term ctxt) constraints))

    val (prf2, ctxt2) = (prf, ctxt) |> fold (fn C0 => fn (prf_, ctxt_) =>
        if false (* null (Logic.strip_params C0) andalso null (Logic.strip_assums_hyp C0) *) then
          (prf_, ctxt_)
        else
          let
            val C = norm_with_env_in_run_state ctxt_ C0
            exception ConstraintSimpFailed
            fun fail_cont ctxt_ msg =
              let val _ = tracing
                ("failed to simplify a constraint "(*^"with fixes or assumes: "*)
                ^str_of_normed_term ctxt_ C
                ^"\n\nbecause:\n"^msg)
              in
                raise ConstraintSimpFailed
              end

            val ctxt_2 = ctxt_ |> Context.proof_map (map_constraints_in_run_state (K []))
          in
            case (SOME (solve_prems false false fail_cont fail_cont C [C] ctxt_2)
               handle ConstraintSimpFailed => NONE)
            of
              NONE => (prf_, ctxt_)
            | SOME ([C_prf], ctxt_3) =>
                let
                 val eq_C = (aconv_norm (norm_with_env_in_run_state ctxt_3))

                 (* val _ = tracing ("simplified constraint  "^str_of_normed_term ctxt_3 C
                   ^"  to\n"^cat_lines (map (str_of_normed_term ctxt_3 #> curry (op ^) "  ")
                     (get_the_run_state (Context.Proof ctxt_3) |> #constraints)))
                 val _ = tracing "replaying proof of constraint simplification ..."
                 val _ = tracing ("  delayed unifs are "
                   ^commas (get_delayed_unifs_in_run_state ctxt_3
                      |> map (fst #> Logic.mk_equals #> str_of_normed_term ctxt_3)))  *)
                 val _ = replay_prf ctxt_3 (C_prf
                   |> fold_rev (impI_prf ctxt_3) (get_constraints_in_run_state ctxt_3) 
                   |> fold_rev (impI_prf ctxt_3 o Logic.mk_equals o fst) (get_delayed_unifs_in_run_state ctxt_3)) (* for testing *)
                 (* val _ = tracing "  done" *)

                 val ctxt_4 = ctxt_3 |> Context.proof_map (map_constraints_in_run_state
                   (union eq_C (get_constraints_in_run_state ctxt_ |> remove eq_C C)))
                 val prf_2 = prf_ |> impI_prf ctxt_4 C |> mp_rev_prf ctxt_4 C_prf

                 (* val _ = tracing "replaying proof with simplified constraint ..."
                 val _ = tracing ("  delayed unifs are "
                   ^commas (get_delayed_unifs_in_run_state ctxt_4
                      |> map (fst #> Logic.mk_equals #> str_of_normed_term ctxt_4)))  *)
                 val _ = replay_prf ctxt_4 (prf_2
                   |> fold_rev (impI_prf ctxt_4) (get_constraints_in_run_state ctxt_4)
                   |> fold_rev (impI_prf ctxt_4 o Logic.mk_equals o fst) (get_delayed_unifs_in_run_state ctxt_4)) (* for testing *)
                 (* val _ = tracing "  done" *)
                in
                  (prf_2, ctxt_4)
                end
          end)
      constraints

    val ((constraints', implied_constraints), ctxt3) = constraint_simplification true ctxt2
    val prf3 = prf2
      |> fold (fn (C, C_prf) => impI_prf ctxt3 C #> mp_rev_prf ctxt3 C_prf) implied_constraints
      |> final_C_simp ? (fold_rev (impI_prf ctxt3) constraints')

    (* NB: if final_C_simp = true all remaining constraints' have been implicationally discharged,
       but we keep registered in the run state anyway *)
    val ctxt4 = ctxt3 |> (Context.proof_map (map_constraints_in_run_state (K constraints')))
  in
    (prf3, ctxt4)
  end


and metarec_structural_unifications final_unifs prf ctxt = 
  let
    val {env, delayed_unifs, ...} = get_the_run_state (Context.Proof ctxt)

    val (delayed_unifs2, env2) =
      try_solve_delayed_unifs false ctxt delayed_unifs env
      handle TryPatUnify (ctxt_, (bad_t1, bad_t2), msg) =>
        err_with_trace ctxt_ ("metarec: solving of a delayed unification problem failed: "^msg)

      (* TODO(feature): add optional fallback to FO-unif to deal with type
           constructor polymorphism? But using (m ` i ` a) or rather
           (m ~` a), where (~`) is elaborated to (` ?i `), is better anyway. *)
      (* TODO(feature): interleave structural unification with constraint simplification
           (interleaving with pattern unifications is automatic via unify_proc),
           instead of applying constraint simplification before and after all forced
           structural unifications *)
    val struct_unify = true
    val (delayed_unifs3, env3) =
        (if struct_unify then
          try_solve_delayed_unifs true ctxt delayed_unifs2 env2
        else
          (delayed_unifs2, env2))
      handle TryStructUnify (ctxt_, (bad_t1, bad_t2), msg) =>
        err_with_trace ctxt_ ("metarec: solving of a delayed unification problem structurally failed: "^msg)

    val solved_delayed_unifs = delayed_unifs3 |> filter snd |> map fst
    val unsolved_delayed_unifs = delayed_unifs3 |> filter_out snd |> map fst

    (* val _ =
      let
        val envdiff = env3 |> Envir.term_env |> Vartab.dest
          |> subtract (pairself fst #> (op =)) (Envir.term_env env |> Vartab.dest)
      in 
        tracing ("unification pass solved delayed unification problems\n  "
        ^commas (solved_delayed_unifs |> (map
          (Logic.mk_equals #> Envir.norm_term env #> Syntax.string_of_term ctxt)))
        ^"\nresulting in term instantiations:\n  "
        ^commas (envdiff |> map (fn (ixn, (T, t)) =>
           Syntax.string_of_term ctxt (Var(ixn,T)) ^ " := "
           ^ str_of_normed_term ctxt t)))
      end *)

    (* NB: if first-order unification variables could have been instantiated
       to a lifting during structural unification, so do transitive unlifting now. *)
    val {fo_vars, ...} = get_the_run_state (Context.Proof ctxt)
    val ctxt2 = ctxt |> Context.proof_map (map_env_in_run_state (K env3))
      |> fold (fn fo_var => fn ctxt_ =>
             case Vartab.lookup (Envir.term_env env3) fo_var of
               SOME (_, t) =>
                 let val _ = () (* tracing ("unlifting unification variables in instantiation "
                    ^"of first order variable:   "
                    ^Syntax.string_of_term ctxt_ (Var (fo_var, Term.fastype_of t))
                    ^" := "^str_of_normed_term ctxt_ t) *)
                 (* NB: we rely on env-normalization of t inside unlift_unifvar_occs *)
                 in unlift_unifvar_occs t ctxt_ end
             | NONE => ctxt_)
           fo_vars


    val (prf2, ctxt3) = (prf, ctxt2) |> fold (fn (t1, t2) => fn (prf_, ctxt_) =>
         let
           val P = Logic.mk_equals (t1, t2)
           val (refl_t1_prf, ctxt_2) = reflexive_prf t1 ctxt_
         in
           (prf_ |> impI_prf ctxt_2 P |> mp_rev_prf ctxt_2 refl_t1_prf, ctxt_2)
         end)
       solved_delayed_unifs

    val prf3 = prf2
      |> final_unifs ? (fold_rev (fn (t1, t2) =>
             let val P = Logic.mk_equals (t1, t2)
             in impI_prf ctxt3 P end)
           unsolved_delayed_unifs)

    (* NB: the unification problems that are still unsolved have been implicationally discharged
       if final_unifs = true, but we keep them registered as delayed in the run state anyway *)
    val ctxt4 = ctxt3 |> Context.proof_map (map_delayed_unifs_in_run_state
      (K (map (rpair false) unsolved_delayed_unifs)))
  in
    (prf3, ctxt4)
  end


(* pobj, iobjs  may not contain any Vars
   metarec calculates beta,comp_rule-normal  oobjs  with  J pobj iobjs oobjs *)
(* Note: for implicit toplevel GEN: because of the successful groundness check all variables that
     are present after metarec execution are unification variables that have been introduced in the derivation,
     so just instantiate all of them to freshly fixed free variables that will be schematically quantified
     on export later on. Doesn't this take place in replay_prf already?  *)
and metarec_with_failcont failcont ctxt0 jid (pobj, iobjs) =
  let
    val thy = Proof_Context.theory_of ctxt0
    val unfxd_free_ns = fold Term.add_free_names (pobj :: iobjs) []
      |> filter_out (Variable.is_fixed ctxt0)
    fun inputmsg () = 
           "metarec: on judgement "^quote jid^" with input ("
             ^Syntax.string_of_term ctxt0 pobj^", ["^Library.commas (map (Syntax.string_of_term ctxt0) iobjs)^"])"
    (* val _ = tracing ("metarec: fixing frees "^commas unfxd_free_ns^" for\n  "^inputmsg ()) *)
    val ctxt = ctxt0
      |> add_to_msg_trace inputmsg
      |> Variable.add_fixes_direct unfxd_free_ns
      |> fold Variable.declare_term (pobj :: iobjs)
      |> (fn ctxt => ctxt |> Context.proof_map (set_run_state (init_run_state ctxt) #> set_assms []))

    (* val _ = tracing ( "metarec: on judgement "^quote jid^" with input ("
      ^Syntax.string_of_term ctxt0 pobj^", ["^Library.commas (map (Syntax.string_of_term ctxt0) iobjs)^"])") *)
    (* val _ = tracing ("metarec: declared constraints are "
      ^(Variable.constraints_of ctxt |> fst |> Vartab.dest |> filter (fn ((n, ix), _) => ix = ~1)
        |> map (fn ((n, _), t) => Free(n,t) |> Syntax.string_of_term ctxt) |> commas)) *)

    val pobj' = normalize_term ctxt pobj
    val iobjs' = map (normalize_term ctxt) iobjs

    val ((prf, oobjs), ctxt2) = metarec_worker true ctxt (SOME failcont) jid (pobj', iobjs')

    (* val _ = tracing ("metarec derivation was successful (but no replay tried yet) with: "
          ^str_of_normed_term ctxt2 (prop_of_proofp prf)) *)
    (* val _ = 
      let
        val {delayed_unifs, constraints, ...} = get_the_run_state (Context.Proof ctxt2)
        val th_1 = prf |> fold_rev (impI_prf ctxt2) (map (Logic.mk_equals o fst) delayed_unifs @ constraints)
          |> replay_prf ctxt2 
      in
        tracing ("metarec derivation was successful (but no constraint min yet) with: "
          ^Display.string_of_thm ctxt2 th_1)
       end *)

    val (prf2, ctxt3) = metarec_constraint_simp false prf ctxt2
    (* val _ = 
      let
        val {delayed_unifs, constraints, ...} = get_the_run_state (Context.Proof ctxt3)
        val _ = tracing ("replaying proof after constraint min")
        val _ = tracing ("  delayed unifs are "
          ^commas (get_delayed_unifs_in_run_state ctxt3
             |> map (fst #> Logic.mk_equals #> str_of_normed_term ctxt3))) 
        val th_2 = prf2 |> fold_rev (impI_prf ctxt3) (map (Logic.mk_equals o fst) delayed_unifs @ constraints)
          |> replay_prf ctxt3 
      in
        tracing ("proof replay after constraint min: "^Display.string_of_thm ctxt3 th_2)
      end *)

    val (prf3, ctxt4) = metarec_structural_unifications false prf2 ctxt3
    (* val _ = 
      let
        val {constraints, ...} = get_the_run_state (Context.Proof ctxt4)
        val _ = tracing ("replaying proof after structural unifications")
        (* val _ = tracing ("  delayed unifs are "
          ^commas (get_delayed_unifs_in_run_state ctxt4
             |> map (fst #> Logic.mk_equals #> str_of_normed_term ctxt4)))  *)
        val th_3 = prf3 |> fold_rev (impI_prf ctxt4) constraints
          |> replay_prf ctxt4 
      in
        tracing ("proof replay after structural unifications: "^Display.string_of_thm ctxt4 th_3)
      end *)

    val (prf4, ctxt5) =  metarec_constraint_simp true prf3 ctxt4

    (* NB: we always need a final pass for structural unifications after the last constraint simplification pass.
         Still necessary now that contextual discharge of typing constraints works without unification? *)
    val (prf5, ctxt6) = metarec_structural_unifications true prf4 ctxt5

    (* val _ = tracing ("replaying final proof for  "^str_of_normed_term ctxt6 (prop_of_proofp prf5)) *)
      (* TODO(opt): nur close_derivation machen wenn die Ableitung gross genug war ?! *)
      (* TODO(feature): try to un-normalize to original judgement? *)
    val th = replay_prf ctxt6 prf5 |> Thm.close_derivation

    val {delayed_unifs=delayed_unifs', constraints=constraints', ...} = get_the_run_state (Context.Proof ctxt6)
  in
    ((th, oobjs), (delayed_unifs' |> filter_out snd |> map fst, constraints'))
  end


and metarec ctxt jid (pobj, iobjs) =
  metarec_with_failcont err_with_trace ctxt jid (pobj, iobjs)

(* FIXME?: undischarged unification problems cannot be represented as hyps in a thm, therefore this is stupid.
     same for constraints containing unification variables *)
and metarec_fully_discharged ctxt jid (pobj, iobjs) =
  let
    val ((th, oobjs), (delayed_unifs, constraints)) = metarec ctxt jid (pobj, iobjs)
    val th' = th (* |> fold (fn C => Thm.implies_intr (cterm_of (Proof_Context.theory_of ctxt) C))
      (constraints @ map Logic.mk_equals delayed_unifs) *)
  in
    (th', oobjs)
  end

and metarec_no_constraints ctxt jid (pobj, iobjs) = 
  let
    val ((th, oobjs), (delayed_unifs, constraints)) = metarec ctxt jid (pobj, iobjs)
    val _ =
      if not (null delayed_unifs) then
        err_with_trace ctxt ("metarec_no_constraints: delayed unification problems "
          ^commas (delayed_unifs |> map (fn t1_t2 => Syntax.string_of_term ctxt (Logic.mk_equals t1_t2)))
          ^" remained")
      else if not (null constraints) then
        err_with_trace ctxt ("metarec_no_constraints: constraints "
          ^commas (constraints |> (map (Syntax.string_of_term ctxt)))
          ^" remained")
      else ()
  in
    (th, oobjs)
  end








(* TODO(correctness):
     * ordentlicher check fuer Annahmen fehlt noch: sie sind wieder brules

       Annahmen die lokalen frules entsprechen auch erlauben??
       Was ist mit dependency graph??

       was wenn Annahme eine Praedikatenvariable ist die erst bei Animation
       zu einer brule instantiiert wird? Dann halt dynamischer Check das es
       eine brule ist?

       well-modedness der Annahmen braucht man nicht weil alle in Annahmen
         vorkommenden Variablen available (= ground ?) in sein muessen
         deshalb keine mode-Premissen auf Praedikatenvariablen noetig
         die man dynamisch durch nachschauen des Judgements kontrollieren muesste *)
(* TODO(feature): checken das kein brule in Annahmen benutzt wird. das war ein
     haeufiger Fehler von mir *)
(* FIXME: Spezialbehandlung von freshunifvar (fuehrt nicht zu Fakten-Inkonsistenz bei gleichem Input ()) *)
(* "Premissen" entspr. goal clauses in lambdaProlog
   "Annahmen" entspr. definite clauses die in Implikationen vor Goals benutzt werden *)
and check_prem ctxt may_have_lthy_transforms check_groundness prem (seen_lthy_transf, (avail_vars, avail_tvars, juds)) =
  let
    val gctxt = Context.Proof ctxt
    val {lthy_transforms, ...} = get_current_ruledata gctxt
    val _ =
      if Drule.is_norm_hhf prem then ()
      else err_with_trace ctxt ("check_prem: premise   "^Syntax.string_of_term ctxt prem
        ^"   not in hhf normal form")

    val params0 = Logic.strip_params prem
    val (freshns, ctxt2) = Variable.variant_fixes (map fst params0) ctxt
    val params = freshns ~~ (map snd params0) |> map Free
    val prem_concl = Term.subst_bounds (rev params, Logic.strip_assums_concl prem)
    val prem_assms = Logic.strip_assums_hyp prem |> map (curry Term.subst_bounds (rev params))

    fun check_no_additional_vars msg t = 
       let
         val vars = Term.add_vars t []
         val tvars = Term.add_tvars t []
         val bad_vars = vars |> Library.subtract (op =) avail_vars
         val bad_tvars = tvars |> Library.subtract (op =) avail_tvars
       in
         if not check_groundness orelse (null bad_vars andalso null bad_tvars) then
           ()
         else err_with_trace ctxt2 ("check_prem: "^msg
            ^"\ninput argument is "^Syntax.string_of_term ctxt2 t
            ^"\nvars are "^Library.commas (vars
                 |> map (fn (ixn,T) => Syntax.string_of_term ctxt2 (Var(ixn,T))))
            ^"\ntvars are "^Library.commas (tvars
                 |> map (fn (ixn,S) => Syntax.string_of_typ ctxt2 (TVar(ixn,S))))
            ^"\nbad_vars are "^Library.commas (bad_vars
                 |> map (fn (ixn,T) => Syntax.string_of_term ctxt2 (Var(ixn,T))))
            ^"\nbad_tvars are "^Library.commas (bad_tvars
                 |> map (fn (ixn,S) => Syntax.string_of_typ ctxt2 (TVar(ixn,S)))))
       end
     (* otherwise we could not assume them while recursively solving prems via metarec
        Fun: compare to ancient fixme in raw_simplifier.ML before rewrite_rule_extra_vars ^^ *)
    val _ = prem_assms
      |> map (check_no_additional_vars "assumption of metarec premise has additional Vars or TVars")
    fun collect_all_juds t =
      case decompose_judgement gctxt t of
        SOME (jud, (pobj, iobjs, _)) =>
           insert (op =) jud #> fold collect_all_juds (pobj :: iobjs)
      | NONE =>
            (* note: this t may not contain loose bounds, this is why we
                fixed them earlier *)
          (case get_judgement_for_headterm gctxt t of
            SOME jud => insert (op =) jud
          | NONE => I)
   in
      case decompose_judgement gctxt prem_concl of
        SOME (jid_of_prem, (pobj_of_prem, iobjs_of_prem, oobjs_of_prem)) =>
          let
            val _ =
              if jid_of_prem = constraint_jud then
                [()]
              else
                (pobj_of_prem :: iobjs_of_prem)
                |> map (check_no_additional_vars
                     ("metarec premise conclusion\n"
                     ^Syntax.string_of_term ctxt2 prem_concl
                       ^"\nhas additional Vars or TVars in input position"))
            val seen_lthy_transf' =
              if not (Symtab.defined lthy_transforms jid_of_prem) then
                seen_lthy_transf
              else if not may_have_lthy_transforms then
                err_with_trace ctxt2 ("check_prem: premise with lthy transformation not allowed here   "
                  ^Syntax.string_of_term ctxt2 prem_concl)
              else if null params andalso null prem_assms then
                true
              else
                err_with_trace ctxt2 ("check_prem: premise with lthy transformation under fixes or assumes:  "
                  ^Syntax.string_of_term ctxt2 prem)
            val _ =
              if oobjs_of_prem |> map (Term.map_aterms
                   (fn t as Free _ =>
                       (case find_index (fn t2 => t = t2) params of
                         ~1 => t
                       | i => Bound (length params - i))
                     | t => t))
                 |> forall (Pattern.pattern o abstr_inst (avail_vars, avail_tvars)) then ()
              else
                err_with_trace ctxt2 ("check_prem: synthesized output object in premise conclusion   "
                  ^Syntax.string_of_term ctxt2 prem_concl
                  ^"   not a pattern when available vars are fixed")

            (* TODO(correctness): tracks only ground judgement dependencies instead
                 of proper higher-order judgement dependency analysis including
                 judgement variables. *)
            val further_juddeps = [] |> fold collect_all_juds (pobj_of_prem :: iobjs_of_prem)
            val _ =
              if null further_juddeps then ()
              else tracing ("check_prem: found further judgement dependencies\n    "^Library.commas further_juddeps
                ^"\nin premise conclusion   "^Syntax.string_of_term ctxt2 prem_concl)
          in
            (seen_lthy_transf',
             (avail_vars |> fold Term.add_vars oobjs_of_prem,
              avail_tvars |> fold Term.add_tvars oobjs_of_prem,
              jid_of_prem :: further_juddeps @ juds))
          end
      | NONE =>
          (case try dest_try prem_concl of
            SOME prem' =>
               (* so einfach weil prem_assms schon vollstaendig gecheckt
                  NB: local theory transformations in or before try premises not allowed *)
              if seen_lthy_transf then
                err_with_trace ctxt2 ("check_prem: premise with try not allowed after an lthy transformation here   "
                  ^Syntax.string_of_term ctxt2 prem_concl)
              else
                (let
                  fun cont () = 
                    check_prem ctxt2 may_have_lthy_transforms check_groundness
                      prem' (seen_lthy_transf, (avail_vars, avail_tvars, juds))
                in
                  case decompose_judgement gctxt prem' of
                    SOME (jid', _) =>
                      if Symtab.defined lthy_transforms jid' then
                        err_with_trace ctxt2 ("check_prem: lthy transformation not allowed in a try   "
                          ^Syntax.string_of_term ctxt2 prem_concl)
                      else
                        cont ()
                  | NONE =>
                      cont ()
                end)
          | NONE =>
              (* entspricht in lambdaProlog non-rigid Atomen in Goals
                 das ist wichtig fuer hoeherstufige Programmiertechnik, zB fuer map F xs *)
              let
                val _ = warning ("check_prem: premise conclusion   "^Syntax.string_of_term ctxt2 prem_concl
                  ^"   is not a known judgement and no solver matches. We will accept this now"
                  ^" and try to find use the judgement dynamically for instantiations of the rule."
                  ^" Note that judgement dependency tracking is now very conservative, considering "
                  ^" every judgement in that position.")
                val _ = check_no_additional_vars
                  ("premise conclusion of unknown judgement   "^Syntax.string_of_term ctxt2 prem_concl
                    ^"   has additional Vars or TVars (we are very conservative in the assumed mode of the"
                    ^" judgement: all arguments need to be ground)")
                  prem_concl
              in
                (seen_lthy_transf,
                 (avail_vars, avail_tvars,
                  arb_judgement :: juds))
              end)
   end

and check_prems ctxt may_have_lthy_transforms check_groundness prems (avail_vars0, avail_tvars0) =
  (false, (avail_vars0, avail_tvars0, []))
  |> fold (fn prem =>
         let val ctxt' = ctxt |> add_to_msg_trace (fn () => "checking premise "
           ^Syntax.string_of_term ctxt prem)
         in check_prem ctxt' may_have_lthy_transforms check_groundness prem end)
       prems
  |> snd

(* TODO(feature): auch unter Quantoren die Anwendung von implicit
     frules auf entstehende wf-Premissen erlauben, indem man fixt
     und entstehende gefixte Regeln generalisiert *)
and check_rule_wellformedness ctxt prop0 = 
  let
    val ([prop], ctxt2) = Variable.import_terms true [prop0] ctxt
    (* generate wellformedness hypotheses from conclusions of the rule premises
       and use them as local rules to show wellformedness of
       the rule conclusion 

       TODO(correctness): nicht doch lieber auch die Annahmen der
       Regelpremissen vor den generierten lokalen Regeln haben?!
       
       fixes werden dann zu Quantoren (dh zu schematischen Variablen in add_assm)
       vor den localen wf Regel die wir annehmen,
       was auch intuitiv ist: die Premissen haben Ableitung die parametrisch
       in den fixes ist, also sind ihre entsprechend wf Ableitungen auch
       parametrisch in den fixes *)
    val ctxt3 = ctxt2 
      |> fold (fn prem => fn ctxt2' =>
             let
               val params_raw = Logic.strip_params prem
               val (param_names, ctxt2'') = Variable.variant_fixes (map fst params_raw) ctxt2'
               val params = param_names ~~ (map snd params_raw)
               val prem_fixed_concl = Logic.strip_assums_concl prem
                 |> curry Term.subst_bounds (rev params |> map Free)
               val all_abs = fold_rev (Logic.all o Free) params
               val cert = cterm_of (Proof_Context.theory_of ctxt2'')
               val assms =
                 (case higher_judgement ctxt2'' prem_fixed_concl of
                   SOME (_, wfprem) => [prem_fixed_concl, wfprem]
                 | NONE => [prem_fixed_concl])
                 |> map (all_abs #> cert)
              in
                ctxt2''
                |> Assumption.add_assumes assms
                |-> fold (add_assm false)
              end)
           (Logic.strip_imp_prems prop)
  in
    case higher_judgement ctxt3 (Logic.strip_imp_concl prop) of
      SOME ((jud', inputs), _) =>
        let val _ = metarec ctxt3 jud' inputs
        in () end
    | NONE => ()
  end


and gen_check_rule calc_juddeps check_groundness ctxt prop =
    case decompose_judgement (Context.Proof ctxt) (Logic.strip_imp_concl prop) of
      SOME (concl_jud, (pobj, iobjs, oobjs)) =>
        if not calc_juddeps andalso not check_groundness then
          SOME (concl_jud, [])
        else
          (let
            (* TODO(functionality): diesen check weglassen? weil Pattern.match
               wird bei non-Patterns sowieso automatisch zu first-order-matching *)
            fun warn_in_ctxt warnmsg =
              let val _ = warning warnmsg
              in add_to_msg_trace (fn () => "WARNING: "^warnmsg) end
            val ctxt2 =
              if Pattern.pattern pobj then ctxt
              else
                ctxt |> warn_in_ctxt ("gen_check_rule: primary object in conclusion of rule \n"
                  ^Syntax.string_of_term ctxt prop
                  ^"\nnot a pattern so we use purely structural matching for it")
            val ctxt3 =
              case iobjs |> find_first (fn iobj => not (Pattern.pattern iobj)) of
                SOME iobj => ctxt2
                  |> warn_in_ctxt ("gen_check_rule: input object "
                       ^Syntax.string_of_term ctxt2 iobj^" in non-primary position is not a pattren")
              | NONE => ctxt2 

            val iobjs_are_patterns = forall Pattern.pattern iobjs
            val pobj_vars = Term.add_vars pobj []
            val pobj_tvars = Term.add_tvars pobj []
            val prems = Logic.strip_imp_prems prop
            (* val _ = tracing ("gen_check_rule: primary object is "^Syntax.string_of_term ctxt3 pobj)
            val _ = tracing ("gen_check_rule: pobj_vars are "^Library.commas (map (Syntax.string_of_term ctxt3 o Var) pobj_vars)) *)

            val (avail_vars0, avail_tvars0) = 
               (pobj_vars, pobj_tvars)
               |> fold (fn iobj => fn (avail_vars, avail_tvars) =>
                      if Pattern.pattern iobj then
                        (Term.add_vars iobj avail_vars, Term.add_tvars iobj avail_tvars)
                      else
                        (avail_vars, avail_tvars))
                    iobjs

            val (avail_vars, avail_tvars, jud_deps) =
              check_prems ctxt3 false check_groundness prems (avail_vars0, avail_tvars0)

            val oobjs_abstrinst = oobjs |> map (abstr_inst (avail_vars, avail_tvars))
            val iobjs_abstrinst = iobjs |> map (abstr_inst (avail_vars, avail_tvars))
            val oobjs_abstrinst_vars = fold Term.add_vars oobjs_abstrinst [] |> map Var
            val oobjs_abstrinst_tvars = fold Term.add_tvars oobjs_abstrinst [] |> map TVar

            val _ = 
              if not check_groundness orelse (null oobjs_abstrinst_vars andalso null oobjs_abstrinst_tvars) then ()
              else err_with_trace ctxt3 ("gen_check_rule: additional vars or tvars\n"
                ^(Library.commas (map (Syntax.string_of_term ctxt3) oobjs_abstrinst_vars
                    @ map (Syntax.string_of_typ ctxt3) oobjs_abstrinst_tvars))
                ^"\nin output objects\n"
                ^cat_lines (map (Syntax.string_of_term ctxt3) oobjs)
                ^"\nof conclusion")

            val _ = iobjs_abstrinst |> map (fn iobj_abstrinst =>
              if not check_groundness orelse Pattern.pattern iobj_abstrinst then ()
              else if null (Term.add_vars iobj_abstrinst []) andalso null (Term.add_vars iobj_abstrinst []) then ()
              else err_with_trace ctxt3 ("check_rule: input object in conclusion has additional vars "
                 ^"and is not a pattern when available vars are fixed"))

            val _ = check_rule_wellformedness ctxt3 prop
          in
            SOME (concl_jud, jud_deps)
          end)
    | NONE => NONE

and check_rule calc_juddeps check_groundness ctxt prop =  
  case gen_check_rule calc_juddeps check_groundness ctxt prop of
    SOME x => x
  | NONE => err_with_trace ctxt ("check_rule: rule "^Syntax.string_of_term ctxt prop
      ^" establishes unknown judgement")




(* large priority means gets priority before smaller values *)
(* TODO(features):
   * bei check_local_ty_wf den Typ des gefixten Typen im Kontext der Premissen
     synthetisieren und damit Wohlgeformtheit checken
     dh "Typsystem" fuer Regeln implementieren
   * Prioritaet nicht numerisch formulieren sondern als Constraints
     an Prioritaetsgraph der dann fuer Performance in numerische
     Prioris kompiliert wird
*)
and gen_add_rule local_rule check_groundness ctxt0 prior rule0 gctxt =
  let
     val {rules, depgraph, judgements, term_to_jud, ...} = get_current_ruledata gctxt

     val ctxt = ctxt0 |> add_to_msg_trace (fn () =>
       "gen_add_rule on "^Display.string_of_thm ctxt0 rule0)
       (* moeglichst wenig eta-normalisieren (nur das was der Simplifier braucht zum rewriten)
          um Namen von Bounds zu erhalten *)
     val rule =
       if local_rule then rule0
       else rule0 |> normalize_lesseta_withvars ctxt
     val _ = 
       if local_rule orelse (prop_of rule) aconv (prop_of rule0) then
         ()
       else
         warning ("gen_add_rule: rule was not normal wrt. computational rules; normalized to:"
            ^"\n"^Display.string_of_thm ctxt rule)
     val prop = Thm.prop_of rule
     val (concl_jud, jud_deps) = check_rule (not local_rule) check_groundness ctxt prop
     val depgraph' = depgraph |> fold (curry Graph.add_edge concl_jud) jud_deps
  in
    gctxt
    |> map_rule_stuff
      (Symtab.map_default (concl_jud, Item_Net2.init eq_for_net)
         (Item_Net2.cons (DirectRule rule, prior) (rule_net_index judgements term_to_jud)))
      (K depgraph')
  end

and add_rule prior rule gctxt =
  gen_add_rule false true (Context.proof_of gctxt) prior rule gctxt

and add_rule_unchecked_grnd prior rule gctxt =
  gen_add_rule false false (Context.proof_of gctxt) prior rule gctxt

and add_rule_unchecked prior rule gctxt =
  let val ctxt = Context.proof_of gctxt
  in
    gen_add_rule true false ctxt prior (normalize_lesseta_withvars ctxt rule) gctxt
  end












(* TODO(correctness):
   * check that gen brules don't affect judgements used as premises of comp rules
   * use decomposing pattern matching on frule heads in primary positions 
     not unification (which is not that bad because facts contain no variables,
     so this is non-pattern matching)
*)
and gen_with_pot_frules local_run expl_frules_opt pot_frules_with_opt_fact4head ctxt0 = 
  let
    fun do_pot_frule (frule_id, fact4head_opt) ctxt =
      let
        val gctxt = Context.Proof ctxt
        val {frules, ...} = get_current_ruledata gctxt
        val (frule, traced) =
          case Inttab.lookup frules frule_id of
            SOME (frule, _, _, _, traced) => (frule, traced)
          | NONE => raise Fail ("gen_with_pot_frules: frule with id "^string_of_int frule_id^" not found")
        val maj_cprem = Drule.cprems_of frule |> hd
        val heads = Conjunction.dest_conjunctions maj_cprem
          |> map Thm.term_of
        val thy = Proof_Context.theory_of ctxt

        fun lookup head = 
          let
            val res = lookup_facts gctxt head
            val _ =
              if null res andalso traced then
                trace_with_facts ctxt ("\nfrule not saturated (yet?):\n"^Display.string_of_thm ctxt frule)
              else
                ()
          in
            res
          end
        val facts_for_heads_posprod = heads |> map_index (fn (i,head) =>
             case fact4head_opt of
               SOME (headidx, fact) =>
                 if headidx = i then [fact]
                 else lookup head
             | NONE => lookup head)
           |> list_amb
           |> map_filter (fn facts_for_heads =>
              let
                (* renaming Bounds for more readable generated facts *)
                val frule' = frule
                  |> Thm.rename_boundvars (dummy_comb heads) (dummy_comb (map Thm.prop_of facts_for_heads))
                val frule'_curried = Conjunction.curry_balanced (length heads) frule'
              in
                (frule'_curried OF facts_for_heads) |> normalize_withvars ctxt
                |> pair (frule_id, frule', facts_for_heads) |> SOME
                handle THM _ => (* raised if input facts don't correspond to an instantiation of the frule *)
                  let val _ =
                    if traced then
                      tracing ("input facts\n"
                        ^cat_lines (map (fn th => "  *  "^Display.string_of_thm ctxt th) facts_for_heads)
                        ^"\ndont correspond to instantiation of traced frule\n"
                        ^Display.string_of_thm ctxt frule
                        ^"\ncurried version is \n"
                        ^Display.string_of_thm ctxt frule'_curried)
                    else
                      ()
                  in NONE end
              end)
      in
        ctxt
        |> fold do_inst_frule facts_for_heads_posprod
      end

    and do_inst_frule ((frule_id, frule', facts_for_heads), inst_frule_wo_heads) ctxt =
      let
        val thy = Proof_Context.theory_of ctxt
        val {frules, ...} = get_current_ruledata (Context.Proof ctxt)
        val (applied_facts, traced) =
          case Inttab.lookup frules frule_id of
            SOME (_, _, _, applied_facts, traced) => (applied_facts, traced)
          | NONE => raise Fail ("gen_with_pot_frules: frule with id "^string_of_int frule_id^" not found")
        val facts_for_heads_props = map (prop_of #> Envir.beta_eta_contract) facts_for_heads
        val facts_idx = fold (curry (op $)) facts_for_heads_props (Free("dummy", Term.dummyT))
          |> Envir.beta_eta_contract
        val proplist_eq = op abeconvs
        val props's =  Net.match_term applied_facts facts_idx
        val execute_frule = props's |> forall (fn props' =>
              not (proplist_eq (facts_for_heads_props, props')))
        fun frules_transf mor =
          let val f = Inttab.map_entry frule_id
            (fn (th, kind, headjuds, applied_facts, traced) =>
              let val applied_facts' = applied_facts |> Net.insert_term proplist_eq
                (Morphism.term mor facts_idx |> Envir.beta_eta_contract,
                 map (Morphism.term mor) facts_for_heads_props)
              in
                (th, kind, headjuds, applied_facts', traced)
              end)
          in map_frule_stuff I f I I end
        
        val _ =
          if traced then
            trace_with_facts ctxt ("\ntrying to apply frule:\n"^Display.string_of_thm ctxt frule'
            ^"\non facts\n"
            ^cat_lines (map (Syntax.string_of_term ctxt) facts_for_heads_props)
            ^(if execute_frule then "" else "\nbut those facts have already been tried "))
          else
            ()

        exception UnsolvablePrem
        fun global_fail_cont ctxt2 msg = 
          err_with_trace_and_facts ctxt2
            ("gen_with_pot_frules: failed to solve a premise in instantiated frule (heads discharged)\n"
              ^Display.string_of_thm ctxt2 inst_frule_wo_heads
              ^"\n\nbecause:\n"^msg)
        fun local_fail_cont _ _ = raise UnsolvablePrem
        val _ =
          if not local_run andalso is_some (get_run_state (Context.Proof ctxt)) then
            err_with_trace ctxt ("gen_with_pot_frules: context before solve_prems has a run state."
              ^"\ninstantiated frule without heads is "^Display.string_of_thm ctxt inst_frule_wo_heads)
          else ()

        fun do_solve_prems () = solve_prems_standalone global_fail_cont local_fail_cont
          inst_frule_wo_heads (Thm.prems_of inst_frule_wo_heads) ctxt

        fun succ_cont ((solved_prems, inst_env'), ctxt') =
            let
              val _ =
                if not local_run andalso is_some (get_run_state (Context.Proof ctxt')) then
                  err_with_trace ctxt' ("gen_with_pot_frules.succ_cont: context after solve_prems has a run state"
                    ^"\ninstantiated frule without heads is "^Display.string_of_thm ctxt' inst_frule_wo_heads)
                else ()
              val frule'' = inst_frule_wo_heads |> instnorm_thm_with_env ctxt' inst_env'
                (* TODO(correctness): wer ist der eta-Uebeltaeter? *)
              val res = Drule.implies_elim_list (eta_convert frule'') (map eta_convert solved_prems)
              val gen_raw_facts = 
                balanced_conjuncts_to_thms res
                |> filter_out (fn fact => (Thm.prop_of fact) aconv (Data.mk_Trueprop Data.True))

              val gen_facts = gen_raw_facts |> filter_out (prop_of #> can dest_brule)
              val gen_brules = gen_raw_facts |> map_filter (fn fact =>
                if can dest_brule (prop_of fact) then
                  let
                    (* generated backward rules stay generalized over non-instantiated Vars in the frule *)
                    (* TODO(feature): Thm.forall_elim_vars 0,  frule checking muss man dann auch entspr anpassen *)
                    val brule = fact
                      |> Conv.fconv_rule (Conv.rewr_conv Data.brule_const_def)
                      |> beta_convert (* TODO(opt): necessary? *)
                  in
                     SOME brule
                  end
                else NONE)
              (* val _ = tracing ("frule\n   "^Display.string_of_thm ctxt' frule'
                ^"\nis generating facts\n"^cat_lines (map (Display.string_of_thm ctxt') gen_facts)) *)
            in
              ctxt'
              |> (if local_run then Context.proof_map (Morphism.form frules_transf)
                  else map_pot_lthy frules_transf)
              |> fold (fn brule => fn ctxt2 =>
                     let
                       val {gen_brule_concls, ...} = get_current_ruledata (Context.Proof ctxt2)
                       val concl = Thm.concl_of brule
                       val thy2 = Proof_Context.theory_of ctxt2
                       val already_there = Net.unify_term gen_brule_concls (Envir.eta_contract concl)
                         |> map (fn brule2 =>
                              if unifies thy2 (Thm.concl_of brule2, concl) then
                                if (prop_of brule2 aconv prop_of brule) then
                                  true
                                else
                                  (* false *)
                                  err_with_trace ctxt2 ("gen_with_pot_frules: conclusions of generated brules overlap: "
                                  ^Syntax.string_of_term ctxt2 (Thm.concl_of brule2)
                                  ^"   vs   "^Syntax.string_of_term ctxt2 concl)
                              else false)
                         |> exists I
                       fun transf mor =
                         if already_there then I
                         else
                           let val brule' = Morphism.thm mor brule
                           in
                             map_gen_brule_concls (Net.insert_term Thm.eq_thm_prop (Thm.concl_of brule', brule'))
                               (* NB: cannot use ctxt2 because declarations emit theory checkpoints
                                    which change the theory *)
                               (* TODO(opt!!): proof_of teuer *)
                               (* NB: we want generated brules to be available in subsequent metarec calls *)
                             #> (fn gctxt => gctxt |> gen_add_rule true false (Context.proof_of gctxt) 0 brule')
                           end

                       (* fun str_of_thm_with_constTs th =
                          Display.string_of_thm ctxt2 th
                          ^"\n  where "^commas (Term.add_consts (prop_of th) [] |> map (fn (n, T) =>
                             Syntax.string_of_term ctxt2 (Const(n,T)) ^" :: "^Syntax.string_of_typ ctxt2 T))
                       val _ = tracing
                         ("adding brule\n  "^str_of_thm_with_constTs brule
                          ^"\ngenerated from instantiated frule (wo heads)\n  "
                          ^str_of_thm_with_constTs frule''
                          ^"\nbased on frule (wo heads)\n  "
                          ^str_of_thm_with_constTs inst_frule_wo_heads
                          ^"\nbased on frule (renamed)\n  "
                          ^str_of_thm_with_constTs frule'
                          ^"\ninst_env' (type part) is\n  "
                          ^commas (Vartab.dest (Envir.type_env inst_env')
                             |> map (fn (ixn, (S, T')) =>
                               Syntax.string_of_typ ctxt2 (TVar(ixn, S))^" := "^Syntax.string_of_typ ctxt2 T'))) *)

                       val ctxt3 = ctxt2
                         |> (if local_run then Context.proof_map (Morphism.form transf)
                             else map_pot_lthy transf)
                     in
                       ctxt3
                     end)
                   gen_brules
                (* FIXME?: Fakten als Regeln auch einfuegen bevor die
                    Rekursion angestossen wird? *)
              |> fold (gen_add_fact local_run expl_frules_opt false) gen_facts
            end
      in
        if execute_frule then
          succ_cont (do_solve_prems ())
             (* lthy-transformationen duerfen nicht nach try-Premissen stehen, deshalb geht das *)
          handle UnsolvablePrem => ctxt
        else
          ctxt
      end
  in
    ctxt0 |> fold do_pot_frule pot_frules_with_opt_fact4head
  end


and gen_add_fact local_run expl_frules_opt guaranteed_new_for_expl_frules fact0 ctxt = 
  let
    (* TODO(feature): nonground facts
         interessant um zB rewrite regeln  c ?x ~~> c2 ?x 
         als Fakten behandeln zu koennen, etwa mit impliziten frules
           t1 ~~> t2 ==> t1 rewto t2

         aber fraglich ob man nicht auch mit
           register_my_rews ==> brule (t1 rewto t2)
         auskommt ...

         das bedarf dann folgender Aenderungen
          * im Fakten-Konsis-Check nicht mehr aconv sondern unifies
          * frule Anwendung soll nach wie vor mit matching stattfinden,
            also das explizit machen statt OF nutzen
          * Fakten-Check hier und in add_assm anpassen *)
    val fact = normalize ctxt fact0
    val gctxt = Context.Proof ctxt
    val {facts, frules, frules_hdidx, facts_lhs_idx, ...} = get_current_ruledata gctxt
    val fact_prop = Thm.prop_of fact
    val (jud, pobj, iobjs, oobjs) =
      case decompose_judgement gctxt fact_prop of
        SOME (jud, (pobj, iobjs, oobjs)) => (jud, pobj, iobjs, oobjs)
      | NONE => err_with_facts ctxt "gen_add_fact: fact has unknown judgement"
    val lhs_idx = Free(jud, @{typ "prop"}) $ pack_pobj_iobjs pobj iobjs

    (* TODO(correctness): wf-check des Facts
         (ist unpraktisch wenn man wfelem definiert,
         weil das eine Elementschaftspremisse hat) *)

    val already_inserted = Net.lookup facts (Net.key_of_term fact_prop)
      |> exists (fn fact' => Thm.eq_thm_prop (fact',fact))
    fun fact_insert_transf mor =
      let
        val fact' = Morphism.thm mor fact
          (* TODO: wenn man spaeter lokalisiert Judgements hat muss man wohl fact'
               decomposen um das richtige Judgement zu erfahren. Aufpassen mit
               Premissen die durch export morphismen entstehen  *)
        val jud' = 
          case decompose_judgement gctxt (prop_of fact) of
            SOME (jud', _) => jud'
          | NONE =>
              err_with_facts ctxt ("gen_add_fact: fact has unknown judgement: "
                ^Display.string_of_thm ctxt fact)
      in
          (* TODO(semantics): nur im aux ctxt die new_facts loggen? *)
          (* NB: always logging fact even if we are running expl frules now *)
        map_fact_stuff (Net.insert_term Thm.eq_thm_prop (Thm.prop_of fact', fact'))
          (Net.insert_term Thm.eq_thm_prop (lhs_idx, fact'))
          (Symtab.cons_list (jud', fact'))
        (* use facts directly as brules *)
        #> map_gen_brule_concls (Net.insert_term Thm.eq_thm_prop (Thm.concl_of fact', fact'))
            (* nicht nochmal nen wf-Check machen *)
            (* TODO(opt!!): proof_of teuer auf Theorien *)
        #> (fn gctxt => gctxt |> gen_add_rule true false (Context.proof_of gctxt) 0 fact')
      end
  in
    ctxt
      (* TODO(correctness): warum ist es wichtig das duplizierte notes absorbiert werden? 
           sollten ja nicht entstehen ... *)
    |> (jud = note_jud andalso not local_run andalso not already_inserted)
          ? (pot_note_in_lthy fact)
    |> (not already_inserted) ? (
         if local_run then
           Context.proof_map (Morphism.form fact_insert_transf)
         else
           map_pot_lthy fact_insert_transf)
    |> (not already_inserted orelse guaranteed_new_for_expl_frules) ?
         (fn ctxt2 =>
           let
             (* d.h. sammle ausgewaehlte explizite frules und impliziten frules auf
                die einen Head haben der gegen fact_prop matcht *)
             val pot_frules = Net.match_term frules_hdidx (Envir.eta_contract fact_prop)
               |> map_filter (fn (frule_id, head_idx) =>
                    case Inttab.lookup frules frule_id of
                      SOME (_, ImplicitFRule, _, _, _) =>
                        SOME (frule_id, SOME (head_idx, fact))
                    | SOME (_, ExplicitFRule, _, _, _) =>
                        if is_some expl_frules_opt
                           andalso Inttab.defined (the expl_frules_opt) frule_id
                        then
                          SOME (frule_id, SOME (head_idx, fact))
                        else
                          NONE
                    | NONE => err_with_facts ctxt2 "gen_add_fact: internal error: no frule registered for some id")

             (* val _ = tracing ("gen_add_fact: considering \"new\" fact\n    "^Display.string_of_thm ctxt2 fact) *)

             (* val _ = tracing ("pot_frules for new fact \n"
               ^ Display.string_of_thm ctxt2 fact
               ^"\nare\n"^cat_lines (map (Display.string_of_thm ctxt2 o get_frule frules o fst) pot_frules)) *)
             val _ = Net.lookup facts_lhs_idx (Net.key_of_term lhs_idx)
               |> forall (fn fact' =>
                    case decompose_judgement gctxt (prop_of fact') of
                      SOME (jud', (pobj', iobjs', oobjs')) =>
                        if jud <> jud'
                          orelse (get_judgement_inconsis_allowed gctxt jud)
                          orelse exists (not o aconv) ((pobj, pobj') :: (iobjs ~~ iobjs'))
                          orelse forall (op aconv) (oobjs ~~ oobjs')
                        then true
                        else err_with_facts ctxt2 ("gen_add_fact: fact inconsistency:\n   "
                          ^Display.string_of_thm ctxt2 fact^"\nvs\n    "
                          ^Display.string_of_thm ctxt2 fact'
                          ^"\n\nraw oobjs\n    "
                          ^PolyML.makestring oobjs^"\nvs\n    "
                          ^PolyML.makestring oobjs')
                    | NONE => err_with_facts ctxt2 ("gen_add_fact: an already indexed fact has unknown judgement:\n"
                        ^Display.string_of_thm ctxt2 fact'))
           in
             ctxt2 |> gen_with_pot_frules local_run expl_frules_opt pot_frules
           end)
  end

and add_local_fact fact ctxt =
  gen_add_fact true NONE false fact ctxt


(* NB: nicht in einer Deklaration verwenden, sondern statt einer Deklaration
     (Ausnahme: garantiert ausserhalb von expl frule runs);
     nutzt fuer die Fakten naemlich map_pot_lthy *)
and add_facts_decl facts0 ctxt =
  let
    val facts = facts0 |> forall (fn fact0 =>
      if null (Term.add_vars (prop_of fact0) [])
         andalso null (Term.add_tvars (prop_of fact0) []) then true
      else err_with_facts ctxt ("gen_add_fact: fact "^Display.string_of_thm ctxt fact0
             ^" contains Vars or TVars"))
    val _  = ()
      |> fold (fn fact0 => fn _ => check_rule_wellformedness ctxt (prop_of fact0)) facts0
  in
    ctxt |> fold (gen_add_fact false NONE false) facts0
  end

(* NB: nur rudimentaer in Deklarations benutzbar die garantiert ausserhalb
    von expl frule runs stattfinden, sonst falsche map_pot_lthy Semantik *)
and add_facts_gctxt facts gctxt = run_on_ctxt (add_facts_decl facts) gctxt






and gen_add_frule checked checked_grndness explicit traced frule0 gctxt =
  let
    val thy = Context.theory_of gctxt
    val ctxt = Context.proof_of gctxt

    val {depgraph, frules, frules_hdidx, frules_factgen, ...} = get_current_ruledata gctxt

    val frule = frule0 |> normalize_withvars ctxt
      |> balance_majprem_and_concl thy
    val maj_cprem = Drule.cprems_of frule |> hd
    val cconcl = Thm.cprop_of frule |> Drule.strip_imp_concl
    val prems = tl (Thm.prems_of frule)

    val heads = Conjunction.dest_conjunctions maj_cprem |> map Thm.term_of
    val headjuds = heads |> map (fn head =>
      case decompose_judgement gctxt head of
        SOME (headjud, _) => headjud
      | NONE => error ("gen_add_frule: head is of unknown judgement\n"
          ^Syntax.string_of_term ctxt head))
    val concls = Conjunction.dest_conjunctions cconcl |> map Thm.term_of
      |> filter_out (fn concl => concl aconv (Data.mk_Trueprop Data.True))

    (* TODO(correctness): check if frule is an frule already *)

    val frule_id = serial ()
    (* val _ = tracing ("frule_id is "^string_of_int frule_id) *)
    val frule_key = calc_frule_key frule_id

    (* insert this frule already to discover reflexive dependencies *)
    val frules' = frules |> Inttab.update (frule_id,
      (frule, if explicit then ExplicitFRule else ImplicitFRule, headjuds, Net.empty, traced))
    (* braucht insert_term_safe weil Variablen der frule verschiedene
       heads oder gen facts unifizierbar erscheinen lassen *)
    val frules_hdidx' = frules_hdidx |> fold_index (fn (i, head) =>
        Net.insert_term_safe (op =) (head, (frule_id, i))) heads
    val frules_factgen' = frules_factgen |> fold (fn concl =>
        if can dest_brule concl then I
        else Net.insert_term_safe (op =) (concl, frule_id)) concls

    val _ =
      if explicit orelse null prems then ()
      else err_with_trace ctxt "gen_add_frule: implicit frule has premises"
    val (avail_vars0, avail_tvars0) =
      (Term.add_vars (term_of maj_cprem) [], Term.add_tvars (term_of maj_cprem) [])
    val (avail_vars, avail_tvars, prem_juds) =
      check_prems ctxt explicit checked_grndness prems (avail_vars0, avail_tvars0)
        
    (* val _ = tracing ("gen_add_frule: prem_juds are  "^Library.commas prem_juds) *)

    fun calc_depgraph' () = depgraph
      |> Graph.new_node (frule_key, FRule frule_id)
      |> fold (fn prem_jud => Graph.add_edge (frule_key, prem_jud)) prem_juds
      |> fold (fn head =>
             let
               val head_jud =
                 case decompose_judgement gctxt head of
                   SOME (head_jud, _) => head_jud
                 | NONE => error ("gen_add_frule: head of unknown judgement\n"
                     ^Syntax.string_of_term ctxt head)
               val rules_pot_fact_unifying_with_head =
                 Net.unify_term frules_factgen' (Envir.eta_contract head)
               (* val _ = tracing ("gen_add_frule: potential pre-frules for head "
                 ^Syntax.string_of_term ctxt head^"  are  \n"
                 ^cat_lines (map (Display.string_of_thm ctxt o get_frule frules')
                    rules_pot_fact_unifying_with_head)) *)
             in
               fold (fn id' => Graph.add_edge (frule_key, calc_frule_key id'))
                 rules_pot_fact_unifying_with_head
               (* TODO(semantics): warum nicht immer so und wozu dann noch direkte
                     frule -> frule Abhaengigkeiten? Wenn dependency tracking genauer
                     ist ueber Termgraph ist das ja nicht schlechter.
                  !! Momentan wird das in check_depgraph aber zur Untscheidung
                     "abhaengig von Judgement wg Goal" und "abhaengig von anderer FRule
                     fuer Head" genutzt *)
               #> (get_judgement_kind gctxt head_jud = CollJud) ?
                    Graph.add_edge (frule_key, head_jud)
             end)
           heads
      |> fold (fn concl =>
            if can dest_brule concl then
              let
                val brule = dest_brule concl
                val (inst, ctxt') = ctxt |> add_to_msg_trace (fn () =>
                  "gen_add_frule: checking generated brule "^Syntax.string_of_term ctxt brule)
                  |> Variable.import_inst true (Thm.prems_of frule)
                  (* TODO(feature): Heads und Premissen als Annahmen beim Regelchecken dazu *)
                  (* the brule is checked with all available variables (available
                     via the frule heads and premises) fixed *)
                val brule_inst = Term_Subst.instantiate inst brule
                val (brule_concl_jud, brule_prem_juds) = check_rule true true ctxt' brule_inst
              in
                Graph.add_edge (brule_concl_jud, frule_key)
                #> fold (fn brule_prem_jud => Graph.add_edge (brule_concl_jud, brule_prem_jud))
                     brule_prem_juds
              end
            else
              let
                val vars = Term.add_vars concl []
                val tvars = Term.add_tvars concl []
                val bad_vars = vars |> Library.subtract (op =) avail_vars
                val bad_tvars = tvars |> Library.subtract (op =) avail_tvars
                val _ =
                  if null bad_vars andalso null bad_tvars then
                    ()
                  else
                    err_with_trace ctxt ("gen_add_frule: conclusion has additional vars or tvars: "^
                      Syntax.string_of_term ctxt concl
                      ^"\nvars are "^Library.commas (vars
                           |> map (fn (ixn,T) => Syntax.string_of_term ctxt (Var(ixn,T))))
                      ^"\ntvars are "^Library.commas (tvars
                           |> map (fn (ixn,S) => Syntax.string_of_typ ctxt (TVar(ixn,S))))
                      ^"\nbad_vars are "^Library.commas (bad_vars
                           |> map (fn (ixn,T) => Syntax.string_of_term ctxt (Var(ixn,T))))
                      ^"\nbad_tvars are "^Library.commas (bad_tvars
                           |> map (fn (ixn,S) => Syntax.string_of_typ ctxt (TVar(ixn,S)))))

                val concl_jud = case decompose_judgement gctxt concl of
                    SOME (concl_jud, _) =>
                      if explicit orelse concl_jud <> note_jud then
                        concl_jud
                      else
                        err_with_trace ctxt
                          ("gen_add_frule: implicit frule with note judgement conclusion")
                  | NONE =>
                      err_with_trace ctxt ("gen_add_frule: conclusion is not a brule and not"
                        ^" of known judgement: "^Syntax.string_of_term ctxt concl)
                val rules_pot_head_unifying_with_fact =
                  Net.unify_term frules_hdidx' (Envir.eta_contract concl) |> map fst
              in
                (* Fakten als brules auffassen! *)
                Graph.add_edge (concl_jud, frule_key)
                #> fold (fn id' => Graph.add_edge (calc_frule_key id', frule_key))
                  rules_pot_head_unifying_with_fact
              end)
          concls

    val depgraph' =
      if not checked then depgraph
      else
        let
          val depgraph' = calc_depgraph' ()
          val _ = check_depgraph (Display.string_of_thm ctxt) frules' depgraph'
        in depgraph' end
  in
    gctxt
    |> map_frule_stuff (K depgraph') (K frules') (K frules_hdidx') (K frules_factgen')
    (* ist unproblematisch, weil lokal vorkommende frules immer
       Beweiskontexten zugeordnet sind, also die map_pot_lthy Semantik
       nicht beeinflusst wird *)
    |> (not explicit) ?  (run_on_ctxt (fn ctxt' =>
         gen_with_pot_frules false NONE [(frule_id, NONE)] ctxt'))
  end


fun add_expl_frule frule gctxt =
  gen_add_frule true true true false frule gctxt
fun add_expl_frule_unchecked_grnd frule gctxt =
  gen_add_frule true false true false frule gctxt
fun add_traced_expl_frule frule gctxt =
  gen_add_frule true true true true frule gctxt

fun add_impl_frule frule gctxt =
  gen_add_frule true true false false frule gctxt
fun add_impl_frule_unchecked_grnd frule gctxt =
  gen_add_frule true false false false frule gctxt






fun print_new_facts gctxt =
  let
    val {new_facts, ...} = get_current_ruledata gctxt
    val _ = Output.writeln ("new_facts:")
    val _ = () |> fold_rev (fn (_, fact) => fn _ =>
        Output.writeln (Display.string_of_thm (Context.proof_of gctxt) fact))
      (Symtab.dest_list new_facts)
  in
    ()
  end

(* sollte das eher eine Declaration sein?!?! Vermutlich, aber mit neuer semantik und nur auf lthys!!
     add_expl_frule, add_impl_frule, add_rule etc sind
     ja alles Attribute also werden die wohl wie Declarations
     mitinstantiiert *)
fun run_expl_frules lthy0 =
  let
    val lthy1 = lthy0 |> set_running_expl_frules true
    val {depgraph, frules, new_facts=new_facts0, gen_brule_concls, ...} =
      get_current_ruledata (Context.Proof lthy1)

      (* sccs without dependencies go last *)
    val depgraph_scc = Graph.strong_conn depgraph
    fun do_frule_scc scc lthy =
      let
        val {new_facts, ...} = get_current_ruledata (Context.Proof lthy)
        fun accum f new_headjuds new_traced (restr_expl_frules, headjuds, traced) =
          (f restr_expl_frules, union (op =) new_headjuds headjuds, traced orelse new_traced)
        val (restr_expl_frules, headjuds, traced) = (Inttab.empty, [], false)
          |> fold (fn key =>
                 case get_frule_id depgraph key of
                   SOME id =>
                     (case Inttab.lookup frules id of
                       SOME (_, ExplicitFRule, headjuds, _, traced) =>
                         accum (Inttab.update (id, ())) headjuds traced
                     | SOME (_, ImplicitFRule, headjuds, _, traced) =>
                         accum I headjuds traced
                     | NONE =>
                         err_with_trace lthy "run_expl_frules: frule id not found")
                 | NONE => I)
               scc
        val _ =
          if traced then
            trace_with_facts lthy ("do_frule_scc:  saturating rules \n"
              ^(cat_lines (Inttab.dest restr_expl_frules |> map_filter (fn (id, _) =>
                try (get_frule frules #> Display.string_of_thm lthy) id)))
              ^"\non new facts\n"
              ^(cat_lines (map (snd #> Display.string_of_thm lthy) (Symtab.dest_list new_facts))))
          else
            ()
      in
        (* TODO(opt): nur Fakten probieren fuer die es heads in der scc gibt *)
        lthy
        |> fold (fn headjud =>
               case Symtab.lookup new_facts headjud of
                 SOME new_facts' => fold (gen_add_fact false (SOME restr_expl_frules) true) new_facts'
               | NONE => I)
             headjuds
      end
    fun do_collector colljud lthy =
      let
        val gctxt = Context.Proof lthy
        val thy = Context.theory_of gctxt
        val (collI, basejud, triggerjud_opt) = get_judgement_coll_info gctxt colljud
        val {facts, judgements,...} = get_current_ruledata gctxt
        val mode = get_judgement_mode gctxt basejud

        fun get_rel_facts_for jud' = 
          let
            val head_term = get_judgement_head_term gctxt jud'
            val head_term_argTs = fastype_of head_term |> binder_types
            val head_term_pobjT = hd head_term_argTs
            val head_term_iobjTs = take (fst mode) (tl head_term_argTs)
              (* TODO(correctness): take (snd mode)   after drop ? *)
            val head_term_oobjTs = drop (fst mode) (tl head_term_argTs)

            val jud_maker =
              case lookup_judgement_analyzer judgements jud' of
                SOME (_, maker, _) => maker
              | NONE => error ("run_expl_frules: "^quote jud'
                  ^" not a judgement but needed to collect "^quote colljud)
            fun dummy_var T = Var(("blub",0), T)

            val dummy_judappl = jud_maker thy
               (dummy_var head_term_pobjT, map dummy_var head_term_iobjTs,
                 map dummy_var head_term_oobjTs)
          in
            Net.unify_term facts dummy_judappl
          end

        val facts_of_triggerjud = 
          if is_some triggerjud_opt then
            get_rel_facts_for (the triggerjud_opt)
          else []

        (* val _ =
          if is_some triggerjud_opt then
            trace_with_facts lthy ("do_collector: triggerjud "^quote (the triggerjud_opt)
              ^"  has no facts registered")
          else () *)
      in
        if is_some triggerjud_opt andalso null (get_rel_facts_for (the triggerjud_opt)) then
          lthy
        else
          let
              (* TODO(correctness): rel_facts checken ? *)
            val rel_facts = get_rel_facts_for basejud
            val rel_facts_proplist = fold (Data.mk_prop_cons o prop_of) rel_facts Data.prop_nil
              |> cterm_of thy
            val coll_fact = collI |> Drule.instantiate' []
              [SOME (cterm_of thy Data.unit_elem), SOME rel_facts_proplist]
            (* val _ = tracing ("do_collector: collected the following facts for "^quote colljud
              ^":\n"^cat_lines (map (Display.string_of_thm lthy) rel_facts)) *)
          in
            lthy |> gen_add_fact false NONE true coll_fact
          end
      end
    fun do_scc scc lthy =
      case scc of
        [key] =>
          (case try (get_judgement_kind (Context.Proof lthy)) key of
            SOME CollJud => do_collector key lthy
          | _ => do_frule_scc scc lthy)
      | _ => do_frule_scc scc lthy

   (* TODO(opt): besser depgraph_scc reversen und fold nutzen ? *)
   val lthy2 = lthy1 |> fold_rev do_scc depgraph_scc
   val log = get_lthy_transform_log lthy2

   val lthy3 = lthy2
    |> map_lthy_transforms_log (K [])
         (* explicitly reset new_facts *)
    |> map_pot_lthy (K (map_fact_stuff I I (K Symtab.empty)))
    |> set_running_expl_frules false

   val _ = Output.writeln
     ("explicit frules execution started on:\n"
        ^(Symtab.dest_list new_facts0 |> rev |> map (fn (_, th) => "  "^Display.string_of_thm lthy3 th) |> cat_lines)
      ^"\n\nexecuted local theory transformations:\n"
        ^(rev log |> map (fn s => "  "^s) |> cat_lines))
  in
    lthy3
  end
  










(* constraint propagation rules are of the form
     guards aka prems ==> heads conjunction ==> conclusion conjunction *)
fun add_constraint_propag_rule checked_grndness propag_rule0 gctxt =
  let
    val thy = Context.theory_of gctxt
    val ctxt = Context.proof_of gctxt

    val {constraint_propag_rules_hdidx, ...} = get_current_ruledata gctxt
    val propag_rule = propag_rule0 |> normalize_lesseta_withvars ctxt

    val nprems = length (Thm.prems_of propag_rule) - 1
    val balance_conv =
      Conv.concl_conv nprems (
        (Conv.implies_conv (balance_conj_conv thy) Conv.all_conv)
        then_conv (Conv.concl_conv ~1 (balance_conj_conv thy)))
    val propag_rule = propag_rule0 |> normalize_withvars ctxt
      |> Conv.fconv_rule balance_conv
    val prems = Thm.prems_of propag_rule |> rev |> drop 1 |> rev

    val heads_conj = Drule.cprems_of propag_rule |> drop nprems |> hd
    val heads = Conjunction.dest_conjunctions heads_conj |> map Thm.term_of
    val concls = Conjunction.dest_conjunctions (cconcl_of propag_rule) |> map Thm.term_of
      |> filter_out (fn concl => concl aconv (Data.mk_Trueprop Data.True))


    fun check_jud err term = 
      case decompose_judgement gctxt term of
        SOME _ => () 
      | NONE => err term
    val _ = heads |> map (check_jud (fn head =>
      error ("add_constraint_propag_rule: head is of unknown judgement\n"^Syntax.string_of_term ctxt head)))
    val _ = concls |> map (check_jud (fn concl =>
      error ("add_constraint_propag_rule: conclusion is of unknown judgement\n"^Syntax.string_of_term ctxt concl)))

    (* TODO(correctness): check if propag_rule is a propag_rule already *)

    (* braucht insert_term_safe weil Variablen der propag_rule verschiedene
       heads oder gen facts unifizierbar erscheinen lassen *)
    val constraint_propag_rules_hdidx' = constraint_propag_rules_hdidx |> fold_index (fn (i, head) =>
        Net.insert_term_safe (eq_pair Thm.eq_thm_prop (op =)) (head, (propag_rule, i))) heads

    val (avail_vars0, avail_tvars0) =
      (Term.add_vars (Thm.term_of heads_conj) [], Term.add_tvars (Thm.term_of heads_conj) [])
    val (avail_vars, avail_tvars, prem_juds) =
      check_prems ctxt false checked_grndness prems (avail_vars0, avail_tvars0)
    val _ = concls |> map (fn concl =>
      let
        val vars = Term.add_vars concl []
        val tvars = Term.add_tvars concl []
        val bad_vars = vars |> Library.subtract (op =) avail_vars
        val bad_tvars = tvars |> Library.subtract (op =) avail_tvars
        val _ =
          if null bad_vars andalso null bad_tvars then
            ()
          else
            err_with_trace ctxt ("add_constraint_propag_rule: concl has additional vars or tvars: "^
              Syntax.string_of_term ctxt concl
              ^"\nvars are "^Library.commas (vars
                   |> map (fn (ixn,T) => Syntax.string_of_term ctxt (Var(ixn,T))))
              ^"\ntvars are "^Library.commas (tvars
                   |> map (fn (ixn,S) => Syntax.string_of_typ ctxt (TVar(ixn,S))))
              ^"\nbad_vars are "^Library.commas (bad_vars
                   |> map (fn (ixn,T) => Syntax.string_of_term ctxt (Var(ixn,T))))
              ^"\nbad_tvars are "^Library.commas (bad_tvars
                   |> map (fn (ixn,S) => Syntax.string_of_typ ctxt (TVar(ixn,S)))))
       in () end)
        
    (* val _ = tracing ("gen_add_frule: prem_juds are  "^Library.commas prem_juds) *)
  in
    gctxt
    |> map_constraint_propag_rules_hdidx (K constraint_propag_rules_hdidx')
  end


(* constraint simplification rules are of the form
     guards and sub-goals aka prems ==> heads conjunction *)
fun add_constraint_simp_rule checked_grndness simp_rule0 gctxt =
  let
    val thy = Context.theory_of gctxt
    val ctxt = Context.proof_of gctxt

    val {constraint_simp_rules_hdidx, ...} = get_current_ruledata gctxt
    val simp_rule = simp_rule0 |> normalize_lesseta_withvars ctxt

    val nprems = length (Thm.prems_of simp_rule)
    val balance_conv = Conv.concl_conv nprems (balance_conj_conv thy)
    val simp_rule = simp_rule0 |> normalize_withvars ctxt
      |> Conv.fconv_rule balance_conv
    val prems = Thm.prems_of simp_rule

    val heads_conj = cconcl_of simp_rule
    val heads = Conjunction.dest_conjunctions heads_conj |> map Thm.term_of

    fun check_jud err term = 
      case decompose_judgement gctxt term of
        SOME _ => () 
      | NONE => err term
    val _ = heads |> map (check_jud (fn head =>
      error ("add_constraint_simp_rule: head is of unknown judgement\n"^Syntax.string_of_term ctxt head)))

    (* TODO(correctness): check if simp_rule is a simp_rule already *)

    (* braucht insert_term_safe weil Variablen der simp_rule verschiedene
       heads oder gen facts unifizierbar erscheinen lassen *)
    val constraint_simp_rules_hdidx' = constraint_simp_rules_hdidx |> fold_index (fn (i, head) =>
        Net.insert_term_safe (eq_pair Thm.eq_thm_prop (op =)) (head, (simp_rule, i))) heads

    val (avail_vars0, avail_tvars0) =
      (Term.add_vars (Thm.term_of heads_conj) [], Term.add_tvars (Thm.term_of heads_conj) [])
    val (avail_vars, avail_tvars, prem_juds) =
      check_prems ctxt false checked_grndness prems (avail_vars0, avail_tvars0)

    (* val _ = tracing ("gen_add_frule: prem_juds are  "^Library.commas prem_juds) *)
  in
    gctxt
    |> map_constraint_simp_rules_hdidx (K constraint_simp_rules_hdidx')
  end









fun gen_jud_dest_opt head_name mode t =
  let
    val (h, ts) = strip_comb t

    fun cont head_name' =
      if head_name = head_name' andalso length ts = (fst mode + snd mode + 1) then
        let
          val (pt, ts2) = (hd ts, tl ts)
          val iobjs = take (fst mode) ts2
          val oobjs = drop (fst mode) ts2
        in SOME (pt, iobjs, oobjs) end
      else
        NONE
  in
    case h of
      Const(head_name', _) => cont head_name'
    | Free(head_name', _) => cont head_name'
    | _ => NONE
  end
fun gen_trueprop_jud_dest_opt head_name mode = try Data.dest_Trueprop
  #> Option.map (gen_jud_dest_opt head_name mode) #> Option.join


fun gen_jud_cdest_opt head_name mode ct =
  let
    val (ch, cts) = Drule.strip_comb ct

    fun cont head_name' =
      if head_name = head_name' andalso length cts = (fst mode + snd mode + 1) then
        let
          val (pt, cts2) = (hd cts, tl cts)
          val iobjs = take (fst mode) cts2
          val oobjs = drop (fst mode) cts2
        in SOME (pt, iobjs, oobjs) end
      else
        NONE
  in
    case (Thm.term_of ch) of
      Const(head_name', _) => cont head_name'
    | Free(head_name', _) => cont head_name'
    | _ => NONE
  end
fun gen_trueprop_jud_cdest_opt head_name mode = try Object_Logic.dest_judgment
  #> Option.map (gen_jud_cdest_opt head_name mode) #> Option.join

      
fun gen_untyped_jud_maker head (pobj, iobjs, oobjs) = list_comb (head, pobj :: iobjs @ oobjs)
fun gen_untyped_trueprop_jud_maker head = gen_untyped_jud_maker head
  #> Data.mk_Trueprop

fun gen_typed_jud_maker (head as Free _) thy =
      gen_untyped_jud_maker head (* Frees have no polymorphic instantiations *)
  | gen_typed_jud_maker (head as Const (n, _)) thy =
      let val T = Sign.the_const_type thy n
      in
      (fn (pobj, iobjs, oobjs) => 
       (* T should be most general type of constant *) 
      let
        val obj_comb = (pobj :: iobjs @ oobjs)
        val binder_Ts = binder_types T
        val _ =
          if length binder_Ts >= length obj_comb then ()
          else error ("gen_typed_jud_maker: constant "^n^" :: "^Syntax.string_of_typ_global thy T
            ^" not of corresponding function type for arguments >= "
            ^cat_lines (map (Syntax.string_of_term_global thy) obj_comb))
        val matching_pairs = (take (length obj_comb) binder_Ts) ~~ (map fastype_of obj_comb)

        val tyenv = Vartab.empty |> fold (Type.typ_match (Sign.tsig_of thy)) matching_pairs
          handle TYPE_MATCH =>
            error ("gen_typed_jud_maker: not a well typed combination: "
               ^"\n   "^Syntax.string_of_term_global thy head^"      on\n"
               ^ Library.cat_lines (map2 (fn t => fn (T, T') =>
                      Syntax.string_of_term_global thy t ^ " :: "^Syntax.string_of_typ_global thy T'
                      ^"  against type "^Syntax.string_of_typ_global thy T)
                   obj_comb  matching_pairs))
      in
        list_comb (Const(n, Envir.norm_type tyenv T), obj_comb)
      end)
      end
fun gen_typed_trueprop_jud_maker head thy =
  gen_typed_jud_maker head thy
  #> Data.mk_Trueprop 


(* NB: nins is the number of arguments *not* including the primary argument *)
fun gen_add_nplace_jud add_jud judkind higherjud_opt nins nouts judname head_term gctxt =
  let
    val n = case try name_from_const_or_free head_term of
        SOME n => n
      | NONE =>
          error ("gen_add_nplace_jud: head_term not a Const or Free: "
            ^Syntax.string_of_term (Context.proof_of gctxt) head_term)
    val prop_valued = (fastype_of head_term |> body_type) = @{typ "prop"}
    val mode = (nins, nouts)
    val matcher =
      if prop_valued then gen_jud_dest_opt n mode
      else gen_trueprop_jud_dest_opt n mode
    val cmatcher =
      if prop_valued then gen_jud_cdest_opt n mode
      else gen_trueprop_jud_cdest_opt n mode
    val maker =
      if prop_valued then gen_typed_jud_maker head_term
      else gen_typed_trueprop_jud_maker head_term
  in
    add_jud judname head_term (matcher, maker, cmatcher) mode judkind higherjud_opt gctxt
  end

fun gen_add_nplace_synth_jud allow_inconsis = gen_add_nplace_jud (add_judgement allow_inconsis)
fun add_nplace_synth_jud allow_inconsis = gen_add_nplace_synth_jud allow_inconsis NormalJud
fun add_nplace_coll_jud colljud head_term basejud triggerjud_opt colljudI =
  gen_add_nplace_jud (add_coll_jud basejud colljudI triggerjud_opt) CollJud NONE 0 1 colljud head_term

fun add_tactic_proc_nplace_jud nins nouts judname head_term tac =
  gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE nins nouts judname head_term
  #> add_tactic_proc judname tac





fun print_depgraph gctxt = 
  let
    val {depgraph, frules, ...} = get_current_ruledata gctxt
    val ctxt = Context.proof_of gctxt
    val pot_frule_to_str = get_frule_id depgraph
      #> Option.map (get_frule frules #> Display.string_of_thm ctxt)
    val _ = Output.writeln "printing depgraph\n\n"
    val _ = Graph.dest depgraph |> map (fn ((k, _), ks) =>
      let
        val k' = perhaps pot_frule_to_str k
        val ks' = map (perhaps pot_frule_to_str) ks
        val _ = Output.writeln ("dependency:\n    "^
          k'^"\ndepends on\n"^cat_lines (map (fn s => "  *  "^s) ks')
          ^"\n\n")
      in () end)
  in () end






fun gen_metarec_tac debug ctxt =
  SELECT_GOAL (PRIMITIVE (normalize ctxt))
  THEN' SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
    val thy = Proof_Context.theory_of ctxt
    val gctxt = Context.Proof ctxt
    fun err msg =
      let val _ = if debug then tracing msg else ()
      in no_tac end
  in
    case decompose_judgement gctxt concl of
      SOME (jid, (pobj, iobjs, _)) =>
        (case get_judgement_kind gctxt jid of
          NormalJud => 
            let
              val (th, _) = metarec_fully_discharged ctxt jid (pobj, iobjs)
              val _ =
                if debug then tracing ("metarec_tac: result is:  "^Display.string_of_thm ctxt th)
                else ()
            in rtac th i end
        | _ => err "not a normal metarec judgement")
    | _ => err "not a metarec judgement"
  end)

val metarec_tac = gen_metarec_tac false
val metarec_tac_debug = gen_metarec_tac true


(* forw_th :  J P P' ==> P' ==> P *)
fun fconv_metarec forw_th solver ctxt =
  let
    val jud =
      case decompose_judgement (Context.Proof ctxt) (Logic.strip_imp_prems (prop_of forw_th) |> hd) of
        SOME (jud, _) => jud
      | _ => error ("fconv_metarec: premise of forwarding theorem not a metarec judgement"
        ^"\n "^Display.string_of_thm ctxt forw_th)
    (* TODO(correctness): check moding and type of judgement *)
  in
    SELECT_GOAL (PRIMITIVE (normalize ctxt))
    THEN' SUBGOAL (fn (goal, i) =>
    let
      val _ = tracing ("fconv_metarec: metarec on goal "^Syntax.string_of_term ctxt goal)
      val ((res, _), (delayed_unifs, constraints)) = metarec ctxt jud (goal, [])
      val unsolved = not (null delayed_unifs andalso null constraints)
      val _ = tracing ("fconv_metarec: result for forwarding is   "^Display.string_of_thm ctxt res
        ^(if unsolved then
            " but constraints remain: "^commas (map (Syntax.string_of_term ctxt)
              (constraints @ map Logic.mk_equals delayed_unifs))
          else ""))
    in
      if unsolved then
        no_tac
      else
        compose_tac (false, forw_th OF [res], 1) i
        THEN solver i
    end)
  end
  



(* braucht man vllt statt Attributen bzw normalen Deklarationen?!?!?
val _ = Outer_Syntax.local_theory "declare_frule" "declare forward rule" Keyword.thy_decl ...
val _ = Outer_Syntax.local_theory "declare_ffact" "declare forward fact" Keyword.thy_decl ...
*)


(* TODO: should we give back a result with  snd res = NONE  instead of  SOME rule  ?? *)
val MR_decl_attr = Scan.lift (Scan.option Parse.int
  >> (fn prio_opt => fn (gctxt, rule) =>
       let val prio = the_default 0 prio_opt
       in (SOME (add_rule prio rule gctxt), SOME rule) end))
val MR_unchecked_grnd_decl_attr = Scan.lift (Scan.option Parse.int
  >> (fn prio_opt => fn (gctxt, rule) =>
       let val prio = the_default 0 prio_opt
       in (SOME (add_rule_unchecked_grnd prio rule gctxt), SOME rule) end))
val MR_unchecked_decl_attr = Scan.lift (Scan.option Parse.int
  >> (fn prio_opt => fn (gctxt, rule) =>
       let val prio = the_default 0 prio_opt
       in (SOME (add_rule_unchecked prio rule gctxt), SOME rule) end))
val MRassm_decl_attr = Scan.lift (Scan.succeed (fn (gctxt, th) =>
  case gctxt of
    Context.Proof _ => (SOME (Context.map_proof (add_assm true th) gctxt), SOME th)
  | _ => error "MRassm attribute: not in a proof context"))

(* TODO(correctness): actually implement deletion declarations or at least throw
    not-implemented-exception to avoid confusion *)
val add_comp_rule_att = Thm.declaration_attribute add_comp_rule
val del_comp_rule_att = Thm.declaration_attribute (K I)

val ffact_add = Thm.declaration_attribute (fn fact => add_facts_gctxt [fact])
val ffact_del = Thm.declaration_attribute (K I)

val expl_frule_add = Thm.declaration_attribute add_expl_frule
val expl_frule_del = Thm.declaration_attribute (K I)

val traced_expl_frule_add = Thm.declaration_attribute add_traced_expl_frule
val traced_expl_frule_del = Thm.declaration_attribute (K I)

val expl_frule_uncheckedgrnd_add = Thm.declaration_attribute add_expl_frule_unchecked_grnd
val expl_frule_uncheckedgrnd_del = Thm.declaration_attribute (K I)

val impl_frule_add = Thm.declaration_attribute add_impl_frule
val impl_frule_del = Thm.declaration_attribute (K I)

val impl_frule_uncheckedgrnd_add = Thm.declaration_attribute add_impl_frule_unchecked_grnd
val impl_frule_uncheckedgrnd_del = Thm.declaration_attribute (K I)

val constraint_propag_rule_add = Thm.declaration_attribute (add_constraint_propag_rule true)
val constraint_propag_rule_del = Thm.declaration_attribute (K I)

val constraint_simp_rule_add = Thm.declaration_attribute (add_constraint_simp_rule true)
val constraint_simp_rule_del = Thm.declaration_attribute (K I)


(* auf Definitionen mit == anwenden *)
(* TODO(feature): localize, dh head_term ist das was bleibt
     wenn man num_ins+num_outs Argumente wegstrippt und
     nicht wirklich der Head *)
val judgement_decl_attr = Scan.lift
    (Parse.nat -- Parse.nat -- Scan.option (Args.$$$ "allowinconsis")
     -- Scan.option ((Args.$$$ "wfjud" -- Args.colon) |-- Parse.string)
  >> (fn (((num_ins, num_outs), allow_inconsis_opt), wf_jud_opt) => fn (gctxt, defth) =>
       let
         val head_term = prop_of defth |> Logic.dest_equals |> fst |> Term.head_of
           |> singleton (Variable.polymorphic (Context.proof_of gctxt))
         val jud_name = name_from_const_or_free head_term ^ "_jud"
         val allow_inconsis = if is_some allow_inconsis_opt then AllowInconsis else DisallowInconsis
       in
         (* TODO(hackish): judgements sind noch nicht lokalisiert worden und wir verlassen
              uns hier darauf das das Attribut zuerst in der Theorie ausgefuehrt wird *)
         case try (get_judgement_kind gctxt) jud_name of
           SOME _ => (SOME gctxt, SOME defth)
         | NONE =>
              (* -1 weil prim object ja nicht zaehlt hier aber
                 zu verwirrend fuer user *)
             (add_nplace_synth_jud allow_inconsis wf_jud_opt (num_ins - 1)
                num_outs jud_name head_term gctxt |> SOME,
              SOME defth)
       end))

val coll_jud_decl_attr = Scan.lift
  (Parse.string -- Scan.option ((Args.$$$ "trigger" -- Args.colon) |-- Parse.string)
  >> (fn (basejud, triggerjud_opt) => fn (gctxt, defth) =>
       let
         val _ = case get_judgement_kind gctxt basejud of
             NormalJud => ()
           | _ => error ("coll_jud_decl_attr: judgement "^quote basejud
             ^" is not a normal judgment and cannot be collected")
         val _ =
           case triggerjud_opt of
             SOME triggerjud =>
               (case get_judgement_kind gctxt triggerjud of
                 NormalJud => ()
               | _ => error ("coll_jud_decl_attr: judgement "^quote basejud
                 ^" is not a normal judgment and be used as a trigger judgement"))
          | NONE => ()
         val head_term =
           case prop_of defth of
             Const (@{const_name "=="}, _) $ lhs $ rhs =>
               let
                 val (head, args) = Term.strip_comb lhs
                 val _ = case args of
                     [arg1 as (Var _), arg2 as (Var _)] =>
                       let val _ =
                         if fastype_of arg1 = Data.unit_ty andalso fastype_of arg2 = Data.proplist_ty then
                           ()
                         else
                           error ("coll_jud_decl_attr: judgement does not take "
                             ^Library.commas (map (Syntax.string_of_typ (Context.proof_of gctxt))
                                [Data.unit_ty, Data.proplist_ty])^"  arguments")
                       in () end
                   | _ => error ("coll_jud_decl_attr: lhs of collector judgement"
                     ^" definition not of the form  jud x y")
               in
                 head 
                 |> singleton (Variable.polymorphic (Context.proof_of gctxt))
               end
           | _ => error "coll_jud_decl_attr: collector judgement definition not a meta equation"

         val colljud = name_from_const_or_free head_term ^ "_jud"
         val colljudI = Data.gen_colljudI OF [defth]
       in
         (add_nplace_coll_jud colljud head_term basejud triggerjud_opt colljudI gctxt |> SOME,
          SOME defth)
       end))

fun define_lthy_transf (name_ct, [rhs_ct]) lthy =
  let
    val name =
      (* TODO(feature): besser sowas wie
         let (n, ns) = strip_comb name_t
         in (n :: ns) |> map name_from_const_or_free |> space_implode "$" end ? *)
      case try name_from_const_or_free_unsuffix (Thm.term_of name_ct) of
        SOME n => n
      | NONE => err_with_facts lthy ("define_lthy_transf: strange term for name "
          ^Syntax.string_of_term lthy (Thm.term_of name_ct))

    val bnd = Binding.name (Long_Name.base_name name)
    val ((lhs, (n, def_th)), lthy2) = lthy
      |> Local_Theory.define ((bnd, NoSyn), ((Thm.def_binding bnd, []), Thm.term_of rhs_ct))

    val thy2 = Proof_Context.theory_of lthy2
    val lhs_ct = lhs |> cterm_of thy2

    val defmsg = "definition "^Syntax.string_of_term lthy2 (prop_of def_th)
      ^"  :: "^Syntax.string_of_typ lthy2 (Thm.ctyp_of_term lhs_ct |> Thm.typ_of)
    val [name_cT, rhs_cT, lhs_cT] = map ctyp_of_term [name_ct, rhs_ct, lhs_ct]

    (* TODO(semantics): Premisse von def_th dischargen wenn man eigentlich global in ner Theorie ist ? *)
    val th = Data.defineI
      |> Drule.instantiate' (map SOME [lhs_cT, name_cT])
           (map SOME [lhs_ct, rhs_ct, name_ct])
      |> (fn th => th OF [def_th])
    val lthy3 = lthy2 |> map_lthy_transforms_log (cons defmsg)
    (* val _ = tracing defmsg *)
  in
    ((th, [lhs_ct]), lthy3)
  end

fun concat_names_proc ctxt (ct1, [ct2], _) =
  let
    val thy = Proof_Context.theory_of ctxt
    val (t1, t2) = pairself Thm.term_of (ct1, ct2)
    val (cT1, cT2) = pairself ctyp_of_term (ct1, ct2)

    val (n1, n2) = pairself name_from_const_or_free_perhaps_unsuffix (t1, t2)
      (* TODO(semantics): eher map_base_name nutzen *)
    val n' = Long_Name.base_name n1 ^ "_" ^ Long_Name.base_name n2 ^ name_suffix
    val t' = Free(n', Thm.typ_of cT1)
    val ct' = cterm_of thy t'
    val th = Drule.instantiate' (map SOME [cT1, cT2, cT1]) (map SOME [ct1, ct2, ct'])
      Data.concat_namesI
  in
    (th, [ct'])
  end



fun rel_local_frees ctxt rel_frees_opt =
  let
    val {outer_ctxt, ...} = Context.Proof ctxt |> get_the_run_state
    val free_constraints = Variable.constraints_of ctxt |> fst

    val rel_names_tab_opt = rel_frees_opt |> Option.map (fn rel_frees =>
       Symtab.empty |> fold (fn n => Symtab.update (n, ())) (map fst rel_frees))

    val normT = Logic.type_map (norm_with_env_in_run_state ctxt)
    fun add_typing n = Free(n, Vartab.lookup free_constraints (n, ~1) |> the |> normT)
    val local_fixes = Variable.dest_fixes ctxt |> map snd
      |> filter_out (fn n => Variable.is_fixed outer_ctxt n)
    (* val _ = tracing ("rel_local_frees: fixes = "^commas (map snd (Variable.dest_fixes ctxt))
      ^"\n  local_fixes ="^commas local_fixes) *)
    val rel_local_fixes = case rel_names_tab_opt of
        SOME rel_names_tab => local_fixes |> filter (Symtab.defined rel_names_tab)
      | NONE => local_fixes
  in
    map add_typing rel_local_fixes
  end




(* TODO(feature,opt): first-order Unifikationsvariablen anbieten die nicht
     von lokalen Fixes abhaengen koennen. Ist aber im wesentlichen schon mit
     lokalen Constraints geloest (hier allerdings keine transitive first-order
     Forderung entlang von Instantiierungsketten) *)
fun fresh_unifvar_proc ctxt fail_cont (_, [], [outpat0]) =
  let
    val thy = Proof_Context.theory_of ctxt

    val norm = norm_with_env_in_run_state ctxt
    val outpat = norm outpat0
    val local_frees = rel_local_frees ctxt NONE 

    val out_T = fastype_of outpat
    val out_n = outpat |> Term.head_of |> Term.dest_Var |> fst |> fst
      handle TERM _ => err_with_trace ctxt ("fresh_unifvar_proc: output pattern not a variable: "
        ^Syntax.string_of_term ctxt outpat)
    val T = (local_frees |> map (fn Free(n,T2) => T2)) ---> out_T
    val (var, ctxt2) = genvar_on_run_state out_n T ctxt
    val t = list_comb (var, local_frees)
    (* val _ = tracing ("generated fresh unifvar "^Syntax.string_of_term ctxt2 t) *)
    val (res_prf, ctxt3) = inst_match_on_freshthm_prf Data.fresh_unifvarI  [SOME t] ctxt2
      handle
        TYPE (msg, Ts, _) => err_with_trace ctxt2 ("fresh_unifvar_proc: exception in instantiate' with "
          ^Syntax.string_of_term ctxt2 t^":\n"^msg
          ^"\n"^cat_lines (map (Syntax.string_of_typ ctxt2) Ts))
      | THM (msg, _, _) => err_with_trace ctxt2 ("fresh_unifvar_proc: exception in instantiate' with "
          ^Syntax.string_of_term ctxt2 t^":\n"^msg)
  in
    ((res_prf, [t]), SOME (get_the_run_state (Context.Proof ctxt3)))
  end


fun unify_proc ctxt fail_cont (t1_0, [t2_0], _) =
  let
    val thy = Proof_Context.theory_of ctxt
    val { outer_ctxt, env, delayed_unifs, constraints, fo_vars } =
      case get_run_state (Context.Proof ctxt) of
        SOME st => st
      | NONE => err_with_trace ctxt ("unify_proc: no run state set")
    val (t1, t2) = (t1_0, t2_0) |> pairself (norm_with_env_in_run_state ctxt)

    val rel_frees = [] |> fold Term.add_frees [t1, t2]
    val local_frees = rel_local_frees ctxt (SOME rel_frees)

    val (t1_lft, t2_lft) = (t1, t2) |> pairself (fold_rev Term.lambda local_frees)
    (* val _ = tracing ("unify_proc on (lifted) terms "
      ^str_of_normed_term ctxt t1_lft ^",  "^str_of_normed_term ctxt t2_lft) *)

    fun calc_res_state env2 delayed_unifs2 =
      { outer_ctxt=outer_ctxt, env=env2, delayed_unifs=delayed_unifs2,
        constraints=constraints, fo_vars=fo_vars }

    fun nonpattern_cont () =
      let
        val delayed_assm = assumption_prf (Logic.mk_equals (t1_lft, t2_lft))
        val (appd_delayed_assm, ctxt2) = (delayed_assm, ctxt)
          |> fold (fn arg => fn (prf, ctxt_) => fun_cong_prf prf arg ctxt_) local_frees
        val aconv' = aconv_norm (norm_with_env_in_run_state ctxt2)
        val delayed_unifs2 = delayed_unifs
          |> insert (eq_fst (eq_pair aconv' aconv')) ((t1_lft, t2_lft), false)

        (* val _ = tracing ("unify_proc: delayed_assm is "^str_of_normed_term ctxt2 (prop_of_proofp delayed_assm))
        val _ = tracing ("unify_proc: appd_delayed_assm is "^str_of_normed_term ctxt2 (prop_of_proofp appd_delayed_assm)) *)

        val (res_prf, ctxt3) = mps_match_on_freshthm_prf Data.unifyI [appd_delayed_assm] ctxt2

        (* val _ = tracing ("unify_proc: res_prf is "^str_of_normed_term ctxt3 (prop_of_proofp res_prf)) *)

        val env2 = get_the_env_in_run_state ctxt3
        val st2 = calc_res_state env2 delayed_unifs2
      in
        ((res_prf, []), SOME st2)
      end
  in
    (case try_pat_unify ctxt (t1_lft, t2_lft) env of
      SOME env2 => 
        let
          (* val envdiff = env2 |> Envir.term_env |> Vartab.dest
            |> subtract (pairself fst #> (op =)) (Envir.term_env env |> Vartab.dest)
          val _ = tracing ("unify_proc did term instantiation "
            ^commas (envdiff |> map (fn (ixn, (T, t)) =>
               Syntax.string_of_term ctxt (Var(ixn,T)) ^ " := "
               ^ str_of_normed_term ctxt t))) *)

          fun changed_unifprob ((t1_, t2_), solved) =
            not solved
            andalso ([] |> fold (Term.add_vars o Envir.norm_term env) [t1_, t2_]
              |> exists (curry Envir.lookup env2 #> is_some))
          val changed_delayed_unifs = delayed_unifs |> filter changed_unifprob
          val unchanged_delayed_unifs = delayed_unifs |> filter_out changed_unifprob

          val (changed_delayed_unifs', env3) =
            try_solve_delayed_unifs false ctxt changed_delayed_unifs env2
          val st2 = calc_res_state env3 (changed_delayed_unifs' @ unchanged_delayed_unifs)

          val ctxt2 = ctxt |> Context.proof_map (set_run_state (SOME st2))
          val (refl_prf, ctxt3) = reflexive_prf t1 ctxt2
          val (res_prf, ctxt4) = mps_match_on_freshthm_prf Data.unifyI [refl_prf] ctxt3

          (* val _ = tracing ("unify_proc: res_prf is "^Syntax.string_of_term ctxt4
            (Envir.norm_term env3 (prop_of_proofp res_prf))) *)

          val st4 = get_the_run_state (Context.Proof ctxt4)
        in
          ((res_prf, []), SOME st4)
        end
    | NONE => nonpattern_cont ())
    handle TryPatUnify (ctxt, (bad_t1, bad_t2), msg) =>
      fail_cont ctxt ("unify_proc: "^msg)
  end
  

fun constraint_gen_proc local_constraint ctxt fail_cont (t0, [], _) =
  let
    val thy = Proof_Context.theory_of ctxt

    val ctxt2 =
      if local_constraint then ctxt
      else
        let
          val ctxt2_ = ctxt |> unlift_unifvar_occs t0
          val t_ = norm_with_env_in_run_state ctxt2_ t0
          (* val fovars = Term.add_vars t_ [] |> map fst *)
        in
          ctxt2_ (* |> Context.proof_map (map_fovars_in_run_state (union (op =) fovars)) *)
        end

    val norm = norm_with_env_in_run_state ctxt2
    val t = norm t0

    (* val _ = tracing ("generating constraint for "^Syntax.string_of_term ctxt2 t) *)

    (* NB: we don't use Variable.export because we would then have to identify which Vars
       have been generalized on export and which ones are unification variables in the derivation *)
    (* NB: since unification variables are applied to the frees they can depend on this is also correct
       in the case of unification variables in rel_assms that have been instantiated *) 
    (* NB: invariant is that the assms are always wrt. the outer_ctxt *)
    (* NB: since we normed all terms and types we can use op = to compare frees *)
    val rel_frees0 = [] |> Term.add_frees t

    (* val _ = tracing ("rel_frees0 are "^commas (map (Syntax.string_of_term ctxt2 o Free) rel_frees0)) *)

    val local_frees0 = rel_local_frees ctxt2 (SOME rel_frees0) |> map Term.dest_Free

    val _ =
      if local_constraint orelse null local_frees0 then ()
      else
        err_with_trace ctxt2 ("constraint_gen_proc: first-order constraint "
          ^str_of_normed_term ctxt t0^" contains local fixes "^
          commas (map (Syntax.string_of_term ctxt2 o Free) local_frees0)
          ^" after unlifting to "^str_of_normed_term ctxt2 t)

    (* TODO(feature): do we want also transitively-relevant assms for some constraints? *)
    val rel_assms =
      get_assms (Context.Proof ctxt2) |> map norm
      |> filter_out (fn assm => null (inter (op =) (Term.add_frees assm []) local_frees0))
      |> rev
    val rel_frees = local_frees0 |> fold Term.add_frees rel_assms
    val local_frees = rel_local_frees ctxt2 (SOME rel_frees)

    (* val _ = tracing ("rel_frees are "^commas (map (Syntax.string_of_term ctxt2 o Free) rel_frees)
       ^"\nlocal_frees are "^commas (map (Syntax.string_of_term ctxt2) local_frees)) *)
    
    (* val _ =
      if local_constraint orelse null local_frees then ()
      else (* NB: we may not give up in this case because of explicit universe level annotations, e.g. in
          (lam i:nat. lam x:guniv i ...) *)
        err_with_trace ctxt2 ("constraint_gen_proc: constraint "
          ^Syntax.string_of_term ctxt2 (norm_with_env_in_run_state ctxt t)
          ^" contains local frees "^commas (map (Syntax.string_of_term ctxt2) local_frees)
          ^" even after unlifting its unification variables") *)
        

    val t' = fold_rev Logic.all local_frees (Logic.list_implies (rel_assms, t))
    val t'_prf = assumption_prf t'
    val t_prf = t'_prf
      |> fold (allE_rev_prf ctxt2) local_frees
      |> fold (mp_rev_prf ctxt2 o assumption_prf) rel_assms

    (* val _ = tracing ("generating constraint "^str_of_normed_term ctxt2 t'^" ...") *)

    val intro_th = if local_constraint then Data.constraintI else Data.foconstraintI
    val (res_prf, ctxt3) = mps_match_on_freshthm_prf intro_th [t_prf] ctxt2

    (* val _ = tracing ("generated constraint "^str_of_normed_term ctxt3 t') *)

    (* TODO(feature/opt): already simplify constraints on-the-fly *)
    fun constraints_f constraints =
      insert (aconv_norm (norm_with_env_in_run_state ctxt3)) t' constraints
    val st2 = Context.Proof ctxt3 |> map_constraints_in_run_state constraints_f
      |> get_the_run_state
  in
    ((res_prf, []), SOME st2)
  end



val setup =
  Attrib.setup (Binding.name "MR") MR_decl_attr "Declaration of meta recursion clauses"
  #> Attrib.setup (Binding.name "MR_unchecked_grnd") MR_unchecked_grnd_decl_attr
    "Declaration of meta recursion clauses, not checked for groundness"
  #> Attrib.setup (Binding.name "MR_unchecked") MR_unchecked_decl_attr
    "Declaration of meta recursion clauses, not checked for groundness, no dependency analysis"
  #> Attrib.setup (Binding.name "MRassm") MRassm_decl_attr "Declaration of local meta recursion assumptions (in proof contexts)"
  #> Attrib.setup (Binding.name "MRjud") judgement_decl_attr "Declaration of judgement"
  #> Attrib.setup (Binding.name "MRcolljud") coll_jud_decl_attr "Declaration of collector judgement"
  #> Attrib.setup (Binding.name "ffact") (Attrib.add_del ffact_add ffact_del)
    "Declaration of forward facts"
  #> Attrib.setup (Binding.name "expl_frule") (Attrib.add_del expl_frule_add expl_frule_del)
    "Declaration of explicit forward rules"
  #> Attrib.setup (Binding.name "traced_expl_frule") (Attrib.add_del traced_expl_frule_add traced_expl_frule_del)
    "Declaration of traced_explicit forward rules"
  #> Attrib.setup (Binding.name "impl_frule") (Attrib.add_del impl_frule_add impl_frule_del)
    "Declaration of implicit forward rules"
  #> Attrib.setup (Binding.name "expl_frule_unchecked_grndness") (Attrib.add_del expl_frule_uncheckedgrnd_add expl_frule_uncheckedgrnd_del)
    "Declaration of explicit forward rules without groundness checking"
  #> Attrib.setup (Binding.name "impl_frule_unchecked_grndness") (Attrib.add_del impl_frule_uncheckedgrnd_add impl_frule_uncheckedgrnd_del)
    "Declaration of implicit forward rules without groundness checking"
  #> Attrib.setup (Binding.name "comp_rule") (Attrib.add_del add_comp_rule_att del_comp_rule_att)
      "Declaration of computational rules for Soft Type Checking"
  #> Attrib.setup (Binding.name "constraint_propag_rule") (Attrib.add_del constraint_propag_rule_add constraint_propag_rule_del)
    "Declaration of constraint propagation rules"
  #> Attrib.setup (Binding.name "constraint_simp_rule") (Attrib.add_del constraint_simp_rule_add constraint_simp_rule_del)
    "Declaration of constraint simplification rules"
  #> Context.theory_map (
       gen_add_nplace_synth_jud DisallowInconsis LthyTransfJud NONE 1 1 define_jud Data.define_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis NormalJud NONE 1 0 note_jud Data.note_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE 1 1 concat_names_jud Data.concat_names_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE 0 1 fresh_unifvar_jud Data.fresh_unifvar_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE 1 0 unify_jud Data.unify_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE 0 0 constraint_jud Data.constraint_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE 0 0 foconstraint_jud Data.foconstraint_headterm)
  #> Context.theory_map (
       add_syn_proc concat_names_jud "concat_names_proc" concat_names_proc
       #> add_general_syn_proc fresh_unifvar_jud "fresh_unifvar_proc" fresh_unifvar_proc
       #> add_general_syn_proc unify_jud "unify_proc" unify_proc
       #> add_general_syn_proc constraint_jud "constraint_gen_proc" (constraint_gen_proc true)
       #> add_general_syn_proc foconstraint_jud "foconstraint_gen_proc" (constraint_gen_proc false)
       #> add_lthy_transform define_jud  "define" define_lthy_transf)


(* val _ =
  Outer_Syntax.local_theory "run_expl_frules" "run explicit frules"
  Keyword.thy_decl
  (Scan.succeed run_expl_frules) *)



end
