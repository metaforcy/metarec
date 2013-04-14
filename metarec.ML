
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
end


functor MetaRec(Data : MetaRecData) =
struct





(* TODO(feature): err_with_trace hiermit nutzen *)
fun string_of_thm_in_gctxt gctxt =
  case gctxt of
    Context.Proof ctxt => Display.string_of_thm ctxt
  | Context.Theory thy => Display.string_of_thm_global thy



infix abeconv
infix abeconvs
fun t1 abeconv t2 = (Envir.beta_eta_contract t1) aconv (Envir.beta_eta_contract t2)
fun t1s abeconvs t2s = forall (op abeconv) (t1s ~~ t2s)


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


val beta_eta_convert = Conv.fconv_rule Drule.beta_eta_conversion
val beta_convert = Conv.fconv_rule (Thm.beta_conversion true)
val eta_convert = Conv.fconv_rule Thm.eta_conversion
val beta_eta_long_convert = Conv.fconv_rule Thm.eta_long_conversion

val beta_norm_cterm = Thm.beta_conversion true #> Thm.rhs_of


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



(* (#input args (not counting the primary argument), #output args) *)
type mode = int * int
type frule_id = int
datatype frule_kind = ImplicitFRule | ExplicitFRule
datatype depgraph_node = Judgement | FRule of frule_id

fun is_synth_mode (ninput, noutput) = (noutput > 0)
fun synth_objs_from_sec_objs mode sec_objs = drop (fst mode) sec_objs

(* TODO(semantics): besser NormalJud in FactJud, RecJud aufteilen? *)
datatype judgement_kind = NormalJud | CollJud | ProcJud | LthyTransfJud
datatype allow_inconsis = AllowInconsis | DisallowInconsis
(* head_term has to be in most general form *)
type judgements_type = (analyzer_ty * term * mode * judgement_kind *
  (thm * string * string option) option * string option * allow_inconsis) Symtab.table
  (* running_expl_frules,   running_on_thy_lvl *)
type run_info_ty = bool * int 

  (* stands for an arbitrary judgement, i.e. depends on all available
     judgements *)
val arb_judgement = "ARB_JUDGEMENT"
val arb_head_term = Free(arb_judgement, Term.dummyT --> @{typ prop})


  (* werden spaeter noch explizit hinzugefuegt, deshalb nicht in den
     initialen Datenstrukturen vorhanden *)
val define_jud = "define_jud"
val note_jud = "note_jud"
val concat_names_jud = "concat_names_jud"

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

fun rule_net_index (judgements : judgements_type) term_to_jud (thm, prior) =
  thm |> Thm.concl_of |> gen_decompose_judgement term_to_jud judgements (fn _ => "<term (no term printer)>")
  |> Option.map (fn (_, (pobj, iobjs, oobjs)) => pack_pobj_iobjs pobj iobjs)
  |> the_list
fun eq_for_net ((thm1, _), (thm2, _)) = Thm.eq_thm_prop (thm1, thm2)




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
    rules: ((thm * int) Item_Net2.T) Symtab.table,
    judgements: judgements_type,
    term_to_jud: string Net.net,
    assms: thm list,
      (* synthesis procedures indexed by the judgement name
         if invoked in frule-applications the current theory
         is only available via the generic context *)
    syn_procs: (string * (Proof.context -> (cterm * cterm list * cterm list) -> (thm * cterm list))) Symtab.table,
    comp_rules: simpset option,
    trace_depth: int * int,
    trace: ((unit -> thm) list) * ((unit -> string) list),

    facts: thm Net.net,
      (* facts indexed by non-wellformed term combination  pack_pobj_iobjs pobj iobjs *)
    facts_lhs_idx: thm Net.net,
      (* conservative approx der Abhaengigkeiten unter Judgements und frules
         enthaelt auch die Abhaengigkeiten enthalten, die durch (aus bestehenden frules)
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
    new_facts: thm list Symtab.table
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
     new_facts = Symtab.empty
   }

val base_scope = 0
val init_run_info = (false, 0)

(* Daten aus der Hintergrundtheorie werden bei init von Beweiskontexten
   automatisch uebernommen *)
structure RuleData = Generic_Data(
  type T = int * ruledata_type Inttab.table * run_info_ty
  val empty = (base_scope, Inttab.empty |> Inttab.update_new (base_scope, empty_ruledata), init_run_info)
  val extend = I

  fun merge ((scope1, tab1, run_info1), (scope2, tab2, run_info2)) =
    let
      val _ =
        if scope1 = base_scope andalso scope2 = base_scope then ()
        else
          error ("RuleData.merge: scopes are nontrivial")

      fun merge_ruledata (data1, data2) =
        let
          val {rules=rules1, judgements=judgements1, term_to_jud=term_to_jud1, assms=assms1, syn_procs=syn_procs1,
            comp_rules=comp_rules1, trace_depth=trace_depth1, trace=trace1, facts=facts1, facts_lhs_idx=facts_lhs_idx1,
            depgraph=depgraph1, frules=frules1, frules_hdidx=frules_hdidx1, frules_factgen=frules_factgen1,
            gen_brule_concls=gen_brule_concls1, lthy_transforms=lthy_transforms1, lthy_transform_log=lthy_transform_log1,
            new_facts=new_facts1} = data1
          val {rules=rules2, judgements=judgements2, term_to_jud=term_to_jud2, assms=assms2, syn_procs=syn_procs2,
            comp_rules=comp_rules2, trace_depth=trace_depth2, trace=trace2,
            facts=facts2, facts_lhs_idx=facts_lhs_idx2, depgraph=depgraph2, frules=frules2, frules_hdidx=frules_hdidx2,
            frules_factgen=frules_factgen2, gen_brule_concls=gen_brule_concls2, lthy_transforms=lthy_transforms2,
            lthy_transform_log=lthy_transform_log2, new_facts=new_facts2} = data2
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
            new_facts = Symtab.empty
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

    



fun map_rule_stuff f_rules f_depgraph = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules = f_rules rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = f_depgraph depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_judgement_stuff f_judgements f_term_to_jud f_depgraph = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements = f_judgements judgements,
     term_to_jud = f_term_to_jud term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = f_depgraph depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_term_to_jud f_term_to_jud = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements = judgements,
     term_to_jud = f_term_to_jud term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_assms f_assms = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements = judgements,
     term_to_jud=term_to_jud, assms = f_assms assms, syn_procs=syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_syn_procs f_syn_procs = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements = judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs = f_syn_procs syn_procs,
     comp_rules = comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_comp_rules f_comp_rules = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules = f_comp_rules comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun set_trace_depth d = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth = d, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_trace f_trace = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth = trace_depth, trace = f_trace trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_fact_stuff f_facts f_facts_lhs_idx f_new_facts = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts = f_facts facts, facts_lhs_idx= f_facts_lhs_idx facts_lhs_idx,
     depgraph=depgraph,
     frules=frules, frules_hdidx=frules_hdidx, frules_factgen=frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log,
     new_facts = f_new_facts new_facts})

fun map_frule_stuff f_depgraph f_frules f_frules_hdidx f_frules_factgen = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph = f_depgraph depgraph,
     frules = f_frules frules,
     frules_hdidx = f_frules_hdidx frules_hdidx, frules_factgen = f_frules_factgen frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_gen_brule_concls f_gen_brule_concls = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules,
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=f_gen_brule_concls gen_brule_concls,
     lthy_transforms=lthy_transforms, lthy_transform_log=lthy_transform_log, new_facts=new_facts})

fun map_lthy_transforms f_lthy_transforms = map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
    {rules=rules, judgements=judgements,
     term_to_jud=term_to_jud, assms=assms, syn_procs=syn_procs,
     comp_rules=comp_rules, trace_depth=trace_depth, trace=trace,
     facts=facts, facts_lhs_idx=facts_lhs_idx,
     depgraph=depgraph,
     frules = frules, 
     frules_hdidx = frules_hdidx, frules_factgen = frules_factgen,
     gen_brule_concls=gen_brule_concls,
     lthy_transforms = f_lthy_transforms lthy_transforms,
     lthy_transform_log = lthy_transform_log, new_facts=new_facts})

fun map_lthy_transforms_log f_lthy_transform_log =
  Local_Theory.target (Context.proof_map (map_current_ruledata
  (fn {rules, judgements, term_to_jud, assms, syn_procs, comp_rules, trace_depth, trace,
       facts, facts_lhs_idx, depgraph, frules, frules_hdidx, frules_factgen,
       gen_brule_concls, lthy_transforms, lthy_transform_log, new_facts} =>
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
     new_facts=new_facts})))
 
fun get_lthy_transform_log lthy =
  let val {lthy_transform_log = log, ...} =
    get_current_ruledata (Context.Proof (Local_Theory.target_of lthy))
  in log end

fun set_running_expl_frules running_expl_frules =
  Local_Theory.target (Context.proof_map (RuleData.map (fn (scope, ruledata, run_info) =>
    (scope, ruledata,
     run_info |> (fn (_, running_on_thy_lvl) =>
       (running_expl_frules, running_on_thy_lvl))))))
 
fun get_running_expl_frules ctxt =
  if can Local_Theory.assert ctxt then
     let val (_, _, (running_expl_frules, _)) =
       RuleData.get (Context.Proof (Local_Theory.target_of ctxt))
     in running_expl_frules end
  else
    false


fun update_running_on_thy push thy =
  thy |> Context.theory_map (RuleData.map (fn (scope, ruledata, run_info) =>
    (scope, ruledata,
     run_info |> (fn (running_expl_frules, running_on_thy_lvl) =>
       let
         val running_on_thy_lvl' =
           if push then running_on_thy_lvl + 1
           else if running_on_thy_lvl = 0 then error "update_running_on_thy: pop not possible"
           else running_on_thy_lvl - 1
       in 
         (running_expl_frules, running_on_thy_lvl')
       end))))
val push_running_on_thy = update_running_on_thy true
val pop_running_on_thy = update_running_on_thy false

fun is_running_on_thy ctxt =
  let val (_, _, (_, running_on_thy_lvl)) =
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
       ^cat_lines (take rule_trace_depth rule_trace |> map (fn th => "\n"^Display.string_of_thm ctxt (th ())))
     ^"\n\nmessage trace is\n"
       ^cat_lines (take msg_trace_depth msg_trace |> map (fn msg => msg ())))
  end
fun err_with_trace ctxt msg = error (compose_err_from_trace ctxt msg)

 (* d.h. suche Fakten die gegen pat matchen, weil Fakten Var-frei *)
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
         #> map (fst #> Display.string_of_thm ctxt))))
   end
fun err_with_facts ctxt msg = error (gen_msg_with_facts ctxt msg)
fun err_with_trace_and_facts ctxt msg =
  error (gen_msg_with_facts ctxt (compose_err_from_trace ctxt msg))
fun trace_with_facts ctxt msg = tracing (gen_msg_with_facts ctxt msg)


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


fun add_syn_proc jud proc_id proc = map_syn_procs (Symtab.update (jud, (proc_id, proc)))

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



(* nimmt beta-normale HO-Patterns pat und term an,
 eta-expandiert on-the-fly
 Beachte: nimmt auch an das term ein HO-Pattern ist, also
   falls noetig in freeze-unfreeze einpacken
 BTW: Typen von pat, term werden von Pattern.match selbst gematcht *)
fun gen_pattern_match_opt match thy (pat,  term) =
  (let
    val (tyenv, tenv) = match thy (pat, term) (Vartab.empty, Vartab.empty)
    val Tinst = Vartab.dest tyenv |> map (fn (ixn, (sort, ty)) => ((ixn, sort), ty))
    val inst = Vartab.dest tenv |> map (fn (ixn, (T, t)) => ((ixn, Envir.norm_type tyenv T), t))
   in SOME (Tinst, inst) end)
  handle MATCH => NONE

val pattern_match_opt = gen_pattern_match_opt Pattern.match
val pattern_matches_opt =
  let fun match thy (pats, terms) = fold (Pattern.match thy) (pats ~~ terms)
  in gen_pattern_match_opt match end
(* assumes cterms are ground *)
fun cpattern_matches_opt thy (cpats, cterms) =
  ([], [])
  |> fold (fn (cpat, cterm) => fn inst =>
         let
           (* NB: cterms are ground, so this cannot create deep variable instantiations, 
                which we don't want for matching *)
           val (cpat', cterm') = (cpat, cterm) |> pairself (Thm.instantiate_cterm inst)
           val inst2 = Thm.match (cpat', cterm')
         in (fst inst @ fst inst2, snd inst @ snd inst2) end)
       (cpats ~~ cterms)
  |> SOME
  handle MATCH => NONE
fun cpattern_match_opt thy (cpat, cterm) = cpattern_matches_opt thy ([cpat], [cterm])
  

val decompose_pattern_match_opt = gen_pattern_match_opt DecompPattern.decompose_match

fun cert_inst thy (Tinst, inst) =
  (Tinst |> map ((fn ((ixn, S), T) => (TVar (ixn, S), T)) #> pairself (ctyp_of thy)),
   inst |> map ((fn ((ixn, T), t) => (Var (ixn, T), t)) #> pairself (cterm_of thy)))

fun no_lambdas (t1 $ t2) = no_lambdas t1 andalso no_lambdas t2
  | no_lambdas (Abs(_,_,_)) = false
  | no_lambdas _ = true

(* TODO(opt): decomposing pattern matching mit cterm verwaltung *)
fun cdecompose_pattern_match_opt thy (cpat, cterm) =
  (* TODO: nimmt die einfache Semantik von decompose pattern matching an,
      ohne Verschraenkung von first-order und higher-order pattern matching *)
  (* der no_lambdas Fall ist 70-80 Mal haeufiger *)
  if no_lambdas (Thm.term_of cpat) then (* so no implicit eta expansion of cterm can happen *)
    cpattern_match_opt thy (cpat, cterm)
  else
    decompose_pattern_match_opt thy (Thm.term_of cpat, Thm.term_of cterm)
    |> Option.map (cert_inst thy)


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






(* TODO(semantics): dynamisch auf Wohlgeformtheit der entstehenden Metafunktion
     pruefen, dh zu jedem Atom und inputs gibt es hoechstens eine Annahme
     fuer ein Judgement *)
(* TODO(opt): add_fact auf lokale Fakten optimieren
     vllt auch nur dann als lokales Faktum hinzufuegen
     wenn das Judgement bestimmte Form hat? *)
(* NB: darf zugruendeliegende thy des ctxts nicht veraendern,
    insbesondere auch keine declarations erlaubt (weil die checkpoints
    emittieren) *)
and add_assm checked th ctxt =
  let
    val rule =
      if null (Logic.strip_params (prop_of th)) then th
      else Thm.forall_elim_vars 0 th
    val prop = prop_of rule
    val (prems, concl) = Logic.strip_horn prop
    val is_rule = gen_check_rule checked checked ctxt prop |> is_some
    val is_fact = is_rule andalso null prems andalso null (Term.add_vars concl [])
      andalso null (Term.add_tvars concl [])
    val frule_opt = 
      case Term.head_of prop of
        Const (n, _) =>
          if n = Data.frule_const_name then
            rule |> Conv.fconv_rule (Conv.rewr_conv Data.frule_const_def) |> SOME
          else NONE
      | _ => NONE

    val ctxt' = ctxt
      |> Context.proof_map (map_assms (cons th))
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




(* prems have to be normal, rule is only used for printing *)
 (* ctxt is the thy-transferred version of ctxt0 corresponding to 
    lthy transformations potentially done on gctxt
    NB: ctxt is not really propagated linearly here, everything starts from
      a theory transferred ctxt0, which is also the first output
 *)
and solve_prems topcall allow_lthy_transf global_fail_cont local_fail_cont rule prems ctxt0 =
  let
    exception LocalFail of Proof.context * string
    exception GlobalFail of Proof.context * string

    fun solve_prem prem (inst, ctxt) =
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
        val prem2 = Thm.instantiate_cterm inst prem
          |> normalize_cterm ctxt
        fun act_rule () = Thm.instantiate inst rule
          |> normalize_withvars ctxt

        (* TODO(tuning): use Subgoal.focus to prove prem
             but how to deal with implicit normalization?
               normalize prem2 instead!
             (will probably degrade performance, so not really a good idea?) *)
        val params_raw = Logic.strip_params (Thm.term_of prem2)
        val (param_names, ctxt_rec0) = Variable.variant_fixes (map fst params_raw) ctxt 
        val (params, prem2_body) = prem2 |> strip_alls_cterm param_names 
          (* noetig weil durch Parameterfixierung non-Patterns entstehen *)
        val lam_abs = fold_rev Thm.lambda params
        val (prem2_assms, prem2_concl) = strip_horn_cterm prem2_body 
        val (prem2_assm_ths, ctxt_rec1) = ctxt_rec0 |> Assumption.add_assumes prem2_assms
        val ctxt_rec = ctxt_rec1 |> fold (add_assm false) prem2_assm_ths

        val (fail_ex, prem2_concl', pot_wrap_try) =
          case try cdest_try prem2_concl of
            SOME x => (LocalFail, x, fn th => Data.tryI OF [th])
          | NONE => (GlobalFail, prem2_concl, I)
        fun discharge ctxt2 th = 
          th |> pot_wrap_try
          |> Assumption.export false ctxt_rec ctxt
          |> Drule.forall_intr_list params
        (* TODO: drop local fixes, assumptions, frule generated facts, but retain
             the state (lifted out from the extended context)
             (esp. remaining non-pattern unification problems), which is
             implemented as a special field of the rule_data record.
           metarec_worker then also has to return an output context, which only
             differs in the state from the input context*)
        (* fun discharge_ctxt ctxt2 =
          ctxt |> update_lifted_state_from ctxt2 *)
        fun extend_inst inst new_inst = inst
          |> apfst (append (fst new_inst))
          |> apsnd (append (snd new_inst))

        (* val _ = tracing ("solve_prems: prem2_concl' is "^
          Syntax.string_of_term ctxt_rec (mark_eta_redexes (Thm.term_of prem2_concl'))) *)
      in
        case decompose_judgement_cterm gctxt prem2_concl' of
          SOME (jid, (pobj_of_prem, iobjs_of_prem, oobj_pats_of_prem)) => 
            let
              (* val _ = tracing ("solve_prems: pobj_of_prem is "^
                Syntax.string_of_term ctxt_rec (mark_eta_redexes (Thm.term_of pobj_of_prem))) *)
              val ctxt_rec' = add_to_rule_trace act_rule ctxt_rec
              val ((discharged_th, oobjs), ctxt2) =
                (case Symtab.lookup syn_procs jid of
                  SOME (_, proc) =>
                    (* TODO(feature): local backtracking falls proc fehlschlaegt sinnvoll ?! *)
                    (proc ctxt_rec' (pobj_of_prem, iobjs_of_prem, oobj_pats_of_prem), ctxt)
                | NONE =>
                    (case Symtab.lookup lthy_transforms jid of
                      SOME (lthy_transform_id, lthy_transform) =>
                        if (not allow_lthy_transf) then
                          err_with_trace ctxt_rec' ("solve_prems: lthy transformation not allowed")
                        else if not (null params andalso null prem2_assms) then
                          err_with_trace ctxt_rec' ("solve_prems: lthy transformation under fixes or assumes not allowed")
                        else if get_running_expl_frules ctxt then
                          (* ctxt = ctxt_rec' weil keine Param oder Annahmen
                             ctxt ist eine lthy *)
                          let
                            val lthy = ctxt
                            val (res as (resth, _), lthy2) = lthy
                              |> lthy_transform (pobj_of_prem, iobjs_of_prem)
                          in
                            (res, lthy2)
                          end
                        else
                          err_with_trace ctxt_rec' ("solve_prems: expected local theory to do lthy transformation "
                            ^quote lthy_transform_id^" on "^Syntax.string_of_term ctxt_rec (Thm.term_of prem2_concl'))
                    | NONE =>
                        (* NB: recursive calls to solve_prems in metarec_worker are not
                            allowed to do lthy transformations; ctxt_rec' always contains generated
                            brules of gctxt, cf. gen_with_pot_frules *)
                        (metarec_worker topcall ctxt_rec'
                           (SOME (fn ctxt => fn msg => raise fail_ex (ctxt, msg)))
                           jid (pobj_of_prem, iobjs_of_prem),
                         ctxt)))
                |> (fn ((th, oobjs), ctxt2) =>
                     (* FIXME: wenn lthy transformation Local_Defs nutzt will man diese Assumptions
                         nicht exporten! *)
                     ((discharge ctxt2 th, map (normalize_cterm ctxt2) oobjs), (* discharge_ctxt *) ctxt2))
              val new_inst =
                case cpattern_matches_opt (Proof_Context.theory_of ctxt2) (map lam_abs oobj_pats_of_prem, map lam_abs oobjs) of
                  SOME x => x
                | NONE =>
                    let
                      val maker' = lookup_judgement_analyzer judgements jid |> the |> #2
                      val t = maker' (Proof_Context.theory_of ctxt2)
                        (Thm.term_of pobj_of_prem, map Thm.term_of iobjs_of_prem, map Thm.term_of oobjs)
                    in
                      raise fail_ex (ctxt2, "solve_prems: recursive synthesized judgement "  
                      ^"\n     "^Syntax.string_of_term ctxt2 t
                      ^"\ndoes not match premise (with lifting parameters ["
                        ^Library.commas (map (Syntax.string_of_term ctxt2 o Thm.term_of) params)
                      ^"])\n     "^Syntax.string_of_term ctxt2 (Thm.term_of prem2_concl')
                      ^"\nof instantiated rule "
                      ^"\n     "^Display.string_of_thm ctxt2 (act_rule ())
                      ^"\n\n raw oobjs: \n" ^cat_lines (map PolyML.makestring oobjs)
                      ^"\n\n raw oobj_pats: \n"^cat_lines (map PolyML.makestring oobj_pats_of_prem))
                    end
            in
              (discharged_th, (extend_inst inst new_inst, ctxt2))
            end
        | NONE =>
            err_with_trace ctxt_rec ("solve_prems: not a known judgement in instantiated premise"
                 ^"\n      "^Syntax.string_of_term ctxt_rec (Thm.term_of prem2_concl')
                 ^"\nof instantiated rule"
                 ^"\n      "^Display.string_of_thm ctxt_rec (act_rule ()))
      end
  in
    (([],[]), ctxt0) |> fold_map solve_prem prems
      (* TODO(opt): noch noetig wenn prem2 schon normalisiert wird ? *)
    |-> (fn ths => fn (inst, ctxt') =>
          (map (normalize ctxt') ths, (inst, ctxt')))
      handle
        LocalFail (ctxt, msg) => local_fail_cont ctxt msg
      | GlobalFail (ctxt, msg) => global_fail_cont ctxt msg
  end





(* pobj, iobjs may not contain any Vars and have to be beta,comp_rules-normal *)
and metarec_worker topcall ctxt global_fail_cont_opt jid (pobj, iobjs) =
  let
    val gctxt = Context.Proof ctxt
    val {rules, judgements, ...} = get_current_ruledata gctxt

    exception LocalFail
    exception GlobalFail of Proof.context * string
    val global_fail_cont =
      case global_fail_cont_opt of
        SOME fc => fc
      | NONE => err_with_trace

    val _ =
      if length iobjs = fst (get_judgement_mode gctxt jid)then ()
      else err_with_trace ctxt ("metarec_worker: judgement "^quote jid
         ^" has wrong number of input objects "^Library.commas (map (Syntax.string_of_term ctxt o Thm.term_of) iobjs))

    val thy = Proof_Context.theory_of ctxt
    val jud_cmatcher =
      case lookup_judgement_analyzer judgements jid of
        SOME (_, _, jud_cmatcher) => jud_cmatcher
      | NONE => err_with_trace ctxt ("metarec_worker: judgment "^quote jid^" not known")

    val pot_rules = case Symtab.lookup rules jid of
        SOME inet =>
          Item_Net2.retrieve_match inet
            (pack_pobj_iobjs (Thm.term_of pobj) (map Thm.term_of iobjs) |> Envir.eta_contract)
          |> order_by_priority
      | NONE => [] (* error ("metarec_worker: no rules registered for judgement "^quote jid) *)

    fun no_match failed_rules =
      let val no_match_msg =
        "metarec_worker: no matching rule for animation of judgement "
        ^quote jid^" for primary object\n"^Syntax.string_of_term ctxt (Thm.term_of pobj)
         ^"\nand further inputs\n"^cat_lines (map (Syntax.string_of_term ctxt o Thm.term_of) iobjs)
         ^(if null failed_rules then
             ""
           else
             "\nfailed rules:\n"^cat_lines (map (Display.string_of_thm ctxt) failed_rules))
         ^"\npotential rules:\n"^cat_lines (map (Display.string_of_thm ctxt) pot_rules)
      in
        raise GlobalFail (ctxt, no_match_msg)
      end



    fun rulematch () =
      let
        fun rename_and_inst_rule rule inst = 
          let
            (* val _ = tracing ("before renaming and inst: "^Syntax.string_of_term ctxt (mark_eta_redexes (prop_of rule))) *)
              (* rename bound variables for better error messages *)
              (* use uninstantiated rule to avoid confusion with var:=abstraction instantiations *)
              (* pobj_of_rule, iobjs_of_rule  und  obj, iobjs  beta-normal wg add_rule *)
            val (pobj_of_rule, iobjs_of_rule, _) = rule |> cconcl_of |> jud_cmatcher |> the
            val rule1 = rule
              |> Thm.rename_boundvars (pack_pobj_iobjs (Thm.term_of pobj_of_rule) (map Thm.term_of iobjs_of_rule))
                   (pack_pobj_iobjs (Thm.term_of pobj) (map Thm.term_of iobjs))
            val res = Thm.instantiate inst rule1 |> normalize_withvars ctxt
            (* val _ = tracing ("after renaming and inst: "^Syntax.string_of_term ctxt (mark_eta_redexes (prop_of res))) *)
          in
            res
          end
        fun app_rule rule' = 
          let
            val prems' = Drule.cprems_of rule'
            val (solved_prems, (inst', _)) =
              solve_prems false false
                (fn ctxt => fn msg => raise GlobalFail (ctxt, msg))
                (fn _ => fn _ => raise LocalFail)
                rule' prems' ctxt

            (* val _ = tracing ("solved prems are: "^commas
              (solved_prems |> map (Syntax.string_of_term ctxt o mark_eta_redexes o prop_of)))

            val _ = tracing ("concl-matching-instantiated rule is: "
              ^Syntax.string_of_term ctxt (prop_of rule' |> mark_eta_redexes)) *)

            (* TODO(correctness): normalize_withvars nutzen weil nichtinst Vars
                 im Typ von Refinement-Regeln uebrigbleiben duerfen? oder verbieten? *)
            val rule'' = Thm.instantiate inst' rule' |> normalize ctxt

            (* val _ = tracing ("premise-solving-instantiated and normalized rule is: "
              ^Syntax.string_of_term ctxt (prop_of rule'' |> mark_eta_redexes)) *)


            val (pobj_of_rule'', iobjs_of_rule'', oobjs_of_rule'') =
              cconcl_of rule'' |> jud_cmatcher |> the
            (* TODO(opt): refinement check weglassen wenn iobj_pat der uninstantiierten Regel
                bereits ein pattern war *)
            val _ = map2 (fn iobj => fn iobj_of_rule =>
                  (* iobj_of_rule  und  iobj  beta-normal, s.o. *)
                if Pattern.pattern (Thm.term_of iobj_of_rule) then 
                  case cpattern_match_opt thy (iobj_of_rule, iobj) of
                    SOME _ =>
                      (* TODO(correctness): instantiierung noch auf rule'' anwenden
                           sonst ist rule'' allgemeiner als das was mit den iobjs gefordert wurde *)
                      ()
                  | NONE => raise LocalFail
                else
                  err_with_trace ctxt ("metarec_worker: refinement not a pattern after"
                    ^" instantiation with synthesized information"))
              iobjs iobjs_of_rule''
            
            val res = Drule.implies_elim_list rule'' solved_prems
            (* val _ = tracing ("discharged rule assumptions gave "
              ^Syntax.string_of_term ctxt (prop_of res |> mark_eta_redexes)) *)
          in
            (res, oobjs_of_rule'')
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
                val (pobj_pat, iobj_pats, _) = rule |> cconcl_of |> jud_cmatcher |> the
                fun match_iter [] [] succ_cont inst = succ_cont inst
                  | match_iter (iobj_pat :: rem_iobj_pats) (iobj :: rem_iobjs) succ_cont inst =
                        (* kein eta, wird on-the-fly expandiert *)
                      let val iobj_pat' = Thm.instantiate_cterm inst iobj_pat |> beta_norm_cterm
                      in
                        if Pattern.pattern (Thm.term_of iobj_pat') then
                           (case cpattern_match_opt thy (iobj_pat', iobj) of
                             NONE => first_succ rem_rules failed_rules
                           | SOME inst2 =>
                               match_iter rem_iobj_pats rem_iobjs succ_cont
                                 (inst2 |> apfst (append (fst inst))
                                   |> apsnd (append (snd inst))))
                        else 
                          (* fuer dieses Argument also bisher nur struktureller Abgleich uebers Netz gecheckt,
                             spaeter wird geprueft ob das gereicht hat.
                             wenn das nicht gereicht, schmeisst der sanity check die LocalFail exception
                             und probiert somit auch die anderen matchenden Regeln *)
                          match_iter rem_iobj_pats rem_iobjs succ_cont inst
                      end
              in
                (* Implicitly degrades to structural first-order matching (which is also
                   decompose in this sense) if pobj_pat is not a pattern. *)
                case cdecompose_pattern_match_opt thy (pobj_pat, pobj) of
                  NONE => first_succ rem_rules failed_rules
                | SOME inst0 =>
                    inst0 |> match_iter iobj_pats iobjs (fn inst =>
                      let val rule' = rename_and_inst_rule rule inst
                      in
                        app_rule rule'
                        handle LocalFail => first_succ rem_rules (rule' :: failed_rules)
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
            let val ctxt_rec = ctxt |> add_to_msg_trace (fn () =>
              "metarec_simp_prover: trying to prove "^Syntax.string_of_term ctxt goal
                ^" via meta recursion")
            in rtac (metarec ctxt_rec jid (pobj, iobjs) |> fst) i end))))
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




  
  

(* pobj, iobjs  may not contain any Vars
  find beta,comp_rule-normal  oobjs  with  J pobj iobjs oobjs *)
and metarec ctxt0 jid (pobj, iobjs) =
  let
    val thy = Proof_Context.theory_of ctxt0
    val ctxt = ctxt0 |> add_to_msg_trace (fn () =>
      "metarec: on judgement "^quote jid^" with input ("
        ^Syntax.string_of_term ctxt0 pobj^", ["^Library.commas (map (Syntax.string_of_term ctxt0) iobjs)^"])")
      |> fold Variable.declare_term (pobj :: iobjs)
    val {judgements, ...} = get_current_ruledata (Context.Proof ctxt)
    val jud_maker =
      case lookup_judgement_analyzer judgements jid of
        SOME (_, jud_maker, _) => jud_maker
      | NONE => err_with_trace ctxt ("metarec: judgment "^quote jid^" not known")

    val cert = cterm_of thy
    val pobj' = normalize_term ctxt pobj
    val iobjs' = map (normalize_term ctxt) iobjs

    val (th, coobjs)= metarec_worker true ctxt NONE jid (cert pobj', map cert iobjs')
    val oobjs = map Thm.term_of coobjs
    val orig_jud = jud_maker (Proof_Context.theory_of ctxt) (pobj, iobjs, oobjs)
      (* TODO(opt): nur close_derivation machen wenn die Ableitung gross genug war ?! *)
    (* un-normalize to original judgement *)
    val res = (Drule.equal_elim_rule2 OF [normalize_term_conv ctxt orig_jud, th])
      |> Thm.close_derivation
  in
    (res, oobjs)
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
            val _ = (pobj_of_prem :: iobjs_of_prem)
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
         (Item_Net2.cons (rule, prior) (rule_net_index judgements term_to_jud)))
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
        fun do_solve_prems () = solve_prems true true global_fail_cont local_fail_cont
          inst_frule_wo_heads (Drule.cprems_of inst_frule_wo_heads) ctxt

        fun succ_cont (solved_prems, (inst', ctxt')) =
            let
              val thy' = Proof_Context.theory_of ctxt'
              val frule'' = Thm.instantiate inst' inst_frule_wo_heads |> normalize ctxt'
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
                      |> normalize_withvars ctxt'
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
                             #> (fn gctxt => gctxt |> gen_add_rule true false (Context.proof_of gctxt) 0 brule')
                           end
                         (* NB: we want generated brules to be available in subsequent metarec calls *)
                       (* val msg = "adding generated brule "^Display.string_of_thm ctxt2 brule *)
                       val ctxt3 = ctxt2
                         |> (if local_run then Context.proof_map (Morphism.form transf)
                             else map_pot_lthy transf)
                     in
                       ctxt3
                     end)
                   gen_brules
                (* FIXME Fakten als Regeln auch einfuegen bevor die
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
                     fuer Head"  *)
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
              val (res, _) = metarec ctxt jid (pobj, iobjs)
              val _ =
                if debug then tracing ("metarec_tac: result is:  "^Display.string_of_thm ctxt res)
                else ()
            in rtac res i end
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
      val (res, _) = metarec ctxt jud (goal, [])
      val _ = tracing ("fconv_metarec: result for forwarding is   "^Display.string_of_thm ctxt res)
    in
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
  #> Context.theory_map (
       gen_add_nplace_synth_jud DisallowInconsis LthyTransfJud NONE 1 1 define_jud Data.define_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis NormalJud NONE 1 0 note_jud Data.note_headterm
       #> gen_add_nplace_synth_jud DisallowInconsis ProcJud NONE 1 1 concat_names_jud Data.concat_names_headterm)
  #> Context.theory_map (
       add_syn_proc concat_names_jud "concat_names_proc" concat_names_proc
       #> add_lthy_transform define_jud  "define" define_lthy_transf)


(* val _ =
  Outer_Syntax.local_theory "run_expl_frules" "run explicit frules"
  Keyword.thy_decl
  (Scan.succeed run_expl_frules) *)



end
