
structure IsarIntegration = struct




fun assume_constraints ts ctxt =
  let
    val constraints0 = []
      |> fold (dest_constraintimps #> fst #> union (op =)) ts
    val constraints = constraints0 |> filter_out (can dest_freshunifvar)
    val unifvars = constraints0 |> map_filter (try dest_freshunifvar)
    val unconstrained_ts = ts |> map (dest_constraintimps #> snd)

    val (bound_assms0, ctxt2) = ctxt
      |> fold Variable.auto_fixes constraints
      (* |> Variable.add_fixes_direct (unifvars |> map
          (fn Free (x, _) => x
            | t => error ("assume_constraints: unification variable not a Free: "
              ^Syntax.string_of_term ctxt t))) *)
      |> Proof_Context.add_assms_i Assumption.assume_export
           (constraints |> map (fn C => ((Binding.empty, []), [(C, [])])))
    val assms0 = bound_assms0 |> maps (fn (_, assms_) => assms_)
    val assms = assms0 |> map (fn assm =>
      let
        val assmC = @{thm constraintI} OF [assm]
        val moding_rewr_net = ElabRuleProcessing.Data.get (Context.Proof ctxt)
          |> #moding_rewrites 
        val pot_rews = Item_Net.retrieve moding_rewr_net (prop_of assmC)
        val assmC_rewr = assmC |> Conv.fconv_rule (Conv.try_conv (Conv.rewrs_conv pot_rews))
      in
        assmC_rewr
      end)
    val ctxt3 = ctxt2 |> fold (MetaRec.add_assm true) assms
    (* val _ = tracing ("assume_constaints: assumed  "
      ^commas (map (Syntax.string_of_term ctxt3) constraints))
    val _ = tracing ("Assumption.all_prems_of: "
      ^commas (map (Display.string_of_thm ctxt3) (Assumption.all_prems_of ctxt3))) *)
  in
    (unconstrained_ts, ctxt3)
  end




(* adapted from expression.ML *)


fun check_expr thy instances = map (apfst (Locale.check thy)) instances;



(*Sanity check of instantiations and extraction of implicit parameters.
  The latter only occurs iff strict = false.
  Positional instantiations are extended to match full length of parameter list
  of instantiated locale.*)

fun parameters_of thy strict (expr, fixed) =
  let
    fun reject_dups message xs =
      (case duplicates (op =) xs of
        [] => ()
      | dups => error (message ^ commas dups));

    fun parm_eq ((p1: string, mx1: mixfix), (p2, mx2)) = p1 = p2 andalso
      (mx1 = mx2 orelse error ("Conflicting syntax for parameter " ^ quote p1 ^ " in expression"));

    fun params_loc loc = Locale.params_of thy loc |> map (apfst #1);
    fun params_inst (loc, (prfx, Expression.Positional insts)) =
          let
            val ps = params_loc loc;
            val d = length ps - length insts;
            val insts' =
              if d < 0 then error ("More arguments than parameters in instantiation of locale " ^
                quote (Locale.extern thy loc))
              else insts @ replicate d NONE;
            val ps' = (ps ~~ insts') |>
              map_filter (fn (p, NONE) => SOME p | (_, SOME _) => NONE);
          in (ps', (loc, (prfx, Expression.Positional insts'))) end
      | params_inst (loc, (prfx, Expression.Named insts)) =
          let
            val _ = reject_dups "Duplicate instantiation of the following parameter(s): "
              (map fst insts);
            val ps' = (insts, params_loc loc) |-> fold (fn (p, _) => fn ps =>
              if AList.defined (op =) ps p then AList.delete (op =) p ps
              else error (quote p ^ " not a parameter of instantiated expression"));
          in (ps', (loc, (prfx, Expression.Named insts))) end;
    fun params_expr is =
      let
        val (is', ps') = fold_map (fn i => fn ps =>
          let
            val (ps', i') = params_inst i;
            val ps'' = distinct parm_eq (ps @ ps');
          in (i', ps'') end) is []
      in (ps', is') end;

    val (implicit, expr') = params_expr expr;

    val implicit' = map #1 implicit;
    val fixed' = map (Variable.check_name o #1) fixed;
    val _ = reject_dups "Duplicate fixed parameter(s): " fixed';
    val implicit'' =
      if strict then []
      else
        let val _ = reject_dups
          "Parameter(s) declared simultaneously in expression and for clause: " (implicit' @ fixed')
        in map (fn (x, mx) => (Binding.name x, NONE, mx)) implicit end;

  in (expr', implicit'' @ fixed) end;


(** Read instantiation **)

(* Parse positional or named instantiation *)

local

fun prep_inst prep_term ctxt parms (Expression.Positional insts) =
      (insts ~~ parms) |> map
        (fn (NONE, p) => Free (p, dummyT)
          | (SOME t, _) => prep_term ctxt t)
  | prep_inst prep_term ctxt parms (Expression.Named insts) =
      parms |> map (fn p =>
        (case AList.lookup (op =) insts p of
          SOME t => prep_term ctxt t |
          NONE => Free (p, dummyT)));

in

fun parse_inst x = prep_inst Syntax.parse_term x;
fun make_inst x = prep_inst (K I) x;

end;



(* Instantiation morphism *)

fun inst_morph (parm_names, parm_types) ((prfx, mandatory), insts') ctxt =
  let
    (* parameters *)
    val type_parm_names = fold Term.add_tfreesT parm_types [] |> map fst;

    (* type inference and contexts *)
    val parm_types' = map (Type_Infer.paramify_vars o Logic.varifyT_global) parm_types;
    val type_parms = fold Term.add_tvarsT parm_types' [] |> map (Logic.mk_type o TVar);
    val arg = type_parms @ map2 Type.constraint parm_types' insts';
    val res = Syntax.check_terms ctxt arg;
    val ctxt' = ctxt |> fold Variable.auto_fixes res;

    (* instantiation *)
    val (type_parms'', res') = chop (length type_parms) res;
    val insts'' = (parm_names ~~ res') |> map_filter
      (fn inst as (x, Free (y, _)) => if x = y then NONE else SOME inst
        | inst => SOME inst);
    val instT = Symtab.make (type_parm_names ~~ map Logic.dest_type type_parms'');
    val inst = Symtab.make insts'';
  in
    (Element.inst_morphism (Proof_Context.theory_of ctxt) (instT, inst) $>
      Morphism.binding_morphism (Binding.prefix mandatory prfx), ctxt')
  end;




(*** Locale processing ***)

(** Parsing **)

fun parse_elem prep_typ prep_term ctxt =
  Element.map_ctxt
   {binding = I,
    typ = prep_typ ctxt,
    term = prep_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt),
    pattern = prep_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt),
    fact = I,
    attrib = I};

fun parse_concl prep_term ctxt concl =
  (map o map) (fn (t, ps) =>
    (prep_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) t,
      map (prep_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)) ps)) concl;




(** Simultaneous type inference: instantiations + elements + conclusion **)

local

fun mk_type T = (Logic.mk_type T, []);
fun mk_term t = (t, []);
fun mk_propp (p, pats) = (Type.constraint propT p, pats);

fun dest_type (T, []) = Logic.dest_type T;
fun dest_term (t, []) = t;
fun dest_propp (p, pats) = (p, pats);

fun extract_inst (_, (_, ts)) = map mk_term ts;
fun restore_inst ((l, (p, _)), cs) = (l, (p, map dest_term cs));

fun extract_elem (Element.Fixes fixes) = map (#2 #> the_list #> map mk_type) fixes
  | extract_elem (Element.Constrains csts) = map (#2 #> single #> map mk_type) csts
  | extract_elem (Element.Assumes asms) = map (#2 #> map mk_propp) asms
  | extract_elem (Element.Defines defs) = map (fn (_, (t, ps)) => [mk_propp (t, ps)]) defs
  | extract_elem (Element.Notes _) = [];

fun restore_elem (Element.Fixes fixes, css) =
      (fixes ~~ css) |> map (fn ((x, _, mx), cs) =>
        (x, cs |> map dest_type |> try hd, mx)) |> Element.Fixes
  | restore_elem (Element.Constrains csts, css) =
      (csts ~~ css) |> map (fn ((x, _), cs) =>
        (x, cs |> map dest_type |> hd)) |> Element.Constrains
  | restore_elem (Element.Assumes asms, css) =
      (asms ~~ css) |> map (fn ((b, _), cs) => (b, map dest_propp cs)) |> Element.Assumes
  | restore_elem (Element.Defines defs, css) =
      (defs ~~ css) |> map (fn ((b, _), [c]) => (b, dest_propp c)) |> Element.Defines
  | restore_elem (Element.Notes notes, _) = Element.Notes notes;

fun check cs context =
  let
    fun prep (_, pats) (ctxt, t :: ts) =
      let val ctxt' = Variable.auto_fixes t ctxt
      in
        ((t, Syntax.check_props (Proof_Context.set_mode Proof_Context.mode_pattern ctxt') pats),
          (ctxt', ts))
      end;
    val (cs', (context', _)) = fold_map prep cs
      (context, Syntax.check_terms
        (Proof_Context.set_mode Proof_Context.mode_schematic context) (map fst cs));
  in (cs', context') end;

in

fun check_autofix insts elems concl ctxt =
  let
    val inst_cs = map extract_inst insts;
    val elem_css = map extract_elem elems;
    val concl_cs = (map o map) mk_propp concl;
    (* Type inference *)
    val (inst_cs' :: css', ctxt') =
      (fold_burrow o fold_burrow) check (inst_cs :: elem_css @ [concl_cs]) ctxt;
    val (elem_css', [concl_cs']) = chop (length elem_css) css';
  in
    (map restore_inst (insts ~~ inst_cs'),
      map restore_elem (elems ~~ elem_css'),
      concl_cs', ctxt')
  end;

end;



(** Prepare locale elements **)

fun declare_elem prep_vars (Element.Fixes fixes) ctxt =
      let val (vars, _) = prep_vars fixes ctxt
      in ctxt |> Proof_Context.add_fixes vars |> snd end
  | declare_elem prep_vars (Element.Constrains csts) ctxt =
      ctxt |> prep_vars (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) csts) |> snd
  | declare_elem _ (Element.Assumes _) ctxt = ctxt
  | declare_elem _ (Element.Defines _) ctxt = ctxt
  | declare_elem _ (Element.Notes _) ctxt = ctxt;



(** Finish locale elements **)

fun finish_inst ctxt (loc, (prfx, inst)) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (parm_names, parm_types) = Locale.params_of thy loc |> map #1 |> split_list;
    val (morph, _) = inst_morph (parm_names, parm_types) (prfx, inst) ctxt;
  in (loc, morph) end;

fun finish_fixes (parms: (string * typ) list) = map (fn (binding, _, mx) =>
  let val x = Binding.name_of binding
  in (binding, AList.lookup (op =) parms x, mx) end);



local

fun closeup _ _ false elem = elem
  | closeup (outer_ctxt, ctxt) parms true elem =
      let
        (* FIXME consider closing in syntactic phase -- before type checking *)
        fun close_frees t =
          let
            val rev_frees =
              Term.fold_aterms (fn Free (x, T) =>
                if Variable.is_fixed outer_ctxt x orelse AList.defined (op =) parms x then I
                else insert (op =) (x, T) | _ => I) t [];
          in fold (Logic.all o Free) rev_frees t end;

        fun no_binds [] = []
          | no_binds _ = error "Illegal term bindings in context element";
      in
        (case elem of
          Element.Assumes asms => Element.Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, ps) => (close_frees t, no_binds ps)) propps)))
        | Element.Defines defs => Element.Defines (defs |> map (fn ((name, atts), (t, ps)) =>
            let val ((c, _), t') = Local_Defs.cert_def ctxt (close_frees t)
            in ((Thm.def_binding_optional (Binding.name c) name, atts), (t', no_binds ps)) end))
        | e => e)
      end;

in

fun finish_elem _ parms _ (Element.Fixes fixes) = Element.Fixes (finish_fixes parms fixes)
  | finish_elem _ _ _ (Element.Constrains _) = Element.Constrains []
  | finish_elem ctxts parms do_close (Element.Assumes asms) = closeup ctxts parms do_close (Element.Assumes asms)
  | finish_elem ctxts parms do_close (Element.Defines defs) = closeup ctxts parms do_close (Element.Defines defs)
  | finish_elem _ _ _ (Element.Notes facts) = Element.Notes facts;

end;



(** Process full context statement: instantiations + elements + conclusion **)

(* Interleave incremental parsing and type inference over entire parsed stretch. *)

local

fun prep_full_context_statement
    parse_typ parse_prop prep_vars_elem prep_inst prep_vars_inst prep_expr
    {strict, do_close, fixed_frees} raw_import init_body raw_elems raw_concl ctxt1 =
  let
    val thy = Proof_Context.theory_of ctxt1;

    val (raw_insts, fixed) = parameters_of thy strict (apfst (prep_expr thy) raw_import);

    fun prep_insts_cumulative (loc, (prfx, inst)) (i, insts, ctxt) =
      let
        val (parm_names, parm_types) = Locale.params_of thy loc |> map #1 |> split_list;
        val inst' = prep_inst ctxt parm_names inst;
        val parm_types' = parm_types
          |> map (Type_Infer.paramify_vars o
              Term.map_type_tvar (fn ((x, _), S) => TVar ((x, i), S)) o Logic.varifyT_global);
        val inst'' = map2 Type.constraint parm_types' inst';
        val insts' = insts @ [(loc, (prfx, inst''))];
        val (insts'', _, _, _) = check_autofix insts' [] [] ctxt;
        val inst''' = insts'' |> List.last |> snd |> snd;
        val (morph, _) = inst_morph (parm_names, parm_types) (prfx, inst''') ctxt;
        val ctxt'' = Locale.activate_declarations (loc, morph) ctxt;
      in (i + 1, insts', ctxt'') end;

    fun prep_elem insts raw_elem ctxt =
      let
        val ctxt' = ctxt
          |> Context_Position.set_visible false
          |> declare_elem prep_vars_elem raw_elem
          |> Context_Position.restore_visible ctxt;
        val elems' = parse_elem parse_typ parse_prop ctxt' raw_elem;
      in (elems', ctxt') end;

    fun prep_concl raw_concl (insts, elems, ctxt) =
      let
        val concl = parse_concl parse_prop ctxt raw_concl;
      in check_autofix insts elems concl ctxt end
    val fors = prep_vars_inst fixed ctxt1 |> fst;
    val ctxt2 = ctxt1 |> Proof_Context.add_fixes fors |> snd;
    val (_, insts', ctxt3) = fold prep_insts_cumulative raw_insts (0, [], ctxt2);

    val _ =
      if fixed_frees then ()
      else
        (case fold (fold (Variable.add_frees ctxt3) o snd o snd) insts' [] of
          [] => ()
        | frees => error ("Illegal free variables in expression: " ^
            commas_quote (map (Syntax.string_of_term ctxt3 o Free) (rev frees))));

    val ctxt4 = init_body ctxt3;
    val (elems, ctxt5) = fold_map (prep_elem insts') raw_elems ctxt4;
    val (insts, elems', concl, ctxt6) = prep_concl raw_concl (insts', elems, ctxt5);

    (* Retrieve parameter types *)
    val xs = fold (fn Element.Fixes fixes => (fn ps => ps @ map (Variable.check_name o #1) fixes)
      | _ => fn ps => ps) (Element.Fixes fors :: elems') [];
    val (Ts, ctxt7) = fold_map Proof_Context.inferred_param xs ctxt6;
    val parms = xs ~~ Ts;  (* params from expression and elements *)

    val fors' = finish_fixes parms fors;
    val fixed = map (fn (b, SOME T, mx) => ((Binding.name_of b, T), mx)) fors';
    val deps = map (finish_inst ctxt6) insts;
    val elems'' = map (finish_elem (ctxt1, ctxt6) parms do_close) elems';

  in ((fixed, deps, elems'', concl), (parms, ctxt7)) end

in

(* fun cert_full_context_statement x =
  prep_full_context_statement (K I) (K I) Proof_Context.cert_vars
  make_inst Proof_Context.cert_vars (K I) x;

fun cert_read_full_context_statement x =
  prep_full_context_statement Syntax.parse_typ Syntax.parse_prop Proof_Context.read_vars
  make_inst Proof_Context.cert_vars (K I) x; *)

fun read_full_context_statement x =
  prep_full_context_statement Syntax.parse_typ Syntax.parse_prop Proof_Context.read_vars
  parse_inst Proof_Context.read_vars check_expr x;

end;





local


fun prep_statement prep activate raw_elems raw_concl ctxt = (*changes*)
  let
    val ((_, _, elems, concl), _) =
      prep {strict = true, do_close = false, fixed_frees = true}
        ([], []) I raw_elems raw_concl ctxt;

    val ((assm_elems, nonassm_elems), recomb_elems) = elems
      |> MetaRec.filter_split (fn Element.Assumes _ => true | _ => false)
    val elem_css = assm_elems |> map (fn Element.Assumes assms_ => map snd assms_)
    val (css', ctxt2) = ctxt |>
      (* TODO(correctness): also process patterns?! but they are not even checked by check_autofix ... *)
      (fold_burrow o fold_burrow o MetaRec.fold_burrow_fst) assume_constraints (elem_css @ [concl])
    val (elem_css2, [concl2]) = chop (length elem_css) css'
    val assm_elems2 = (assm_elems ~~ elem_css2) |> map (fn (Element.Assumes asms, css) =>
      (asms ~~ css) |> map (fn ((b, _), cs) => (b, cs)) |> Element.Assumes)
    val elems2 = recomb_elems assm_elems2 nonassm_elems

    val (_, ctxt3) = ctxt2
      |> Proof_Context.set_stmt true
      |> fold_map activate elems2;
  in (concl2, ctxt3) end;

in

fun read_statement x = prep_statement read_full_context_statement Element.activate x;

end;

























(* adapted from specification.ML *)


local

fun prep_statement prep_att prep_stmt elems concl ctxt =
  (case concl of
    Element.Shows shows =>
      let
        val (propp, elems_ctxt) = prep_stmt elems (map snd shows) ctxt;
        val prems = Assumption.local_prems_of elems_ctxt ctxt;
        val stmt = Attrib.map_specs (map prep_att) (map fst shows ~~ propp);
        val goal_ctxt = (fold o fold) (Variable.auto_fixes o fst) propp elems_ctxt;
      in (([], prems, stmt, NONE), goal_ctxt) end
  | Element.Obtains obtains =>
      let
        val case_names = obtains |> map_index (fn (i, (b, _)) =>
          if Binding.is_empty b then string_of_int (i + 1) else Name_Space.base_name b);
        val constraints = obtains |> map (fn (_, (vars, _)) =>
          Element.Constrains
            (vars |> map_filter (fn (x, SOME T) => SOME (Variable.check_name x, T) | _ => NONE)));

        val raw_propp = obtains |> map (fn (_, (_, props)) => map (rpair []) props);
        val (propp, elems_ctxt) = prep_stmt (elems @ constraints) raw_propp ctxt;

        val thesis = Object_Logic.fixed_judgment (Proof_Context.theory_of ctxt) Auto_Bind.thesisN;

        fun assume_case ((name, (vars, _)), asms) ctxt' =
          let
            val bs = map fst vars;
            val xs = map Variable.check_name bs;
            val props = map fst asms;
            val (Ts, _) = ctxt'
              |> fold Variable.declare_term props
              |> fold_map Proof_Context.inferred_param xs;
            val params = map Free (xs ~~ Ts);
            val asm = fold_rev Logic.all params (Logic.list_implies (props, thesis));
            val _ = ctxt' |> Proof_Context.add_fixes (map (fn b => (b, NONE, NoSyn)) bs);
          in
            ctxt'
            |> Variable.auto_fixes asm
            |> Proof_Context.add_assms_i Assumption.assume_export
              [((name, [Context_Rules.intro_query NONE]), [(asm, [])])]
            |>> (fn [(_, [th])] => th)
          end;

        val more_atts = map (Attrib.internal o K)
          [Rule_Cases.consumes (~ (length obtains)), Rule_Cases.case_names case_names];
        val prems = Assumption.local_prems_of elems_ctxt ctxt;
        val stmt = [((Binding.empty, []), [(thesis, [])])];

        val (facts, goal_ctxt) = elems_ctxt
          |> (snd o Proof_Context.add_fixes [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)])
          |> fold_map assume_case (obtains ~~ propp)
          |-> (fn ths =>
            Proof_Context.note_thmss "" [((Binding.name Obtain.thatN, []), [(ths, [])])] #>
            #2 #> pair ths);
      in ((more_atts, prems, stmt, SOME facts), goal_ctxt) end);

structure Theorem_Hook = Generic_Data
(
  type T = ((bool -> Proof.state -> Proof.state) * stamp) list;
  val empty = [];
  val extend = I;
  fun merge data : T = Library.merge (eq_snd op =) data;
);

fun gen_theorem schematic prep_bundle prep_att prep_stmt
    kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int lthy =
  let
    val _ = Local_Theory.assert lthy;
    val thy = Proof_Context.theory_of lthy;

    val attrib = prep_att thy;

    val elems = raw_elems |> map (Element.map_ctxt_attrib attrib);
    val ((more_atts, prems, stmt, facts), goal_ctxt) = lthy
      |> Bundle.includes (map (prep_bundle lthy) raw_includes)
      |> prep_statement attrib prep_stmt elems raw_concl;
    val atts = more_atts @ map attrib raw_atts;

    fun after_qed' results goal_ctxt' =
      let
        val results' = burrow (map Goal.norm_result o Proof_Context.export goal_ctxt' lthy) results;
        val (res, lthy') =
          if forall (Attrib.is_empty_binding o fst) stmt then (map (pair "") results', lthy)
          else
            Local_Theory.notes_kind kind
              (map2 (fn (b, _) => fn ths => (b, [(ths, [])])) stmt results') lthy;
        val lthy'' =
          if Attrib.is_empty_binding (name, atts) then
            (Proof_Display.print_results Markup.empty int lthy' ((kind, ""), res); lthy')
          else
            let
              val ([(res_name, _)], lthy'') =
                Local_Theory.notes_kind kind [((name, atts), [(maps #2 res, [])])] lthy';
              val _ = Proof_Display.print_results Markup.empty int lthy' ((kind, res_name), res);
            in lthy'' end;
      in after_qed results' lthy'' end;
  in
    goal_ctxt
    |> Proof_Context.note_thmss "" [((Binding.name Auto_Bind.assmsN, []), [(prems, [])])]
    |> snd
    |> Proof.theorem before_qed after_qed' (map snd stmt)
    |> (case facts of NONE => I | SOME ths => Proof.refine_insert ths)
    |> tap (fn state => not schematic andalso Proof.schematic_goal state andalso
        error "Illegal schematic goal statement")
    |> fold_rev (fn (f, _) => f int) (Theorem_Hook.get (Context.Proof goal_ctxt))
  end;

in

(* val theorem = gen_theorem false (K I) (K I) Expression.cert_statement; *)
val theorem_cmd =
  gen_theorem false Bundle.check Attrib.intern_src read_statement(*changed*);

(* val schematic_theorem = gen_theorem true (K I) (K I) Expression.cert_statement; *)
val schematic_theorem_cmd =
  gen_theorem true Bundle.check Attrib.intern_src read_statement(*changed*);

fun add_theorem_hook f = Theorem_Hook.map (cons (f, stamp ()));

end;











(* adapted from proof_context.ML *)



(* propositions with patterns *)

local

fun simult_matches ctxt (t, pats) =
  (case Seq.pull (Unify.matchers (Proof_Context.theory_of ctxt) (map (rpair t) pats)) of
    NONE => error "Pattern match failed!"
  | SOME (env, _) => Vartab.fold (fn (v, (_, t)) => cons (v, t)) (Envir.term_env env) []);

fun prep_propp mode prep_pats prep_props args ctxt =(*changes*)
  let
    fun prep (_, raw_pats) (ctxt, prop :: props) =
      let val ctxt' = Variable.declare_term prop ctxt
      in ((prop, prep_pats (Proof_Context.set_mode Proof_Context.mode_pattern ctxt') raw_pats), (ctxt', props)) end;

    val raw_props = maps (map fst) args
    val (props, ctxt2) =
      ctxt |> Proof_Context.set_mode mode
      |> prep_props raw_props
      |> apsnd (Proof_Context.restore_mode ctxt)

    val (propp, (ctxt3, _)) = (fold_map o fold_map) prep args (ctxt2, props)
  in (propp, ctxt3) end;

fun gen_bind_propp mode parse_pat(*changed*) parse_prop raw_args ctxt =
  let
    val (args, ctxt') = prep_propp mode parse_pat(*changed*) parse_prop raw_args ctxt;
    val binds = flat (flat (map (map (simult_matches ctxt')) args));
    val propss = map (map #1) args;
    fun gen_binds ctxt0 = ctxt0
      |> Proof_Context.bind_terms (map #1 binds ~~
          map (SOME o Term.close_schematic_term) (Variable.export_terms ctxt' ctxt0 (map #2 binds)));
  in ((propss, gen_binds), ctxt' |> Proof_Context.bind_terms (map (apsnd SOME) binds)) end;

in

(* val read_propp           = prep_propp mode_default Syntax.read_props;
val cert_propp           = prep_propp mode_default (map o cert_prop);
val read_propp_schematic = prep_propp mode_schematic Syntax.read_props;
val cert_propp_schematic = prep_propp mode_schematic (map o cert_prop); *)

val bind_propp             = gen_bind_propp Proof_Context.mode_default Syntax.read_props
  (fn raw_props => fn ctxt => (*changes*)
    let
      val props = Syntax.read_props ctxt raw_props |> Syntax.check_terms ctxt
      val (props2, ctxt2) = assume_constraints props ctxt
      val _ = tracing ("bind_propp: elaborated terms: "^commas
        (props2 |> map (Syntax.string_of_term ctxt2)))
    in (props2, ctxt2) end)
(* val bind_propp_i           = gen_bind_propp mode_default (map o cert_prop);
val bind_propp_schematic   = gen_bind_propp mode_schematic Syntax.read_props;
val bind_propp_schematic_i = gen_bind_propp mode_schematic (map o cert_prop); *)

end;



local

fun gen_assms prepp exp args ctxt =
  let
    val cert = Thm.cterm_of (Proof_Context.theory_of ctxt);
    val ((propss, _), ctxt1) = prepp (map snd args) ctxt;
    val _ = Variable.warn_extra_tfrees ctxt ctxt1;
    val (premss, ctxt2) = fold_burrow (Assumption.add_assms exp o map cert) propss ctxt1;
  in
    ctxt2
    |> Proof_Context.auto_bind_facts (flat propss)
    |> Proof_Context.note_thmss "" (map fst args ~~ map (map (fn th => ([th], []))) premss)
  end;

in

val add_assms = gen_assms bind_propp;
(* val add_assms_i = gen_assms bind_propp_i; *)

end;















(* adapted from proof.ML *)

local

fun gen_assume asm prep_att exp args state =
  state
  |> Proof.assert_forward
  |> Proof.map_context_result (asm exp (Attrib.map_specs (map (prep_att (Proof.context_of state))) args))
  |> (fn (named_factss, state) => (named_factss, state |> Proof.set_facts (maps snd named_factss)))
       (* inlined  these_factss []  from proof.ML*)
  |> #2;

in

val assm_cmd = gen_assume add_assms(*changed*) Attrib.attribute_cmd;
val assume_cmd = assm_cmd Assumption.assume_export;
val presume_cmd = assm_cmd Assumption.presume_export;

end;


(* common goal statements *)

local

fun check_result msg sq =
  (case Seq.pull sq of
    NONE => error msg
  | SOME (s, _) => s);

fun gen_have prep_att prepp before_qed after_qed stmt int =
  Proof.local_goal (Proof_Display.print_results Markup.state int)
    prep_att prepp "have" before_qed after_qed stmt;

fun gen_show prep_att prepp before_qed after_qed stmt int state =
  let
    val testing = Unsynchronized.ref false;
    val rule = Unsynchronized.ref (NONE: thm option);
    fun fail_msg ctxt =
      "Local statement fails to refine any pending goal" ::
      (case ! rule of NONE => [] | SOME th => [Proof_Display.string_of_rule ctxt "Failed" th])
      |> cat_lines;

    fun print_results ctxt res =
      if ! testing then ()
      else Proof_Display.print_results Markup.state int ctxt res;
    fun print_rule ctxt th =
      if ! testing then rule := SOME th
      else if int then
        writeln (Markup.markup Markup.state (Proof_Display.string_of_rule ctxt "Successful" th))
      else ();
    val test_proof =
      Proof.local_skip_proof true
      |> Unsynchronized.setmp testing true
      |> Exn.interruptible_capture;

    fun after_qed' results =
      Proof.refine_goals print_rule (Proof.context_of state) (flat results)
      #> check_result "Failed to refine any pending goal"
      #> after_qed results;
  in
    state
    |> Proof.local_goal print_results prep_att prepp "show" before_qed after_qed' stmt
    |> int ? (fn goal_state =>
      (case test_proof (Proof.map_context (Context_Position.set_visible false) goal_state) of
        Exn.Res _ => goal_state
      | Exn.Exn exn => raise Exn.EXCEPTIONS ([exn, ERROR (fail_msg (Proof.context_of goal_state))])))
  end;

in

(*val have = gen_have (K I) Proof_Context.bind_propp_i;*)
val have_cmd = gen_have Attrib.attribute_cmd bind_propp(*changed*)
(*val show = gen_show (K I) Proof_Context.bind_propp_i;*)
val show_cmd = gen_show Attrib.attribute_cmd bind_propp(*changed*)

end;











(* adapted from isar_cmd.ML *)


fun goal opt_chain goal stmt int =
  opt_chain #> goal NONE (K I) stmt int;

val have = goal I have_cmd(*changed*);
val hence = goal Proof.chain have_cmd(*changed*);
val show = goal I show_cmd(*changed*);
val thus = goal Proof.chain show_cmd(*changed*);









(* adapted from isar_syn.ML *)


fun gen_theorem spec schematic kind =
  Outer_Syntax.local_theory_to_proof' spec
    ("state " ^ (if schematic then "schematic " ^ kind else kind))
    (Scan.optional (Parse_Spec.opt_thm_name ":" --|
      Scan.ahead (Parse_Spec.includes >> K "" ||
        Parse_Spec.locale_keyword || Parse_Spec.statement_keyword)) Attrib.empty_binding --
      Scan.optional Parse_Spec.includes [] --
      Parse_Spec.general_statement >> (fn ((a, includes), (elems, concl)) =>
        ((if schematic then schematic_theorem_cmd(*changed*) else theorem_cmd(*changed*))
          kind NONE (K I) a includes elems concl)));

val _ = gen_theorem @{command_spec "theorem"} false Thm.theoremK;
val _ = gen_theorem @{command_spec "lemma"} false Thm.lemmaK;
val _ = gen_theorem @{command_spec "corollary"} false Thm.corollaryK;
(* TODO: the schematic variants probably don't work anyway, because of
  the necessary unvarification during Syntax.check_term *)
val _ = gen_theorem @{command_spec "schematic_theorem"} true Thm.theoremK;
val _ = gen_theorem @{command_spec "schematic_lemma"} true Thm.lemmaK;
val _ = gen_theorem @{command_spec "schematic_corollary"} true Thm.corollaryK;




(* TODO(porting): in newer versions of Isabelle the redefinition of Isar commands
  is not usually possible, only if Outer_Syntax.batch_mode = Unsynchronized.ref true
  during the redefinition. Worst case in the future: use variants of the command names *)

val _ =
  Outer_Syntax.command @{command_spec "have"} "state local goal"
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o have(*changed*)));

val _ =
  Outer_Syntax.command @{command_spec "hence"} "old-style alias of \"then have\""
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o hence(*changed*)));

val _ =
  Outer_Syntax.command @{command_spec "show"}
    "state local goal, solving current obligation"
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o show(*changed*)));

val _ =
  Outer_Syntax.command @{command_spec "thus"} "old-style alias of  \"then show\""
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o thus(*changed*)));





val _ =
  Outer_Syntax.command @{command_spec "assume"} "assume propositions"
    (Parse_Spec.statement >> (Toplevel.print oo (Toplevel.proof o assume_cmd(*changed*))));





end
