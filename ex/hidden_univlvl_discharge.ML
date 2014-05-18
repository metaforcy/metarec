
structure HiddenUnivlvlDischarge =
struct


  datatype univlvl_comparison = UnivLess | UnivLeq


  local
    fun dest_jud_name t =
      case MetaRec.decompose_judgement (Context.Proof @{context}) t of
        SOME (jud, _) => jud
      | NONE => error ("internal error in lookup of judgement name in  "
          ^Syntax.string_of_term @{context} t)
  in
    val constraint_typing_jud_n = dest_jud_name @{prop "t <: A"}
    val univ_leq_jud_n = dest_jud_name @{prop "i u<= j"}
    val univ_less_jud_n = dest_jud_name @{prop "i u< j"}
  end

  fun dest_univlvl ctxt C = 
    case MetaRec.decompose_judgement (Context.Proof ctxt) C of
      SOME (jud, (t, [A], _)) =>
        if jud = constraint_typing_jud_n andalso A aconv @{term "univlvl"} then
          SOME t
        else
          NONE
    | _ => NONE
  fun mk_univlvl i =
    @{term constraint_typing} $ i $ @{term univlvl} |> FOLogic.mk_Trueprop


  (* TODO(feature): contract non-branching terminal u<=-chains (i.e. unify along them)
       after terminal hidden universelevels are gone
       (could be essential to avoid universe clutter from typing constraint merge rule. *)
  (* TODO(feature): contract branching u<=-chains with hidden intermediate levels:
        i1 u<= j1  i2 u<= j2  j1 u<= k  j2 u<= k ~~~>  j1, j2 := k    if j1, j2 hidden *)
  (* TODO(minor? feature): u<=-initiale hidden Universenlevel auch dischargen
       unter Instantiierung mit 0.
       Koennte wichtig sein wegen infunify von Typisierungs Constraints *)
  (* minor FIXME: ignore and discharge inflvl constraints.
      uncritical because inflvl universe levels are always non-hidden *)

  (* NB: assumes that all universe levels (used in u<, u<= inequations) have  i <: univlvl  constraints in Cs
    (which is the usual situation after standard elaboration) *)
  fun calc_hidden_terminal_univlvl_discharge Cs ctxt =
    let
      val gctxt = Context.Proof ctxt
      val (concl, vars_in_concl) = case MetaRec.get_normed_concl_stats ctxt of
          SOME (MetaRec.ConclStats (concl, _, vars)) => (concl, vars)
        | NONE => error ("calc_hidden_terminal_univlvl_discharge: no concl stats available "
          ^"in linear ctxt in runstate")

      fun dest_univ_ieq C =
        case MetaRec.decompose_judgement gctxt C of
          SOME (jud, (i, [j], _)) =>
            if jud = univ_leq_jud_n then
              SOME (UnivLeq, (i, j))
            else if jud = univ_less_jud_n then
              SOME (UnivLess, (i, j))
            else
              NONE
        | _ => NONE
      fun mk_univ_ieq (compty, (i, j)) = case compty of
          UnivLeq => @{term univ_leq} $ i $ j |> FOLogic.mk_Trueprop
        | UnivLess => @{term univ_less} $ i $ j |> FOLogic.mk_Trueprop

      val uls = Cs |> map_filter (dest_univlvl ctxt)
      val ul_iqs = Cs |> map_filter dest_univ_ieq

      val _ = uls |> map (fn i =>
        if can Term.dest_Var i orelse can Term.dest_Free i then
          ()
        else
          error ("calc_hidden_terminal_univlvl_discharge: non-atomic universe level "
            ^Syntax.string_of_term ctxt i))
      val _ = tracing ("univlvls are "^commas (uls |> map (Syntax.string_of_term ctxt)))
      val _ = tracing ("univlvl inequations are "^commas (ul_iqs
        |> map (mk_univ_ieq #> Syntax.string_of_term ctxt)))

      val ul_graph = Term_Graph.empty
        |> fold (fn i => Term_Graph.new_node (i, [])) uls
        |> fold (fn ul_iq as (_, (i, j)) => fn ul_graph =>
               ul_graph |> Term_Graph.add_edge (i, j)
               |> Term_Graph.map_node j (cons ul_iq)
               handle Term_Graph.UNDEF k =>
                 error ("calc_hidden_terminal_univlvl_discharge: missing universe level constraint for "
                   ^Syntax.string_of_term ctxt k^" used in inequality "
                   ^Syntax.string_of_term ctxt (mk_univ_ieq ul_iq)))
             ul_iqs

      val _ = tracing ("univlvl graph is\n"^
        cat_lines (Term_Graph.dest ul_graph |> map (fn ((i, prevs), succs) =>
          "  "^Syntax.string_of_term ctxt i^" -> "^commas (succs |> map (Syntax.string_of_term ctxt) )
            ^"   (eqs from: "^commas (prevs |> map (mk_univ_ieq #> Syntax.string_of_term ctxt))^")")))
      
      (* val _ = tracing ("concl is "^Syntax.string_of_term ctxt concl) *)

      val hidden_uls = uls |> filter_out (fn i =>
        not (can Term.dest_Var i)
        orelse member (op =) vars_in_concl (Term.dest_Var i)
        orelse Cs |> exists (fn C =>
          not (is_some (dest_univlvl ctxt C)) andalso not (is_some (dest_univ_ieq C))
          andalso member (op =) (Term.add_vars C []) (Term.dest_Var i)))

      val _ = tracing ("hidden univlvls are "^
        commas (hidden_uls |> map (Syntax.string_of_term ctxt)))

      (* NB: univlvls that are only smaller than hidden terminals are also
          considered as terminals (which makes instantiation an iterative effort)
          True terminals come last and terminals smaller than them come before. *) 
      val hidden_terminals = Term_Graph.maximals ul_graph |> inter (op =) hidden_uls
        |> MetaRec.list_fixpoint (fn hidden_terminals =>
             hidden_terminals |> fold (fn i => 
                 fold (fn j =>
                     if Term_Graph.immediate_succs ul_graph j = [i]
                       andalso member (op =) hidden_uls j 
                     then insert (op =) j
                     else I)
                   (Term_Graph.immediate_preds ul_graph i))
               hidden_terminals)

      val _ = tracing ("hidden terminal univlvls are "^
        commas (hidden_terminals |> map (Syntax.string_of_term ctxt))) 
        
      val cert = cterm_of (Proof_Context.theory_of ctxt)
      val (ctxt2, iq_ths) = (ctxt, []) |> fold (fn i => fn (ctxt_, ths) =>
          let
            val iqs = Term_Graph.get_node ul_graph i
            (* val _ = tracing ("iqs for "^Syntax.string_of_term ctxt_ i
              ^" are "^commas (iqs |> map (mk_univ_ieq #> Syntax.string_of_term ctxt_))) *)
            (* TODO(minor opt): avoid deepest (.. umax 0) subtree in i_inst, if  length iqs > 0 *)
            val (i_inst, i_ths) = (@{term "0"}, [])
              |> fold_rev (fn (compty, (j, _)) => fn (inst_t0, ths0) =>
                     let
                       val j' = MetaRec.norm_with_env_in_run_state ctxt_ j

                       val j''  = case compty of
                           UnivLeq => j'
                         | UnivLess => @{term "succ"} $ j'
                       val [j'_ct, j''_ct, inst_t0_ct] = map cert [j', j'', inst_t0]
                       val th0_j = (case compty of
                           UnivLeq => @{thm uleq_base}
                         | UnivLess => @{thm uless_base})
                         |> Drule.instantiate' [] [SOME j'_ct]
                       val umax1_th = case compty of
                           UnivLeq => @{thm uleq_umax1}
                         | UnivLess => @{thm uless_umax1}

                       (* TODO(refactor?): instead of manual instantiation, match
                           conclusions of th_j, ths against inst_t? Easy with Thm.match? *)
                       val th_j = (umax1_th |> Drule.instantiate' [] [SOME j'_ct, SOME j''_ct, SOME inst_t0_ct])
                         OF [th0_j]
                       (* val _ = tracing ("th_j for "^Syntax.string_of_term ctxt_ (@{term Pair} $ j $ i)
                         ^": "^Display.string_of_thm ctxt_ th_j) *)
                       val ths = ths0 |> map (fn th =>
                         let
                           val (umax2_th, (i0, j0)) = case dest_univ_ieq (Thm.concl_of th) of
                               SOME (UnivLeq, (i0, j0)) => (@{thm uleq_umax2}, (i0, j0))
                             | SOME (UnivLess, (i0, j0)) => (@{thm uless_umax2}, (i0, j0))
                             | NONE => error ("calc_hidden_terminal_univlvl_discharge: "
                                ^"expected univlvl inequality thm instead of "
                                ^Display.string_of_thm ctxt_ th)
                           val (i0_ct, j0_ct) = (i0, j0) |> pairself cert
                           val th' = (umax2_th |> Drule.instantiate' [] [SOME i0_ct, SOME j0_ct, SOME j''_ct])
                             OF [th]
                           (* val _ = tracing ("lifting:\n  "^Display.string_of_thm ctxt_ th
                            ^"\nto  "^Display.string_of_thm ctxt_ th') *)
                         in th' end)
                       val inst_t = @{term univ_max} $ j'' $ inst_t0
                     in
                       (inst_t, th_j :: ths)
                     end)
                   iqs
            (* val _ = tracing ("i_ths for "^Syntax.string_of_term ctxt i^" are: "^
              commas (i_ths |> map (Display.string_of_thm ctxt)))
            val _ = tracing ("i_inst for "^Syntax.string_of_term ctxt i^" ist: "^
              Syntax.string_of_term ctxt i_inst) *)
            val ctxt_2 = ctxt_ |> Context.proof_map (MetaRec.map_env_in_run_state
              (curry Envir.update (Term.dest_Var i, i_inst)))
            val env_2 = MetaRec.get_the_env_in_run_state ctxt_2
            val ths' = map (MetaRec.instnorm_thm_with_env ctxt_2 env_2) ths 
              |> fold (insert Thm.eq_thm_prop) i_ths
          in
            (ctxt_2, ths')
          end)
        hidden_terminals

      (* val _ = tracing ("inequality thms: "^cat_lines (iq_ths |> map (Display.string_of_thm ctxt2))) *)
   

      fun uninst_ul_check i = i aconv (MetaRec.norm_with_env_in_run_state ctxt2 i)
      val uninst_uls = uls |> filter uninst_ul_check
      val ul_instantiation = uls |> filter_out uninst_ul_check |> map (fn i =>
        (i, MetaRec.norm_with_env_in_run_state ctxt2 i))
      val inst_uls = map snd ul_instantiation |> distinct (op aconv)
      val inst_ul_iqs = ul_iqs |> filter_out (fn (_, (i, j)) =>
          uninst_ul_check i andalso uninst_ul_check j) 
        |> map (mk_univ_ieq #> MetaRec.norm_with_env_in_run_state ctxt2)
        |> distinct (op aconv) (* NB: hidden univlvls can get instantiated to same term *)
          (* NB: we don't use Variable.import/export because they are not exact inverses:
               export changes maxidx of unification vars, which makes exact matching
               of generated SimpCHR impossible *)
      val ([uninst_uls_fxd, inst_ul_iqs_fxd, inst_uls_fxd, _], (((_, freeze_th), (_, thaw_th)), ctxt3)) = ctxt2
        |> fold_burrow
             (fn ts => MetaRec.exact_freeze_thaw ts #-> (fn (ts', fs) => fn ctxt_ => (ts', (fs, ctxt_))))
             ([uninst_uls, inst_ul_iqs, inst_uls] @ [map Thm.prop_of iq_ths])
      val iq_ths_fxd = iq_ths |> map freeze_th

      (* val _ = tracing ("uninstantiated univlvls: "^commas (uninst_uls
        |> map (Syntax.string_of_term ctxt2)))
      val _ = tracing ("instantiated univlvls ineqs: "^commas (inst_ul_iqs
        |> map (Syntax.string_of_term ctxt2)))
      val _ = tracing ("uninstantiated univlvls fixed: "^commas (uninst_uls_fxd
        |> map (Syntax.string_of_term ctxt2)))
      val _ = tracing ("fixed inequality thms: "^cat_lines (iq_ths_fxd
        |> map (Display.string_of_thm ctxt2)))  *)

      (* NB: after applying iq_ths, we have to discharge their premises that
         became instantiated to   (.. umax ..) <: univlvl *)
      val univlvl_ty_rls = [@{thm umax_univlvl_ty}, @{thm zero_univlvl_ty}, @{thm succ_univlvl_ty}]

      val constr_univlvl_ty_assms = uninst_uls_fxd
        |> filter (fn i => inst_ul_iqs_fxd |> exists (fn iq =>
             member (op =) (Term.add_frees iq []) (Term.dest_Free i)))
        |> map (fn i => @{term constraint_const} $ mk_univlvl i)
      val goal = 
        inst_ul_iqs_fxd @ map mk_univlvl inst_uls_fxd
        |> Logic.mk_conjunction_balanced
      val simpth_opt =
        if null inst_uls then NONE
        else
          (* NB: we don't use Goal.prove to fix uninst_uls_fxd, because they would
               not be generalized to the original ones *)
          Goal.prove ctxt2 [] constr_univlvl_ty_assms goal
            (fn {prems=constr_univlvl_ty_prems, ...} =>
              print_tac "goal is"
              THEN REPEAT_DETERM_FIRST (
                (* (fn _ => print_tac "current goal is")
                THEN'*) match_tac ([Conjunction.conjunctionI] @ iq_ths_fxd @ univlvl_ty_rls
                  @ map (fn th => @{thm constraintD} OF [th]) constr_univlvl_ty_prems)))
          |> thaw_th |> SOME
    in
      ((simpth_opt, uninst_uls, ul_instantiation), ctxt2)
    end

  fun hidden_terminal_univlvl_discharge_simproc Cs = MetaRec.cumul_timing "hidden_univlvl_discharge_proc"
    (fn ctxt => calc_hidden_terminal_univlvl_discharge Cs ctxt |> apfst #1)

  val setup = Context.theory_map (MetaRec.add_constraint_simproc true
    hidden_terminal_univlvl_discharge_simproc)

end
