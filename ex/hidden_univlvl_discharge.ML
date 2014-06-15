
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


  (* TODO(feature): more general discharge of all non-essential hidden universe levels:
       instantiation as for terminal ones, i.e.
           ?j := umax ({ ?i | exconstraint (?i u<= ?j) } Un { succ ?i | exconstaint (?i u< ?j)}),
       combined with short-cutting
       simplification of larger constraints:
         constraints( i1 u<= j,  i2 u<= j ) ==> i1 umax i2 u<= j
         constraints( i1 u< j,  i2 u< j ) ==> i1 umax i2 u< j
         constraint( i u< j ) ==> succ i u<= j 
         [| freshFOvar i'  ;  constraints( i u< i', i' u< j) |]  ==> succ i u< j 
       Note that the last constraint simp rule reintroduce essential hidden universe levels
       to avoid i+n algebraic universe level expressions.
       
       If we introduce an exconstraints primitive that searches for the set of
       all matching constraints we might even state the instantiation process of
       a hidden univlvl as a simp CHR:
          [| hidden i  ;
             exconstraints (?? j. i u<= j) (ALL j:J. i u<= j)  ;
             exconstraints (?? j. i u< j) (ALL j:J'. i u< j)  ;
             primunify i (constr_umax (J Un {succ j . j : J'}))  |] ==>
          i <: univlvl 
       But this is less efficient of course and what about u<=-SCCs?

       We could include the following simplification rules as well, to
       get rid of software complexity related to simpthm proof.
       But such an implementation would be less efficient due to search for univlvl occurence
       in umax term and metarec overhead:

         i <: univlvl  ==> succ i <: univlvl
         [|  i1 <: univlvl  ;  i2 <: univlvl  |] ==> umax i1 i2 <: univlvl

         i u<= i  (useful due to instantiation of hiddens in non-trivial u<=-sccs)
         i u< succ i
         synleq i1 (umax j1 j2) ==> i u<= umax j1 j2
         synless i1 (umax j1 j2) ==> i u< umax j1 j2
         
         where synleq, synless are defined by clauses
            synleq i (umax i j)
            synleq j (umax i j)
            synleq i j2 ==> synleq i (umax j1 j2)
            try (synleq i j1) ==> synleq i (umax j1 j2)

            synless i (umax (succ i) j)
            synless j (umax i (succ j))
            synless i j2 ==> synless i (umax j1 j2)
            try (synless i j1) ==> synless i (umax j1 j2)  *)
  (* NB: assumes that all universe levels (used in u<, u<= inequations) have  i <: univlvl  constraints in Cs
    (which is the usual situation after standard elaboration) *)
  fun calc_hidden_univlvl_discharge Cs ctxt =
    let
      val gctxt = Context.Proof ctxt
      val (concl, vars_in_concl) = case MetaRec.get_normed_concl_stats ctxt of
          SOME (MetaRec.ConclStats (concl, _, vars)) => (concl, vars)
        | NONE => error ("calc_hidden_univlvl_discharge: no concl stats available "
            ^"in linear ctxt in runstate")
      val delayed_unifs = MetaRec.get_delayed_unifs_in_run_state ctxt
      val nonhidden_vars_outside_Cs = vars_in_concl
        |> fold (Term.add_vars o Logic.mk_equals o fst) delayed_unifs

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
          error ("calc_hidden_univlvl_discharge: non-atomic universe level "
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
                 error ("calc_hidden_univlvl_discharge: missing universe level constraint for "
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
        orelse member (op =) nonhidden_vars_outside_Cs (Term.dest_Var i)
        orelse Cs |> exists (fn C =>
          not (is_some (dest_univlvl ctxt C)) andalso not (is_some (dest_univ_ieq C))
          andalso member (op =) (Term.add_vars C []) (Term.dest_Var i)))


      val ul_sccs_w_hidden = Term_Graph.strong_conn ul_graph |> map (fn ul_scc =>
          let
            val in_scc = member (op =) ul_scc
            val inbound_ieqs = ul_iqs |> filter (fn (_, (i', j')) => not (in_scc i') andalso in_scc j')
            val inner_ieqs = ul_iqs |> filter (fn (_, (i', j')) => in_scc i' andalso in_scc j')
            val _ = 
              if ul_scc |> exists (fn i =>
                   Term_Graph.get_node ul_graph i
                   |> exists (fn (compty, (j, _)) => compty = UnivLess andalso in_scc j))
              then
                error ("calc_hidden_univlvl_discharge: universe inconsistency in universe level scc\n"
                  ^cat_lines (inner_ieqs |> map (mk_univ_ieq #> Syntax.string_of_term ctxt)))
              else ()
            val hiddens = inter (op =) hidden_uls ul_scc
            val non_hiddens = ul_scc |> filter_out (member (op =) hiddens) 
          in
            ((non_hiddens, hiddens), (inbound_ieqs, inner_ieqs))
          end)
        |> filter_out (fn ((_, hiddens), _) => null hiddens)

      val _ = tracing ("univlvl sccs with hidden univlvls are\n"^
        cat_lines (ul_sccs_w_hidden |> map (fn ((non_hiddens, hiddens), (inbound_ieqs, inner_ieqs)) =>
            "  "
            ^commas (non_hiddens @ hiddens |> map (Syntax.string_of_term ctxt))
            ^"  with inner inequations  "
            ^commas (inner_ieqs |> map (mk_univ_ieq #> Syntax.string_of_term ctxt))
            ^"  with inbound inequations  "
            ^commas (inbound_ieqs |> map (mk_univ_ieq #> Syntax.string_of_term ctxt))
            (*^"  fst-distinctified to  "
            ^commas (inbound_ieqs |> distinct (eq_snd (eq_fst (op aconv))) |> map (mk_univ_ieq #> Syntax.string_of_term ctxt))*))))

      val cert = cterm_of (Proof_Context.theory_of ctxt)

      val (ctxt2, iq_ths) = (ctxt, []) |> fold (fn ((non_hiddens, hiddens), (inbound_ieqs, _)) => fn (ctxt_, ths) =>
          case non_hiddens of
            non_hidden :: _ =>
              let val ctxt_2 = ctxt_ |> Context.proof_map (MetaRec.map_env_in_run_state (
                 fold (fn hidden => curry Envir.update (Term.dest_Var hidden, non_hidden)) hiddens))
              in (ctxt_2, ths) end
          | [] =>
              let
                val norm = MetaRec.norm_with_env_in_run_state ctxt_
                (* NB: normalization necessary due to instantiations that happened already *)
                val inbound_ieqs' = inbound_ieqs |> map (fn (compty, (i, j)) => (compty, (norm i, norm j)))
                  |> distinct (eq_snd (eq_fst (op aconv)))

                (* val _ = tracing ("inbound_ieqs for "^Syntax.string_of_term ctxt_ i
                  ^" are "^commas (inbound_ieqs |> map (mk_univ_ieq #> Syntax.string_of_term ctxt_))) *)
                (* TODO(opt): keep track of uninstantiated univlvls that inst_t0 already bounds and if
                     the uninstantiated univlvls occurring in j' are covered by that, there is no need to
                     add j'' subterm to inst_t. *)
                fun inst_step_for (compty, (j', _)) =
                  let
                    val j''  = case compty of
                        UnivLeq => j'
                      | UnivLess => @{term "usucc"} $ j'
                    val th0_j = (case compty of
                        UnivLeq => @{thm uleq_base}
                      | UnivLess => @{thm uless_base})
                      |> Drule.instantiate' [] [SOME (cert j')]
                  in (j'', th0_j) end

                val (hidden_inst, iq_ths) =
                  case inbound_ieqs' of
                    [] => (@{term first_univlvl}, [])
                  | hd_inbound_ieq' :: tl_inbound_ieqs' => inst_step_for hd_inbound_ieq' ||> single
                      |> fold_rev (fn ieq as (compty, (j', _)) => fn (inst_t0, ths0) =>
                             let
                               val (j'', th0_j) = inst_step_for ieq
                               val [j'_ct, j''_ct, inst_t0_ct] = map cert [j', j'', inst_t0]
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
                                     | NONE => error ("calc_hidden_univlvl_discharge: "
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
                           tl_inbound_ieqs'

                (* val _ = tracing ("iq_ths for "^Syntax.string_of_term ctxt_ i^" are: "^
                  commas (iq_ths |> map (Display.string_of_thm ctxt_))) *)
                val _ = tracing ("instantiating hidden universe levels "^commas (hiddens |> map (Syntax.string_of_term ctxt_))^" := "^
                  Syntax.string_of_term ctxt_ hidden_inst)
                val ctxt_2 = ctxt_ |> Context.proof_map (MetaRec.map_env_in_run_state (
                  fold (fn hidden => curry Envir.update (Term.dest_Var hidden, hidden_inst)) hiddens))
                val env_2 = MetaRec.get_the_env_in_run_state ctxt_2
                val ths' = map (MetaRec.instnorm_thm_with_env ctxt_2 env_2) ths 
                  |> fold (insert Thm.eq_thm_prop) iq_ths 
              in
                (ctxt_2, ths')
              end)
        ul_sccs_w_hidden

      (* val _ = tracing ("inequality thms: "^cat_lines (iq_ths |> map (Display.string_of_thm ctxt2))) *)
   

      fun uninst_ul_check i = i aconv (MetaRec.norm_with_env_in_run_state ctxt2 i)
      val uninst_uls = uls |> filter uninst_ul_check
      val ul_instantiation = uls |> filter_out uninst_ul_check |> map (fn i =>
        (i, MetaRec.norm_with_env_in_run_state ctxt2 i))
      val inst_uls = map snd ul_instantiation |> distinct (op aconv)
      (* NB: only the inequations inbound to a scc with a hidden univlvl, which are of the form
           i  {u<, u<=}  umax (.. i ..),
         will be proven here. Absorption of instantiated ul_iqs inside a scc whose hidden univlvls
         became instantiated to a non-hidden univlvl in the scc require transitivity reasoning
         in general, so are left to CHRs. *)
      val inbnd_inst_ul_iqs = ul_sccs_w_hidden |> maps (fn (_, (inbound_ieqs, _)) => inbound_ieqs)
        |> map (mk_univ_ieq #> MetaRec.norm_with_env_in_run_state ctxt2)
        |> distinct (op aconv) (* NB: different hidden univlvls can get instantiated to same term *)
          (* NB: we don't use Variable.import/export because they are not exact inverses:
               export changes maxidx of unification vars, which makes exact matching
               of generated SimpCHR impossible *)
      val ([uninst_uls_fxd, inbnd_inst_ul_iqs_fxd, inst_uls_fxd, _], (((_, freeze_th), (_, thaw_th)), ctxt3)) = ctxt2
        |> fold_burrow
             (fn ts => MetaRec.exact_freeze_thaw ts #-> (fn (ts', fs) => fn ctxt_ => (ts', (fs, ctxt_))))
             ([uninst_uls, inbnd_inst_ul_iqs, inst_uls] @ [map Thm.prop_of iq_ths])
      val iq_ths_fxd = iq_ths |> map freeze_th

      (* val _ = tracing ("uninstantiated univlvls: "^commas (uninst_uls
        |> map (Syntax.string_of_term ctxt2)))
      val _ = tracing ("right-instantiated univlvls ineqs: "^commas (inbnd_inst_ul_iqs
        |> map (Syntax.string_of_term ctxt2)))
      val _ = tracing ("uninstantiated univlvls fixed: "^commas (uninst_uls_fxd
        |> map (Syntax.string_of_term ctxt2)))
      val _ = tracing ("fixed inequality thms: "^cat_lines (iq_ths_fxd
        |> map (Display.string_of_thm ctxt2)))  *)

      (* NB: after applying iq_ths, we have to discharge their premises that
         became instantiated to   (.. umax ..) <: univlvl *)
      val univlvl_ty_rls = [@{thm umax_univlvl_Cty}, @{thm first_univlvl_Cty}, @{thm usucc_univlvl_Cty}]

      val constr_univlvl_ty_assms = uninst_uls_fxd
        |> filter (fn i => inbnd_inst_ul_iqs_fxd |> exists (fn iq =>
             member (op =) (Term.add_frees iq []) (Term.dest_Free i)))
        |> map (fn i => @{term constraint_const} $ mk_univlvl i)
      val goal = 
        inbnd_inst_ul_iqs_fxd @ map mk_univlvl inst_uls_fxd
        |> Logic.mk_conjunction_balanced
      val simpth_opt =
        if null inst_uls then NONE
        else
          (* NB: we don't use Goal.prove to fix uninst_uls_fxd, because they would
               not be generalized to the original ones *)
          Goal.prove ctxt2 [] constr_univlvl_ty_assms goal
            (fn {prems=constr_univlvl_ty_prems, ...} =>
              print_tac "hidden univlvl discharge goal is"
              THEN REPEAT_DETERM_FIRST (
                (* (fn _ => print_tac "current goal is")
                THEN'*) match_tac ([Conjunction.conjunctionI] @ iq_ths_fxd @ univlvl_ty_rls
                  @ map (fn th => @{thm constraintD} OF [th]) constr_univlvl_ty_prems)))
          |> thaw_th |> SOME
      val _ = case simpth_opt of
          SOME simpth =>
            tracing ("calc_hidden_univlvl: simpth is "^
              Display.string_of_thm ctxt2 simpth)
        | NONE => ()
    in
      ((simpth_opt, uninst_uls, ul_instantiation), ctxt2)
    end

  fun hidden_univlvl_discharge_simproc Cs = MetaRec.cumul_timing "hidden_univlvl_discharge_proc"
    (fn ctxt => calc_hidden_univlvl_discharge Cs ctxt |> apfst #1)

  val setup = Context.theory_map (MetaRec.add_constraint_simproc true
    hidden_univlvl_discharge_simproc)

end
