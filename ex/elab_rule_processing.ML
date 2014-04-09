

structure ElabRuleProcessing =
struct


  structure Data = Generic_Data(
    type T = { constraint_moding_rewrites : thm Item_Net.T }
    val empty = {constraint_moding_rewrites = Item_Net.init Thm.eq_thm_prop
      (Thm.lhs_of #> Thm.term_of #> single)}
    val extend = I
    fun merge ({constraint_moding_rewrites}, {constraint_moding_rewrites = constraint_moding_rewrites2}) =
      {constraint_moding_rewrites = Item_Net.merge (constraint_moding_rewrites, constraint_moding_rewrites2)}
  );


  local
    fun dest_jud_name t =
      case MetaRec.decompose_judgement (Context.Proof @{context}) t of
        SOME (jud, _) => jud
      | NONE => error ("internal error in lookup of judgement name in  "
          ^Syntax.string_of_term @{context} t)
  in
    val elabjud_n = dest_jud_name @{prop "t elabto t' : A"}
    val elabsjud_n = dest_jud_name @{prop "elabs ts ts'_As"}
    val printsasjud_n = dest_jud_name @{prop "t' printsas t"}
    val synthtyjud_n = dest_jud_name @{prop "t synthty A"}
    val unify_jud_n = dest_jud_name @{prop "unify t t'"}
    val freshunifvar_jud_n = dest_jud_name @{prop "freshunifvar t"}
    val constraint_jud_n = dest_jud_name @{prop "constraint P"}
  end



  (* TODO(feature): bei Ueberlappungen der printsas Regeln warnen *)
  local
    val {judgements, ...} = MetaRec.get_current_ruledata (Context.Proof @{context})

    val mk_printsas = MetaRec.lookup_judgement_analyzer judgements printsasjud_n
      |> the |> #2

    fun dest_elab_jud t =
      case MetaRec.decompose_judgement (Context.Proof @{context}) t of
        SOME (jud, (pseudo_t, [], [elab_t, _])) =>
          if jud = elabjud_n then SOME (pseudo_t, elab_t)
          else NONE
      | _ => NONE
    fun opt_inv_elab_jud t : term option =
      dest_elab_jud t |> Option.map (fn (pseudo_t, elab_t) =>
        mk_printsas @{theory} (elab_t, [], [pseudo_t]))

    fun opt_inv_elab_hhf ctxt prop =
      let
        val (param_fresh_ns, ctxt2) = ctxt |> Variable.variant_fixes
          (map fst (Logic.strip_params prop))
        val (params, body) = MetaRec.strip_alls param_fresh_ns prop
        val (prems, concl) = Logic.strip_horn body
        val prems' = prems |> map_filter (opt_inv_elab_hhf ctxt2)
      in
        case opt_inv_elab_jud concl of
          SOME concl' =>
            let val prop' = Logic.list_implies (prems', concl')
              |> fold_rev Logic.all params
            in SOME prop' end
        | NONE => NONE
      end
  in


  fun derive_printsas_rule ctxt elab_rl =
     let val ctxt2 = ctxt |> Variable.declare_thm elab_rl
     in
       case opt_inv_elab_hhf ctxt2 (prop_of elab_rl) of
         SOME goal =>
           let
             val ss = simpset_of ctxt2 |> Simplifier.add_simp @{thm printsasjud_def}
             val th = Goal.prove ctxt2 [] [] goal (fn _ => Simplifier.simp_tac ss 1)
           in
             th
           end
       | _ => error ("not an elaboration rule:  "
         ^Display.string_of_thm ctxt2 elab_rl)
     end    

  end








  (* adapted from conv.ML *)
  fun fold_prems_conv 0 _ ct st = (Conv.all_conv ct, st)
    | fold_prems_conv n cv ct st =
        (case try Thm.dest_implies ct of
          NONE => (Conv.all_conv ct, st)
        | SOME (A, B) =>
            let
              val (A_th, st2) = cv A st
              val (B_th, st3) = fold_prems_conv (n - 1) cv B st2
            in 
              (Drule.imp_cong_rule A_th B_th, st3)
            end)

   fun fold_fconv_rule cv th st =
     let
       val (eq, st2) = cv (Thm.cprop_of th) st
     in
       if Thm.is_reflexive eq then (th, st2)
       else (Thm.equal_elim eq th, st2)
     end;



(* Inferenz von Syntheseregeln aus Elaborierungsregeln

   Vorgehen:
    *   t elabto t' : A   rewriten zu   t' synthty A
    * Unifikationen direkt durchfuehren,
      d.h. Unif wird durch matching gegen Judgement-Outputs ersetzt
    * wechselseitig voneinander abhaengig folgendes v.l.n.r in Premissen:
      * Groundness-tracking der Matching Variablen,
      * Constraints gemaess Constraint-Moding-Change-Rewrite-Rules umformen,
        die konditional anwendbar sind abhaengig vom Moding der
        Judgementargumente im Constraints. Z.B:
           constraint (t <: A), t ground ~~~>  t synthty A
           dargestellt wird das als Rewrite-Regel
              constraint (t <: A)  ==  t synthty A
           wobei wir die Bedingung der groundness von t aus
           dem Moding des Judgements synthty auf der RHS ableiten.
             t ist in Anwendungen dieser Regel fast immer ground,
           bis auf das k in Syntheseregel auf Funktionsraum
           also fast unconditional rewrite.
    * freshunifvar Premissen auf nicht-Variablen (nach Instantiierung mit Unifikator)
      und ground Matching-Variablen fallen weg

   NB: Syntheseregeln fuer Frees muessen bei der spaeteren Ausfuehrung
      der Typsynthese im Kontext vorhanden sein, ggf. unter Nutzung
      von Unifvar fuer Universenlevel
*)


  (* TODO(feature): also process unifications and constraints in local rule premises.
       but that should hardly matter in applications: rules are mostly 2-HHF *)
  (* TODO(correctness): type variables should also be considered in groundness check?
       of little practical significance? *)
  fun derive_synth_rule ctxt = MetaRec.protected_eta_redexes_thmmap ctxt (fn elab_rl =>
    let
      val gctxt = Context.Proof ctxt
      val thy = Proof_Context.theory_of ctxt
      val ss = Simplifier.context ctxt Raw_Simplifier.empty_ss
        addsimps [@{thm elab_to_synthty_rewr}]
      val synth_rl0 = elab_rl |> Simplifier.full_simplify ss
      (* val _ = tracing ("synth_rl0: "^Display.string_of_thm ctxt synth_rl0) *)

      val unifs = Thm.prems_of synth_rl0 |> map_filter (fn prem =>
        case MetaRec.decompose_judgement gctxt prem of
          SOME (jud, (pobj, iobjs, _)) =>
            if jud = unify_jud_n then SOME (pobj, hd iobjs) else NONE
        | NONE => NONE)
      (* val _ = tracing ("unifs: "^ commas (unifs
        |> map (fn tpair => Syntax.string_of_term ctxt (Logic.mk_equals tpair)))) *)
      val ctxt' = ctxt |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt)
        #> MetaRec.set_assms [])
      val env2 = MetaRec.get_the_env_in_run_state ctxt' |> fold (fn tpair => fn env_ =>
          case MetaRec.try_pat_unify ctxt' tpair env_ of
            SOME env_2 => env_2
          | NONE => error ("derive_synth_rule: failed to solve unification problem abstractly: "^
             Syntax.string_of_term ctxt' (Logic.mk_equals tpair)))
        unifs
      val ctxt2 = ctxt' |> Context.proof_map (MetaRec.map_env_in_run_state (K env2))

      (* val envdiff = env2 |> Envir.term_env |> Vartab.dest
        |> subtract (pairself fst #> (op =))
             (MetaRec.get_the_env_in_run_state ctxt' |> Envir.term_env |> Vartab.dest)
      val _ = tracing ("instantiation is:\n  "
        ^commas (envdiff |> map (fn (ixn, (T, t)) =>
           Syntax.string_of_term ctxt2 (Var(ixn,T)) ^ " := "
           ^ MetaRec.str_of_normed_term ctxt2 t))) *)

      
      val synth_rl1 = MetaRec.instnorm_thm_with_env ctxt2 env2 synth_rl0
      (* val _ = tracing ("synth_rl1: "^Display.string_of_thm ctxt2 synth_rl1) *)
      val ss2 = Simplifier.context ctxt2 Raw_Simplifier.empty_ss
        addsimps [@{thm refl_unif_mimp_rewr}]
      val synth_rl2 = synth_rl1 |> Simplifier.full_simplify ss2
      (* val _ = tracing ("synth_rl2: "^Display.string_of_thm ctxt2 synth_rl2) *)

      fun inout_vars_of_jud t = case MetaRec.decompose_judgement gctxt t of
          SOME (jud, (pobj, iobjs, oobjs)) =>
            if jud = freshunifvar_jud_n then ([], []) (* ignoring unification variable declarations *)
            else (fold Term.add_vars (pobj :: iobjs) [], fold Term.add_vars oobjs [])
        | NONE => error ("add_grnd_vars_in_jud: not a judgement "^Syntax.string_of_term ctxt2 t)
      fun add_in_vars_of_jud t = union (op =) (inout_vars_of_jud t |> fst)
      fun add_out_vars_of_jud t = union (op =) (inout_vars_of_jud t |> snd)
      fun add_grnd_vars_of_hhf_prem t = add_out_vars_of_jud (Logic.strip_assums_concl t)

      val grnd_vars0 = [] |> add_in_vars_of_jud (Thm.concl_of synth_rl2)
      fun ground grnd_vars t = subset (op =) (Term.add_vars t [], grnd_vars)
     

      fun constraint_cv ct grnd_vars = 
        case MetaRec.decompose_judgement gctxt (Thm.term_of ct) of
            SOME (jud, (_, _, _)) =>
              let
                val pot_rews = Item_Net.retrieve (Data.get gctxt
                  |> #constraint_moding_rewrites) (Thm.term_of ct)
                val _ = () (* tracing ("pot_rews: "^commas (pot_rews |> map (Display.string_of_thm ctxt2))) *)
              in
                ct |> Conv.try_conv (Conv.first_conv (pot_rews |> map (fn rewth => fn ct =>
                  let
                    val rewrd_constr_th = ct |> Conv.rewr_conv rewth
                  in
                    case MetaRec.decompose_judgement gctxt (Thm.rhs_of rewrd_constr_th |> Thm.term_of) of
                      SOME (_, (pobj, iobjs, _)) =>
                        if forall (ground grnd_vars) (pobj :: iobjs) then
                          let val _ = () (* tracing ("constraint moding rewrite: "
                            ^Display.string_of_thm ctxt2 rewrd_constr_th
                            ^"\n  ground inputs are "^commas (map (Syntax.string_of_term ctxt2) (pobj :: iobjs))) *)
                          in rewrd_constr_th end
                        else
                          let val _ = () (* tracing ("required groundness failed for constraint moding rewrite: "^
                            Display.string_of_thm ctxt2 rewrd_constr_th) *)
                          in ct |> Conv.no_conv end
                    | NONE => error ("constraint_cv: not a judgement after constraint rewriting "
                        ^Syntax.string_of_term ctxt2 (Thm.rhs_of rewth |> Thm.term_of))
                  end)))
                |> (fn rewrd_constr_th =>
                      (rewrd_constr_th,
                       grnd_vars |> add_grnd_vars_of_hhf_prem (Thm.rhs_of rewrd_constr_th |> Thm.term_of)))
              end
          | NONE => (Conv.all_conv ct, grnd_vars |> add_grnd_vars_of_hhf_prem (Thm.term_of ct))

      val (synth_rl3, grnd_vars) = (synth_rl2, grnd_vars0)
        |-> fold_fconv_rule (fold_prems_conv ~1 constraint_cv)
      val ground = ground grnd_vars


      val freshunifvar_decls = Thm.prems_of synth_rl3 |> map_filter (fn prem =>
        case MetaRec.decompose_judgement gctxt prem of
          SOME (jud, (_, _, oobjs)) =>
            if jud = freshunifvar_jud_n then SOME (hd oobjs) else NONE
        | NONE => NONE)
      val elim_freshunifvar_decls = freshunifvar_decls
        |> filter (fn uv => not (is_Var uv) orelse ground uv)
      (* val _ = tracing ("elim_freshunifvar_decls: "^commas (elim_freshunifvar_decls
        |> map (Syntax.string_of_term ctxt2))) *)
      val ss3 = Simplifier.context ctxt2 Raw_Simplifier.empty_ss
        addsimps (elim_freshunifvar_decls |> map (fn uv => @{thm freshunifvar_triv_rewr}
          |> Drule.instantiate' [SOME (ctyp_of thy (fastype_of uv))] [SOME (cterm_of thy uv)]))
        addsimps [@{thm true_mimp_rewr}]
      val synth_rl4 = synth_rl3 |> Simplifier.full_simplify ss3

      (* val _ = tracing ("derived synthesis rule\n  "^Display.string_of_thm ctxt2 synth_rl4) *)
    in
      synth_rl4
    end) 





  fun elabMR_decl_attr checked = Scan.lift (Scan.option Parse.int
    >> (fn prio_opt => fn (gctxt, elab_rl) =>
       let
         val prio = the_default 0 prio_opt
         val ctxt = Context.proof_of gctxt

         val printsas_rl = derive_printsas_rule ctxt elab_rl
         val synth_rl = derive_synth_rule ctxt elab_rl

         val _ =
           case gctxt of (* to avoid output for each local theory layer *)
             Context.Theory _ =>
               let val out = ("generated printing rule\n  "
                 ^Display.string_of_thm ctxt printsas_rl^"\n"
                 ^"generated synthesis rule\n  "
                 ^Display.string_of_thm ctxt synth_rl^"\n")
               in Output.writeln out; tracing out end
           | _ => ()

         val add_rule = if checked then MetaRec.add_rule else MetaRec.add_rule_unchecked
         val gctxt2 = gctxt |> fold (add_rule prio) [elab_rl, printsas_rl, synth_rl]
       in (SOME gctxt2, SOME elab_rl) end))

  fun constraint_moding_rewr_decl_attr x = x |> Scan.lift (Scan.succeed (fn (gctxt, th) =>
    (gctxt |> Data.map (fn {constraint_moding_rewrites} =>
      {constraint_moding_rewrites = constraint_moding_rewrites |> Item_Net.update th}) |> SOME, 
    SOME th)))


end
