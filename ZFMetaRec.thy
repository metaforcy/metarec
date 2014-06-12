theory ZFMetaRec
imports ZFMetaRecSyntax "~~/src/ZF/Constructible/MetaExists"
begin

(* ML_file "zfmetarec.ML"

setup {* ZFMetaRec.setup *} *)



definition
  tracing where
  [MRjud 1 0]: "tracing(x) == True"

lemma tracingI: "tracing(x)"
  by (simp add: tracing_def)

ML {*
  fun tracing_proc ctxt (ct, _, _) =
    let
      val thy = Proof_Context.theory_of ctxt
      val _ = tracing (MetaRec.compose_err_from_trace ctxt
        ("\n\ntracing "^Syntax.string_of_term ctxt (Thm.term_of ct))
        ^"\n\n")
      val th = Drule.instantiate' [SOME (Thm.ctyp_of_term ct)] [SOME ct] @{thm tracingI}
    in
      (th, [])
    end
*}

setup {*
  Context.theory_map (MetaRec.add_syn_proc "ZFMetaRec.tracing_jud" "tracing_proc" tracing_proc)
*}

definition
  fail_const where (* FOL's false not general enough in all cases *)
  [MRjud 1 0]: "fail_const(x) == (!! P::prop. PROP P)"

abbreviation
  fail_abbrev :: "prop" ("fail") where
  "fail_abbrev == fail_const(0)"



definition
  intensionally_inequal :: "i => i => o" where
  [MRjud 2 0]: "intensionally_inequal(x, y) == True"

lemma [MR]: "intensionally_inequal(x, y)" by (simp add: intensionally_inequal_def)
lemma [MR]: "fail ==> intensionally_inequal(x, x)" by (simp add: intensionally_inequal_def)






definition
  ex_constraint_const :: "prop => prop => prop" ("exconstraint _ _") where
  [MRjud 1 1]: "ex_constraint_const(P, Q) == PROP Q"

lemma ex_constraintI: "PROP Q ==> exconstraint (PROP P) (PROP Q)"
  by (simp add: ex_constraint_const_def)


abbreviation
  ex_constraint_abbrev ("exconstraint _") where
  "ex_constraint_abbrev(P) == ex_constraint_const(P, P)"




definition
  no_ex_constraint_const :: "prop => prop" ("noexconstraint _") where
  [MRjud 1 0]: "no_ex_constraint_const(P) == Trueprop(True)"

lemma [MR]: "
  noexconstraint(P)"
  by (simp add: no_ex_constraint_const_def)


lemma [MR]: "
    [|  try (exconstraint P Q) ;  fail  |] ==>
  noexconstraint(P)"
  by (simp add: no_ex_constraint_const_def)


(* NB: we are using Larry's meta existential quantifier to signify matching variables *)
term "?? x. PROP P(x)"

ML {*
  fun dest_metaex (Const(@{const_name ex}, _) $ Abs(x, T, body)) = (x, T, body)
    | dest_metaex t = raise TERM("not a meta ex quantification", [t]) ;;

  fun fully_dest_metaex t = t
    |> perhaps_loop (try dest_metaex #> Option.map (fn (x, T, body) => body))
    |> the_default t


  fun metaexs_to_freshvars lift_fixes t ctxt =
    case try dest_metaex t of
      SOME (x, T, body) => 
        let
          val (v, ctxt2) = MetaRec.genvar_on_run_state x (map fastype_of lift_fixes ---> T) ctxt
          val body' = Term.subst_bound (list_comb (v, lift_fixes), body)
        in
          metaexs_to_freshvars lift_fixes body' ctxt2
        end
    | _ => (t, ctxt)
*}

ML {*
  
  fun aconv_norm ctxt_ = MetaRec.aconv_norm (MetaRec.norm_with_env_in_run_state ctxt_)


  (* TODO(opt!): use exact_net for memo_net and constraint_to_pats
     (instantiated pats should then continue to work memoized -> use aconv_norm insteaf aconv comparisons) *)
  structure ExConstraintMemoization = Proof_Data(
      (* ex_constraint results are indexed in memo_net by their search pattern terms,
           which are converted to fully-dest_metaex'd *open* terms.
         constraint_to_pats maps an active constraint to the patterns that have
           been matched against it (as (C, pat) entries in net that differ in pat).
         fix_necessary_tab says which memoized pattern results depend on a metarec fix. *)
      type T = { memo_net: (term * (term * term)) Net.net,
        constraint_to_pats: (term * term) Net.net,
        fix_necessary_tab: term list Symtab.table }
      fun init _ = { memo_net = Net.empty, constraint_to_pats = Net.empty,
        fix_necessary_tab = Symtab.empty }
    );


  (* NB: pat_indexing contains loose bounds for metaex quantified vars and refers
       to the concrete local_frees, i.e. no lifting here *)
  val calc_pat_indexing = fully_dest_metaex #> Envir.eta_contract

  (* NB: memoization for a constraint pattern is removed if a
     relevant part of the metarec context is discharged (does not matter for foconstraints).
     Memoization table is reset on every linear context boundary outside a metarec derivation,
     esp. after each constraint simplification phase *)
  fun ex_constraint_memo_linctxt_boundary_handler boundary ctxt linctxt =
    let
      fun del_pat pat memo_net = 
        Net.delete_term (fn (pat, (pat2, _)) => pat aconv pat2)
          (calc_pat_indexing pat, pat) memo_net
      fun del_C safe C constraint_to_pats = 
        (if safe then Net.delete_term_safe else Net.delete_term)
          (fn (C, (C2, _)) => aconv_norm ctxt (C, C2))
          (Envir.eta_contract (MetaRec.norm_with_env_in_run_state ctxt C), C) constraint_to_pats
      fun del_fixes_of pat fix_necessary_tab =
        let val fixes = Term.add_frees pat [] |> map fst |> filter (Symtab.defined fix_necessary_tab)
        in fix_necessary_tab |> fold (fn p => Symtab.remove_list (op aconv) (p, pat)) fixes end
    in
      linctxt |> ExConstraintMemoization.map (fn {memo_net, constraint_to_pats, fix_necessary_tab} =>
        case boundary of
          MetaRec.MetaRecCtxtDischargedBoundary disch_params =>
            let 
              val stale_pats = disch_params |> maps (Symtab.lookup fix_necessary_tab #> these)
              val stale_Cs = stale_pats |> maps (fn stale_pat =>
                Net.lookup memo_net (Net.key_of_term (calc_pat_indexing stale_pat))
                |> filter (fn (pat, _) => stale_pat aconv pat) |> map (snd #> snd))
            in
              { memo_net = memo_net |> fold (fn stale_pat => fn net =>
                    del_pat stale_pat net
                    handle Net.DELETE => error ("ex_constraint_memo_linctxt_boundary_handler: internal error:"
                      ^" pattern "^Syntax.string_of_term linctxt stale_pat
                      ^" became stale now due to discharge of params "^commas disch_params
                      ^", but not found in memoization net\n"
                      ^(cat_lines (Net.content memo_net |> map (fn (_, (pat, C)) =>
                          Syntax.string_of_term linctxt pat ^" -> "^Syntax.string_of_term linctxt C)))))
                  stale_pats,
                constraint_to_pats = constraint_to_pats |> fold (del_C false) stale_Cs
                  handle Net.DELETE => error ("ex_constraint_memo_linctxt_boundary_handler: internal error:"
                    ^" deletion of stale constraints "
                    ^commas (stale_Cs |> map (MetaRec.str_of_normed_term ctxt))^" failed"),
                fix_necessary_tab = fix_necessary_tab |> fold del_fixes_of stale_pats }
             end
        | MetaRec.MetaRecConstraintSimpBoundary simpd_C =>
            (* NB: we remove simplified constraints from memo_net, so that ex_constraint result function
               can expect a simplified constraint even in the memoized case *)
            let val stale_pats = Net.match_term constraint_to_pats simpd_C
              |> filter (fn (C, _) => aconv_norm ctxt (C, simpd_C)) |> map snd
            in
              { memo_net = memo_net |> fold del_pat stale_pats
                  handle Net.DELETE => error ("ex_constraint_memo_linctxt_boundary_handler"
                    ^" on MetaRecConstraintSimpBoundary "^MetaRec.str_of_normed_term ctxt simpd_C
                    ^": del_pat failed."
                    ^" stale_pats are "^commas (stale_pats |> map (MetaRec.str_of_normed_term ctxt))),
                constraint_to_pats = constraint_to_pats |> del_C true simpd_C,
                fix_necessary_tab = fix_necessary_tab |> fold del_fixes_of stale_pats }
            end
        | _ =>
            { memo_net = Net.empty, constraint_to_pats = Net.empty,
              fix_necessary_tab = Symtab.empty })
    end


  local
    fun mk_env (tyenv, tenv) = Envir.Envir { maxidx = 0, tyenv=tyenv, tenv=tenv }
    fun dest_env (Envir.Envir {tyenv, tenv, ...}) = (tyenv, tenv)
    fun map_env f = mk_env o f o dest_env
  in


  (* TODO(opt!!): manage constraints in net/item_net for fast constraint matching.
       (constraints cannot be stored with fixed unification variables in net because they
         can become instantiated in the meantime) *)
  (* TODO(feature):
       * further filtering of matching constraints via metarec judgement
       * multiple simultaneous left-to-right matchings by use of meta-conjunctions under meta-exists
         (akin to matching the heads of a CHR or frule) *)
  fun ex_constraint_proc ctxt fail_cont (pat0, _, _) =
    let
      val ctxt = MetaRec.metarec_simp_instantiated_constraints ctxt

      val thy = Proof_Context.theory_of ctxt
      val linctxt = MetaRec.get_linear_ctxt_in_run_state ctxt 
      val { memo_net, ... } = ExConstraintMemoization.get linctxt

      (* NB: norming necessary in particular, because pattern_match_envctxt only norms object *)
      val pat = MetaRec.norm_with_env_in_run_state ctxt pat0
      val assms = MetaRec.get_assms (Context.Proof ctxt) |> rev |> map (MetaRec.norm_with_env_in_run_state ctxt)
      val (local_frees, rel_assms) = MetaRec.rel_frees_and_assms_of (K ()) ctxt pat

      (* val _ = tracing (MetaRec.compose_err_from_trace ctxt
        ("\n\nex_constraint_proc on "^Syntax.string_of_term ctxt pat
        ^"\n  local_frees are "^commas (local_frees |> map (Syntax.string_of_term ctxt))
        ^"\n  rel_assms are "^commas (rel_assms |> map (Syntax.string_of_term ctxt))
        ^"\n  assms are "^commas (assms |> map (Syntax.string_of_term ctxt)))
        ^"\n\n") *)

      val pat_indexing = pat |> calc_pat_indexing


      fun result pat_inst0 C ctxt_ = 
        let
          (* val _ = tracing ("ex_constraint_proc: in result proof construction for "
            ^MetaRec.str_of_normed_term ctxt_ pat_inst0
            ^"\nfrom constraint "^MetaRec.str_of_normed_term ctxt_ C) *)

          val (pat_inst, C_normed) = (pat_inst0, C)
            |> pairself (MetaRec.norm_with_env_in_run_state ctxt_)
          val C_prf = MetaRec.assumption_prf C_normed

          val pat_inst_prf = 
            if C_normed aconv (pat_inst |> curry Logic.list_implies rel_assms |> fold_rev Logic.all local_frees) then
              (* TODO(refactor): this proof construction is shared exactly with MetaRec.constraint_gen_proc *)
              C_prf
              |> fold (MetaRec.allE_rev_prf ctxt_) local_frees
              |> fold (MetaRec.mp_rev_prf ctxt_ o MetaRec.assumption_prf) rel_assms
            else (* find rotation of parameters of constraint and assumption matching *)
              let
                (* NB: we use matching modulo eta and eta-contract because instantiations
                     of unification variables often lead to eta-redexes in constraint conclusions *)
                (* TODO(correctness): seems unnecessary with on-the-fly simplification of instantiated constraints
                   (which are then removed from memo_net) *)
                val C_norm_cv = Thm.eta_conversion

                val (C_normed_eta, pat_inst_eta) = (C_normed, pat_inst)
                  |> pairself (MetaRec.term_cv ctxt C_norm_cv)
                (* fixing unifvars in C that are not shared with pat *)
                (* NB: freezing wrt. pat is not enough for assumption matching,
                       because the constraint can further contain unification variables *)
                val (([C', pat_inst_eta_frozen], ((freeze, _), (thaw, _))), ctxt_2) = ctxt_
                  |> MetaRec.exact_freeze_thaw [C_normed_eta, pat_inst_eta]

                (* fixing and then varifying parameters of fixed constraint *)
                val ((fixing, C'_body), ctxt_3) = ctxt_2 |> Variable.focus C'
                val (C'_assms, C'_concl) = Logic.strip_horn C'_body
                val fix_frees = map (Free o snd) fixing
                val [[C'_concl_fixvard], C'_assms_fixvard, fix_vars] = [[C'_concl], C'_assms, fix_frees]
                  |> burrow (Variable.export_terms ctxt_3 ctxt_2)

                (* val _ = tracing ("ex_constraint_proc: after fixvaring."
                  ^"\n  fix_vars are "^commas (fix_vars |> map (Syntax.string_of_term ctxt_))
                  ^"\n  fixvard concl is "^Syntax.string_of_term ctxt_ C'_concl_fixvard
                  ^"\n  fixvard assms are "^commas (C'_assms_fixvard |> map (Syntax.string_of_term ctxt_))) *)

                val thy = Proof_Context.theory_of ctxt_

                (* matching local_frees against generalized focus frees. other unifvars are frozen *)
                val env = (Vartab.empty, Vartab.empty)
                  |> Pattern.match thy (C'_concl_fixvard, pat_inst_eta_frozen)
                  |> mk_env
                  handle Pattern.MATCH =>
                      MetaRec.err_with_trace ctxt_3 ("ex_constraint_proc: frozen pat_inst "
                        ^Syntax.string_of_term ctxt_3 pat_inst_eta_frozen
                        ^" does not match completely frozen constraint with varified parameters "
                        ^Syntax.string_of_term ctxt_3 C'_concl_fixvard)
                    | Pattern.Pattern =>
                      MetaRec.err_with_trace ctxt_3 "ex_constraint_proc: internal error: non-pattern in conclusion match"

                (* val _ = tracing ("ex_constraint_proc: after matching. env is\n  "
                  ^commas (env |> Envir.term_env |> Vartab.dest |> map (fn (ixn, (T, t)) =>
                    Syntax.string_of_term ctxt_ (Var (ixn, T)) ^" := "^Syntax.string_of_term ctxt_ t))) *)

                (* FIXME: use factual consequences as well. Seems necessary so that deep synthty derivations
                    have corresponding x elabto x : A facts available.
                    Problematic because non-ground facts are only availabe as rules, cf. fact constraint completion
                    in constraint simplification, so this kills performance. *)
                val frozen_assms = assms |> map freeze
                val open_C'_assms = C'_assms_fixvard |> map (Envir.norm_term env)
                  |> subtract (op aconv) frozen_assms

                (* val _ = tracing ("ex_constraint_proc: after calculation of open assumptions") *)

                (* minor FIXME: backtracking over previous match-choices *)
                val env2 = env |> fold (fn open_C'_assm => fn env_ =>
                    case get_first (fn rel_assm =>
                        try (map_env (Pattern.match thy (open_C'_assm, rel_assm))) env_)
                      frozen_assms
                    of
                      SOME env_2 => env_2
                    | NONE =>
                        MetaRec.err_with_trace ctxt_ ("ex_constraint_proc: found constraint "^Syntax.string_of_term ctxt_ C'
                        ^" matching "^Syntax.string_of_term ctxt_ pat
                        ^"\nbut the constraint assumptions "^Syntax.string_of_term ctxt_ open_C'_assm
                        ^"\nare has no match in assms "^commas (assms |> map (Syntax.string_of_term ctxt_))))
                  open_C'_assms

                (* val _ = tracing ("ex_constraint_proc: after assumption matching. env2 is "
                  ^commas (env2 |> Envir.term_env |> Vartab.dest |> map (fn (ixn, (T, t)) =>
                    Syntax.string_of_term ctxt_ (Var (ixn, T)) ^" := "^Syntax.string_of_term ctxt_ t))) *)

              in
                C_prf
                |> MetaRec.conv_prf ctxt_ C_norm_cv
                |> fold (MetaRec.allE_rev_prf ctxt_ o thaw o Envir.norm_term env2) fix_vars
                |> fold (MetaRec.mp_rev_prf ctxt_ o MetaRec.assumption_prf o thaw o Envir.norm_term env2)
                     C'_assms_fixvard
                |> MetaRec.unconvd_from_prf ctxt_ C_norm_cv pat_inst
              end

          val (inst_intro, ctxt_2) = MetaRec.inst_match_on_freshthm_prf
            @{thm ex_constraintI} [NONE, SOME pat] ctxt_
          val (res_prf, ctxt_3) = MetaRec.mps_match_prf inst_intro [pat_inst_prf] ctxt_2

          (* val _ = tracing ("ex_constraint_proc: result proof construction done for "
            ^MetaRec.str_of_normed_term ctxt_3 (MetaRec.prop_of_proofp res_prf)) *)
        in
          ((res_prf, [pat_inst]), ctxt_3 |> Context.Proof |> MetaRec.get_the_run_state |> SOME)
        end
    in
      case Net.match_term memo_net pat_indexing |> filter (fn (pat2, _) => aconv_norm ctxt (pat2, pat)) of
        (_, (pat_inst, C)) :: _ =>
          result pat_inst C ctxt
      | [] =>
          let
            val constraints = MetaRec.get_active_constraints_in_run_state ctxt
            val (([pat_fxd], ((freeze, _), (thaw, _))), ctxt2) = MetaRec.exact_freeze_thaw [pat] ctxt

            (* NB: we don't use Variable.import/export because they are not proper inverses due to
                 re-maxidx-ification of unification variable names *)
            val ((pat_fxd_liftvard, pat_fxd_vard), ctxt3) = ctxt2
              |> metaexs_to_freshvars local_frees pat_fxd
              ||>> metaexs_to_freshvars [] pat_fxd

           (* NB: since assumptions are constant in one context extension level,
               we only match lifted constraint conclusion.
               We don't have to care about the case of further instantiation of unification variables
               in particular, because their dependencies already have to be present. *)
            val pat_fxd_vard_lifted = pat_fxd_liftvard |> fold_rev Logic.all local_frees
            val [[pat_fxd_vard_fixvard], fixvars] = [[pat_fxd_vard], local_frees]
              |> burrow (map (Term_Subst.generalize ([], map (Term.dest_Free #> fst) local_frees)
                   (Term.maxidx_of_term pat_fxd_vard)))
            val fixvar_to_local_free = fixvars ~~ local_frees

            fun prep_match mod_param_rot C =
              let
                (* NB: object is normed by pattern_match_envctxt, but freezing interferes *)
                val C' = C |> MetaRec.norm_with_env_in_run_state ctxt3 |> freeze
                val ((fixing, C''), ctxt_) = Variable.focus C' ctxt3
                val fix_frees = fixing |> map snd
                val concl = Logic.strip_assums_concl C''
                val rel_fixes = fix_frees |> inter (op =) (Term.add_frees concl [])
              in
                if mod_param_rot then concl
                else fold_rev (Logic.all o Free) rel_fixes concl
              end

            (* val _ = tracing ("ex_constraint_proc: searching a constraint matching lifted fixed pattern "
              ^Syntax.string_of_term ctxt3 pat_fxd_vard_lifted
              ^"\nin frozen constraints\n"
              ^commas (constraints |> map (fst #> MetaRec.norm_with_env_in_run_state ctxt3 #> freeze
                 #> Syntax.string_of_term ctxt3))
              ^"\nthat are prepared for non-rotative matching as follows\n"
              ^commas (constraints |> map (fst #> prep_match false #> Syntax.string_of_term ctxt3))
              ^"\nand for rotative matching as follows\n"
              ^commas (constraints |> map (fst #> prep_match true #> Syntax.string_of_term ctxt3))) *)
          in
            (* FIXME: if pattern conclusion head is a parameter itself, matching modulo parameter rotation
              makes no sense. We remove matching modulo parameter rotation for now, as there is no use
              case anymore with on-the-fly contextual discharge of constraints. *)
            case
              (* TODO(opt): matching without local_free rotation first might not be performance gain after all,
                 because the real processing only starts in result function *)
              (* NB: in the mod_param_rot case, the metaex-quantified variables became unlifted unifvars
                 and the unifvars for the fixes are unlifted as well, so pat_fxd_vard_fixvard is a pattern *)
              get_first (fn ((C, _), mod_param_rot) =>
                  let
                    val pat' = if mod_param_rot then pat_fxd_vard_fixvard else pat_fxd_vard_lifted
                    val C' = prep_match mod_param_rot C
                  in
                    case MetaRec.pattern_match_envctxt ctxt3 (pat', C') of
                      NONE => NONE
                    | SOME ctxt4 =>
                        (*if fix_vars |> exists (fn x1 => fix_vars |> exists (fn x2 =>
                             x1 <> x2 andalso
                             ((x1, x2) |> pairself (MetaRec.norm_with_env_in_run_state ctxt4)
                             |> (op aconv))))
                        then (* discovered local_free "permutation" is not injective *)
                          NONE
                        else *)
                         let
                           (* NB: in mod_param_rot case we only want to ensure existence of match against
                             pattern modulo fixes permutation.
                             Actual permutation is calculated in result function.
                             This is why we norm pat_fxd_vard instead of pat_fxd_vard_fixvard. *)
                           val pat_inst = (if mod_param_rot then pat_fxd_vard else pat_fxd_liftvard)
                             |> MetaRec.norm_with_env_in_run_state ctxt4 |> thaw
                           val C_normed = C |> MetaRec.norm_with_env_in_run_state ctxt4

                           (*val _ = 
                             let 
                               val envdiff = MetaRec.get_the_env_in_run_state ctxt4 |> Envir.term_env |> Vartab.dest
                                 |> subtract (pairself fst #> (op =))
                                      (MetaRec.get_the_env_in_run_state ctxt3 |> Envir.term_env  |> Vartab.dest)
                             in 
                               tracing ("ex_constraint_proc: found constraint "
                                 ^Syntax.string_of_term ctxt4 pat_inst
                                 (*^"\n  (= "^Syntax.string_of_term ctxt4 C_normed^")" *)
                                 ^"\nmatching pattern "^Syntax.string_of_term ctxt4 pat
                                 (*^"\n  (pat_fxd_liftvard = "^Syntax.string_of_term ctxt4 pat_fxd_liftvard
                                 ^"\n  ,instantiated pat_fxd_liftvard = "^MetaRec.str_of_normed_term ctxt4 pat_fxd_liftvard
                                 ^"\n  ,instantiated and thawed pat_fxd_liftvard = "
                                   ^Syntax.string_of_term ctxt4
                                     (MetaRec.norm_with_env_in_run_state ctxt4 pat_fxd_liftvard |> thaw)^")"
                                 ^"\nactual preparation: "^commas ([pat', C'] |> map (Syntax.string_of_term ctxt4))
                                 ^"\nterm instantiation from match:\n  "
                                 ^commas (envdiff |> map (fn (ixn, (T, t)) =>
                                    Syntax.string_of_term ctxt4 (Var(ixn,T)) ^ " := "
                                      ^MetaRec.str_of_normed_term ctxt4 t)) *))
                             end *)
                         in
                           SOME ((pat_inst, C_normed), ctxt4)
                         end
                  end)
                (map (rpair false) constraints (* @ map (rpair true) constraints *))
            of
              SOME ((pat_inst, C), ctxt4) =>
                let
                  val { fix_necessary_tab, constraint_to_pats, ...} = ExConstraintMemoization.get linctxt
                  val memo_net2 = memo_net |> Net.insert_term (eq_fst (aconv_norm ctxt4))
                    (pat_indexing, (pat, (pat_inst, C)))
                  val constraint_to_pats2 = constraint_to_pats
                    |> Net.insert_term_safe (eq_pair (aconv_norm ctxt4) (aconv_norm ctxt4))
                      (Envir.eta_contract C, (C, pat)) 
                  val fix_necessary_tab2 = fix_necessary_tab |> fold (fn fix =>
                      Symtab.cons_list (fst (Term.dest_Free fix), pat)) 
                    local_frees
                  val ctxt5 = ctxt4 |> MetaRec.map_linear_ctxt_in_run_state
                    (K (linctxt |> ExConstraintMemoization.map (K
                      {memo_net=memo_net2, constraint_to_pats=constraint_to_pats2,
                        fix_necessary_tab=fix_necessary_tab2})))
                in
                  result pat_inst C ctxt5
                end
            | NONE =>
                let
                  val msg = ("ex_constraint_proc: no constraint matching "
                    ^Syntax.string_of_term ctxt3 pat^" found")
                  (* val _ = tracing msg *)
                in
                  fail_cont ctxt3 msg
                end
          end
    end

    end
*}

setup {*
  Context.theory_map (
    MetaRec.add_general_syn_proc "ZFMetaRec.ex_constraint_const_jud"
      "ex_constraint_proc" ex_constraint_proc
    #> MetaRec.add_linear_ctxt_boundary_handler ex_constraint_memo_linctxt_boundary_handler)
*}




end
