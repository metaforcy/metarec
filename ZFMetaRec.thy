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
      val ruletrace = MetaRec.get_rule_trace ctxt |> map (fn f => f ())
      val _ = tracing (Syntax.string_of_term ctxt (Thm.term_of ct)^"\nrule trace:\n"
        ^cat_lines (map (Syntax.string_of_term ctxt) ruletrace))
      val th = Drule.instantiate' [SOME (Thm.ctyp_of_term ct)] [SOME ct] @{thm tracingI}
    in
      (th, [])
    end
*}

setup {*
  Context.theory_map (MetaRec.add_syn_proc "ZFMetaRec.tracing_jud" "tracing_proc" tracing_proc)
*}

definition
  fail_const where
  [MRjud 1 0]: "fail_const(x) == False"

abbreviation
  fail :: "o" where
  "fail == fail_const(0)"



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


  fun metaexs_to_freshvars t ctxt =
    case try dest_metaex t of
      SOME (x, T, body) => 
        let
          val (v, ctxt2) = MetaRec.genvar_on_run_state x T ctxt
          val body' = Term.subst_bound (v, body)
        in
          metaexs_to_freshvars body' ctxt2
        end
    | _ => (t, ctxt)
*}

ML {*

  structure ExConstraintMemoization = Proof_Data(
      (* ex_constraint results are indexed by their search pattern terms,
         which are converted to fully-dest_metaex'd *open* terms *)
      type T = (term * term) Net.net
      fun init _ = Net.empty
    );

  (* memoization table is reset on every linear context boundary,
     esp. after each constraint simplification phase *)
  fun ex_constraint_memo_linctxt_boundary_handler _ = ExConstraintMemoization.map (K Net.empty)

  (* TODO(feature): support for matching constraints from nontrivial local context
     -> lifting of unifvars in pat_vard over quantifications of C and matching against
        C's conclusion? Do we also have to spell these quantifications out in pat? *)
  (* TODO(feature): further filtering of matching constraints via metarec judgement *)
  fun ex_constraint_proc ctxt fail_cont (pat0, _, _) =
    let
      val thy = Proof_Context.theory_of ctxt
      val linctxt = MetaRec.get_linear_ctxt_in_run_state ctxt 
      val memo_net = ExConstraintMemoization.get linctxt

      val pat = MetaRec.norm_with_env_in_run_state ctxt pat0
      val pat_indexing = pat |> fully_dest_metaex |> Envir.eta_contract
      fun aconv_norm ctxt_ = MetaRec.aconv_norm (MetaRec.norm_with_env_in_run_state ctxt_)

      fun result pat_inst ctxt_ = 
        let
          val C_prf = MetaRec.assumption_prf pat_inst
          val (inst_intro, ctxt_2) = MetaRec.inst_match_on_freshthm_prf
            @{thm ex_constraintI} [NONE, SOME pat] ctxt_
          val (res_prf, ctxt_3) = MetaRec.mps_match_prf inst_intro [C_prf] ctxt_2
        in
          ((res_prf, [pat_inst]), SOME (ctxt_3 |> Context.Proof |> MetaRec.get_the_run_state))
        end
    in
      case Net.match_term memo_net pat_indexing |> filter (fn (pat2, _) => aconv_norm ctxt (pat2, pat)) of
        (_, pat_inst) :: _ => result pat_inst ctxt
      | [] =>
          let
            val constraints = MetaRec.get_constraints_in_run_state ctxt
            (* NB: we don't use Variable.import/export because they are not proper inverses due to
                 re-maxidx-ification of unification variable names *)
            val (([pat_fxd], ((freeze, _), (thaw, _))), ctxt2) = MetaRec.exact_freeze_thaw [pat] ctxt
            val (pat_fxd_vard, ctxt3) = ctxt2 |> metaexs_to_freshvars pat_fxd
          in
            case get_first (fn (C, _) => MetaRec.pattern_match_envctxt ctxt3 (pat_fxd_vard, freeze C)) constraints of
              SOME ctxt4 =>
                let
                  val pat_inst = MetaRec.norm_with_env_in_run_state ctxt4 pat_fxd_vard |> thaw

                  (* val _ = tracing ("ex_constraint_proc: found constraint "
                    ^Syntax.string_of_term ctxt4 pat_inst
                    ^" matching pattern "^Syntax.string_of_term ctxt4 pat) *)

                  val memo_net2 = memo_net |> Net.insert_term (eq_fst (aconv_norm ctxt4))
                    (pat_indexing, (pat, pat_inst))
                  val ctxt5 = ctxt4 |> MetaRec.map_linear_ctxt_in_run_state
                    (K (linctxt |> ExConstraintMemoization.map (K memo_net2)))
                in
                  result pat_inst ctxt5
                end
            | NONE => fail_cont ctxt3 ("no constraint matching "
                ^Syntax.string_of_term ctxt3 pat_fxd_vard^" found")
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
