theory ZFMetaRec
imports ZFMetaRecSyntax "~~/src/ZF/Constructible/MetaExists"
begin

(* ML_file "zfmetarec.ML"

setup {* ZFMetaRec.setup *} *)




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
  fun dest_metaex (Const(@{const_name ex}, _) $ body) = body
    | dest_metaex t = raise TERM("not a meta ex", [t]) ;;


  fun metaexs_to_freshvars t ctxt =
    case try dest_metaex t of
      SOME (Abs(x, T, body)) => 
        let
          val (v, ctxt2) = MetaRec.genvar_on_run_state x T ctxt
          val body' = Term.subst_bound (v, body)
        in
          metaexs_to_freshvars body' ctxt2
        end
    | _ => (t, ctxt)
*}

ML {*
  (* TODO(feature): support for matching constraints from nontrivial local context
     -> lifting of unifvars in pat_vard over quantifications of C and matching against
        C's conclusion? Do we also have to spell these quantifications out in pat? *)
  fun ex_constraint_proc ctxt fail_cont (pat0, _, _) =
    let
      val thy = Proof_Context.theory_of ctxt
      val constraints = MetaRec.get_constraints_in_run_state ctxt
      val pat = MetaRec.norm_with_env_in_run_state ctxt pat0

      (* NB: we don't use Variable.import/export because they are not proper inverses due to
           re-maxidx-ification of unification variable names *)
      val (([pat_fxd], freeze, thaw_th), ctxt2) = MetaRec.exact_freeze_props_thaw_thms [pat] ctxt

      val (pat_fxd_vard, ctxt3) = ctxt2 |> metaexs_to_freshvars pat_fxd
    in
      case get_first (fn (C, _) => MetaRec.pattern_match_envctxt ctxt3 (pat_fxd_vard, freeze C)) constraints of
        SOME ctxt4 =>
          let
            val pat_inst = MetaRec.norm_with_env_in_run_state ctxt4 pat_fxd_vard
              |> cterm_of thy |> Drule.mk_term |> thaw_th |> Drule.dest_term |> Thm.term_of
            val C_prf = MetaRec.assumption_prf pat_inst
            
            val (inst_intro, ctxt5) = MetaRec.inst_match_on_freshthm_prf
              @{thm ex_constraintI} [NONE, SOME pat] ctxt4
            val (res_prf, ctxt6) = MetaRec.mps_match_prf inst_intro [C_prf] ctxt5
            (* val _ = tracing ("ex_constraint_proc: found constraint "^Syntax.string_of_term ctxt6 pat_inst
              ^" matching pattern "^Syntax.string_of_term ctxt6 pat) *)
          in
            ((res_prf, [pat_inst]), SOME (ctxt6 |> Context.Proof |> MetaRec.get_the_run_state))
          end
      | NONE => fail_cont ctxt3 ("no constraint matching "
          ^Syntax.string_of_term ctxt3 pat_fxd_vard^" found")
    end
*}

setup {*
  Context.theory_map (
    MetaRec.add_general_syn_proc "ZFMetaRec.ex_constraint_const_jud"
      "ex_constraint_proc" ex_constraint_proc)
*}




end
