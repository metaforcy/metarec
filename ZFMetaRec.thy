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


(* NB: if we use this shorthand-form, meta-existentials before P make no sense *)
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


  fun dest_conj_list_with_recomb P =
    case try Logic.dest_conjunction P of
      SOME (P1, P2) =>
        let
          val (Ps1, recomb1) = dest_conj_list_with_recomb P1
          val (Ps2, recomb2) = dest_conj_list_with_recomb P2
          val Ps1_len = length Ps1
          fun recomb f xs st =
            let 
              val (y, st2) = recomb1 f (take Ps1_len xs) st
              val (y2, st3) = recomb2 f (drop Ps1_len xs) st2
            in f (y, y2) st3 end
        in
          (Ps1 @ Ps2, recomb)
        end
    | NONE =>
        let
          fun recomb f [x] st = (x, st)
            | recomb _ _ _ = error ("dest_conj_list_with_recomb: recomb called on list with different length")
        in ([P], recomb) end
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
         fix_necessary_tab maps a metarec fix to the memoized pattern results that depend on it. *)
      type T = { memo_net: (term * term) Net.net,
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
                |> filter (fn (pat, _) => stale_pat aconv pat) |> map snd)
            in
              { memo_net = memo_net |> fold (fn stale_pat => fn net =>
                    del_pat stale_pat net
                    handle Net.DELETE => error ("ex_constraint_memo_linctxt_boundary_handler: internal error:"
                      ^" pattern "^Syntax.string_of_term linctxt stale_pat
                      ^" became stale now due to discharge of params "^commas disch_params
                      ^", but not found in memoization net\n"
                      ^(cat_lines (Net.content memo_net |> map (fn (pat, C) =>
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
  fun ex_constraint_proc ctxt fail_cont (pat0, _, [outpat0]) =
    let
      val _ =
        if can dest_metaex outpat0 then
          MetaRec.err_with_trace ctxt ("ex_constraint_proc: meta existential in output pattern "
            ^MetaRec.str_of_normed_term ctxt outpat0)
        else
          ()

      val ctxt = MetaRec.metarec_simp_instantiated_constraints ctxt

      val thy = Proof_Context.theory_of ctxt
      val linctxt = MetaRec.get_linear_ctxt_in_run_state ctxt 
      val { memo_net, ... } = ExConstraintMemoization.get linctxt

      (* NB: norming necessary in particular, because pattern_match_envctxt only norms object *)
      val pat = pat0 |> MetaRec.norm_with_env_in_run_state ctxt
      val assms = MetaRec.get_assms (Context.Proof ctxt) |> rev |> map (MetaRec.norm_with_env_in_run_state ctxt)
      val (local_frees, rel_assms) = MetaRec.rel_frees_and_assms_of (K ()) ctxt pat

      (* val _ = tracing (MetaRec.compose_err_from_trace ctxt
        ("\n\nex_constraint_proc on "^Syntax.string_of_term ctxt pat
        ^"\n  local_frees are "^commas (local_frees |> map (Syntax.string_of_term ctxt))
        ^"\n  rel_assms are "^commas (rel_assms |> map (Syntax.string_of_term ctxt))
        ^"\n  assms are "^commas (assms |> map (Syntax.string_of_term ctxt)))
        ^"\n\n") *)

      val pat_indexing = pat |> calc_pat_indexing
      val lift_pat_inst = curry Logic.list_implies rel_assms #> fold_rev Logic.all local_frees


      fun result pat_inst0 ctxt_ = 
        let
          (*val _ =
            if can Logic.dest_conjunction pat_inst0 then
              tracing ("ex_constraint_proc: in result proof construction for "
                ^MetaRec.str_of_normed_term ctxt_ (lift_pat_inst pat_inst0))
            else () *)

          val pat_inst = pat_inst0 |> MetaRec.norm_with_env_in_run_state ctxt_
          val (pat_inst_conjs, recomb) = dest_conj_list_with_recomb pat_inst

          val pat_inst_conj_prfs = pat_inst_conjs |> map (fn pat_inst_conjunct =>
            (* NB: here we expect the generated assumption to be identical to the assumption
               generated for the found constraint that matches the pattern *)
            (* TODO(refactor): this proof construction is shared exactly with MetaRec.constraint_gen_proc *)
            MetaRec.assumption_prf ctxt_ (lift_pat_inst pat_inst_conjunct)
            |> fold (MetaRec.allE_rev_prf ctxt_) local_frees
            |> fold (MetaRec.mp_rev_prf ctxt_ o MetaRec.assumption_prf ctxt_) rel_assms)

          val (pat_inst_prf, _) = () |> recomb (fn (prf1, prf2) => fn _ =>
              (MetaRec.mps_match_on_thm_prf ctxt_ @{thm Pure.conjunctionI} [prf1, prf2], ()))
            pat_inst_conj_prfs

          val res_prf = MetaRec.mps_match_w_inst_match_thm_prf ctxt_
            @{thm ex_constraintI} [NONE, SOME pat] [pat_inst_prf]

          (* val _ = tracing ("ex_constraint_proc: result proof construction done for "
            ^MetaRec.str_of_normed_term ctxt_3 (MetaRec.prop_of_proofp res_prf)) *)
        in
          ((res_prf, [pat_inst]), ctxt_ |> Context.Proof |> MetaRec.get_the_run_state |> SOME)
        end
    in
      case Net.match_term memo_net pat_indexing |> filter (fn (pat2, _) => aconv_norm ctxt (pat2, pat)) of
        (_, pat_inst) :: _ =>
          result pat_inst ctxt
      | [] =>
          let
            val constraints = MetaRec.get_active_constraints_in_run_state ctxt
            val (([pat_fxd], ((freeze, _), (thaw, _))), ctxt2) = MetaRec.exact_freeze_thaw [pat] ctxt

            (* NB: we don't use Variable.import/export because they are not proper inverses due to
                 re-maxidx-ification of unification variable names *)
            val (pat_fxd_liftvard, ctxt3) = ctxt2 |> metaexs_to_freshvars local_frees pat_fxd

           (* NB: since assumptions are constant in one context extension level,
               we only match lifted constraint conclusion.
               We don't have to care about the case of further instantiation of unification variables
               in particular, because their dependencies already have to be present. *)
            val pat_fxd_vard_lifted_conjs = pat_fxd_liftvard |> Logic.dest_conjunction_list 
              (* minor FIXME: also lift over rel_assms *)
              |> map (fold_rev Logic.all local_frees)

            (* minor FIXME: We should not focus (or even quantify) the variables in C that
               are not present in pat (and therefore are frozen in the same way),
               except if this is necessary to make it a pattern,
               but constraints should mostly be patterns. If they are in a position that
               can match against a metaex-variable of pat then we do not have to do
               anything and if they are not there can be no match. *)
            fun prep_match C =
              let
                (* NB: object is normed by pattern_match_envctxt, but freezing interferes *)
                val C' = C |> MetaRec.norm_with_env_in_run_state ctxt3 |> freeze
                val ((fixing, C''), ctxt_) = Variable.focus C' ctxt3
                val fix_frees = fixing |> map snd
                val concl = Logic.strip_assums_concl C''
                val rel_fixes = fix_frees |> inter (op =) (Term.add_frees concl [])
              in
                fold_rev (Logic.all o Free) rel_fixes concl
              end

            val loc_env0 = EnvDiff.empty 0
            val match_result_opt = SOME loc_env0 |> fold (fn pat_fxd_vard_lifted_conj => fn loc_env_opt =>
                case loc_env_opt of
                  NONE => NONE
                | SOME loc_env_ =>
                    get_first (fn (C, _) =>
                        (* NB: we have lifted the metaex-varified conjuncts of pat_fxd over local_frees because
                           in the presence of local_frees we hope for a matching constraint with the same
                           quantified local_frees in matching order. *)
                        MetaRec.pattern_match_envctxt (pat_fxd_vard_lifted_conj, prep_match C)
                          (loc_env_, ctxt3)
                          (*handle DecompPattern.Special _ => MetaRec.err_with_trace ctxt_ ("ex_constraint_proc:"
                            ^"shared variables in pattern and object term while matching")*))
                      constraints)
              pat_fxd_vard_lifted_conjs

            (* val _ = tracing ("ex_constraint_proc: searching a constraint matching lifted fixed pattern "
              ^Syntax.string_of_term ctxt3 pat_fxd_vard_lifted
              ^"\nin frozen constraints\n"
              ^commas (constraints |> map (fst #> MetaRec.norm_with_env_in_run_state ctxt3 #> freeze
                 #> Syntax.string_of_term ctxt3))
              ^"\nthat are prepared for matching as follows\n"
              ^commas (constraints |> map (fst #> prep_match false #> Syntax.string_of_term ctxt3))) *)
          in
            case match_result_opt of
              SOME loc_env2 =>
                let
                  val pat_inst = pat_fxd_liftvard |> EnvDiff.norm_term loc_env2 |> thaw
                  val C = lift_pat_inst pat_inst

                  (*val _ =
                    if not (can Logic.dest_conjunction pat_inst) then
                      ()
                    else
                    let 
                      val envdiff = MetaRec.get_the_env_in_run_state ctxt3 |> Envir.term_env |> Vartab.dest
                        |> subtract (pairself fst #> (op =))
                             (MetaRec.get_the_env_in_run_state ctxt3 |> Envir.term_env  |> Vartab.dest)
                    in 
                      tracing ("ex_constraint_proc: found constraint(s) "
                        ^Syntax.string_of_term ctxt3 pat_inst
                        ^"\nmatching pattern(s) "^Syntax.string_of_term ctxt3 pat
                        (*^"\n  (pat_fxd_liftvard = "^Syntax.string_of_term ctxt3 pat_fxd_liftvard
                        ^"\n  ,instantiated pat_fxd_liftvard = "^MetaRec.str_of_normed_term ctxt3 pat_fxd_liftvard
                        ^"\n  ,instantiated and thawed pat_fxd_liftvard = "
                          ^Syntax.string_of_term ctxt3
                            (MetaRec.norm_with_env_in_run_state ctxt3 pat_fxd_liftvard |> thaw)^")"
                        ^"\nactual preparation: "^commas ([pat_fxd_vard_lifted, prep_match C] |> map (Syntax.string_of_term ctxt3)) *)
                        ^"\nterm instantiation from match:\n  "
                        ^commas (envdiff |> map (fn (ixn, (T, t)) =>
                           Syntax.string_of_term ctxt3 (Var(ixn,T)) ^ " := "
                             ^MetaRec.str_of_normed_term ctxt3 t)))
                    end *)

                  val { fix_necessary_tab, constraint_to_pats, ...} = ExConstraintMemoization.get linctxt
                  val memo_net2 = memo_net |> Net.insert_term (eq_fst (aconv_norm ctxt3))
                    (pat_indexing, (pat, pat_inst))
                  val constraint_to_pats2 = constraint_to_pats
                    |> Net.insert_term_safe (eq_pair (aconv_norm ctxt3) (aconv_norm ctxt3))
                         (Envir.eta_contract C, (C, pat)) 
                  val fix_necessary_tab2 = fix_necessary_tab |> fold (fn fix =>
                      Symtab.cons_list (fst (Term.dest_Free fix), pat)) 
                    local_frees
                  val ctxt4 = ctxt3 |> MetaRec.map_linear_ctxt_in_run_state
                    (K (linctxt |> ExConstraintMemoization.map (K
                      {memo_net=memo_net2, constraint_to_pats=constraint_to_pats2,
                        fix_necessary_tab=fix_necessary_tab2})))
                in
                  result pat_inst ctxt4
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
