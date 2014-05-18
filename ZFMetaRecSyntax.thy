theory ZFMetaRecSyntax
imports Main
begin


lemma lam_eq_quant_eq:
    "((% x::'a::{}. PROP P(x)) == (% x. PROP Q(x))) ==> ((!! x. PROP P(x)) == (!! x. PROP Q(x)))"
  by simp

ML {* Thm.prop_of @{thm lam_eq_quant_eq} *}

lemma rem_unused_fix:
    "(!! x::'a::{}. PROP P) == (!! x. PROP Q(x)) ==> (PROP P == (!! x. PROP Q(x)))"
  by simp

lemma lam_eq_quant_eq_unused_fix:
    "(% x::'a::{}. PROP P) == (% x. PROP Q(x)) ==> (PROP P == (!! x. PROP Q(x)))"
  apply (rule rem_unused_fix)
  by (rule lam_eq_quant_eq)


definition
  matchout_const :: "'a::{} => 'a => prop" ("matchout _ _") where
  "matchout t1 t2 == (t1 == t2)"

lemma matchoutI: "matchout t t"
  by (simp add: matchout_const_def)



lemma meta_iff_reflection_T: "PROP P ==> (PROP P == Trueprop(True))"
  apply rule
  apply rule
  by assumption
  
ML {*
  val old_mksimps = Simplifier.global_simpset_of @{theory} |> Simplifier.mksimps
*}
setup {*
  Simplifier.map_simpset_global 
    (Simplifier.set_mksimps (fn ss => fn th =>
      let fun eq_trueI th = gen_all th RS @{thm meta_iff_reflection_T}
      in
        case try old_mksimps th of
          NONE => [eq_trueI th]
        | SOME [] => [eq_trueI th]
        | SOME res => res
      end))
*}

lemma output_matching_rewr1: "(PROP Joninputs(O1)) == (!! OV1. matchout O1 (OV1(fxs)) ==> PROP Joninputs(OV1(fxs)))"
  by (tactic {*
    FIRSTGOAL
    (Simplifier.asm_full_simp_tac
      (Raw_Simplifier.empty_ss addsimps [@{thm matchout_const_def}] |> Raw_Simplifier.context @{context})
    THEN'
      (rtac Drule.equal_intr_rule THEN_ALL_NEW Goal.norm_hhf_tac)
    THEN' (SUBPROOF (fn {prems, context, concl, ...} => 
     let
       val is_eq_th = can Logic.dest_equals o prop_of
       val eq_prems = prems |> filter is_eq_th
       val noneq_prem = prems |> filter_out is_eq_th |> the_single
       val noneq_prem_rewr = noneq_prem
         |> Conv.fconv_rule (Simplifier.rewrite
              (Raw_Simplifier.empty_ss addsimps eq_prems |> Raw_Simplifier.context context))
       val _ = tracing ("noneq_prem_rewr is: "^Display.string_of_thm context noneq_prem_rewr)
       val _ = tracing ("goal is: "^Syntax.string_of_term context (Thm.term_of concl))
     in FIRSTGOAL (rtac noneq_prem_rewr) end) @{context})
    THEN' (SUBPROOF (fn {prems, ...} => 
     FIRSTGOAL (rtac (hd prems) THEN_ALL_NEW (rtac @{thm Pure.reflexive}))) @{context})) *})


ML {* print_depth 20 *}
ML {*
  let val alpha = @{typ "'a"}
    val Z = Var(("Z", 0), @{typ "'a => 'a"}) $ Bound 0
    fun expl_app t1 t2 =
      let val (T1, T2) = fastype_of t1 |> Term.dest_funT
      in Free("explapp", (T1 --> T2) --> T1 --> T2) $ t1 $ t2 end
    fun normal_app t1 t2 = t1 $ t2
    val XY =
       normal_app
         (normal_app (Var(("X", 0), @{typ "'a => 'a => 'a"}))
            (@{term "a :: 'a => 'a"} $ Bound 0))
         (Var (("Y", 0), @{typ "'a => 'a"}) $ Bound 0)
    val f = @{term "f :: 'a => 'a"}
    val t1 = Abs("x", alpha, f $ Z)
    val t2 = Abs("x", alpha, f $ (f $ XY))
    val ct1 = cterm_of @{theory} t1
    val ct2 = cterm_of @{theory} t2
  in
  Unify.unifiers (@{theory}, Envir.empty 0, [(t1, t2)]) |> Seq.pull
  (* Pattern.unify @{theory} (t1, t2) (Envir.empty 0) *)
  end

*}


ML_file "item_net2.ML"
ML_file "impconv.ML"
ML_file "decomp_pattern.ML"
ML_file "struct_unify.ML"
ML_file "metarec.ML"


lemma conjunctionE : fixes P Q C assumes H: "PROP P &&& PROP Q" and cont: "(PROP P ==> PROP Q ==> PROP C)" shows "PROP C"
proof -
  note H1 = Pure.equal_elim_rule1[OF Pure.conjunction_def H]
  (* lame, weil Pure.meta_spec nichts bringt *)
  thm Pure.meta_spec[OF H1]
  show "PROP C"
  apply (tactic {* rtac (Thm.forall_elim (cterm_of @{theory} @{term "PROP C"}) @{thm H1}) 1 *})
  by (rule cont)
qed



definition
  try_const :: "prop => prop" ("try (_)"  [5] 10)
where
  "try_const(P) == P"

lemma tryI: "PROP P ==> try (PROP P)"
  unfolding try_const_def .

lemma try_test: "try (x : A) ==> x : A"
unfolding try_const_def .
ML {*
  @{thm try_const_def} |> prop_of;;
  @{thm try_test} |> prop_of
*}


definition
  brule_const :: "prop => prop" ("brule _" [5] 10)
where
  "brule_const(P) == P"

definition
  frule_const :: "prop => prop" ("frule _" [5] 10)
where
  "frule_const(P) == P"

definition
  exact_rule_const :: "prop => prop" ("exactrule _" [5] 10)
where
  "exact_rule_const(P) == P"



definition
  concat_names_const :: "'a::{} => 'b::{} => 'c::{} => prop" ("concat names _ _ = _" [10, 10, 10] 10)
where
  "concat_names_const(n1, n2, n') == Trueprop(True)"

lemma concat_namesI : "concat names n1 n2 = n'"
  unfolding concat_names_const_def by simp



definition
  define_const :: "'a::{} => 'b::{} => 'b :: {} => prop" ("define (_)/ := (_)/ giving (_)" 10)
where
  "define_const(name, rhs, lhs_output) == (lhs_output == rhs)"


lemma defineI: "lhs_output == rhs ==> define name := rhs giving lhs_output"
unfolding define_const_def by simp




definition
  note_const :: "prop => 'a::{} => prop" ("note (_)/ as (_)" [5,5] 10) 
where
  "note_const (P, name) == P"

lemma note_test: "Q ==> note P as bla ==> P"
unfolding note_const_def by simp





type_synonym
  proplist = i

definition
  prop_cons :: "prop => proplist => proplist"
where
  "prop_cons (p, ps) = 0"

definition
  prop_nil :: "proplist"
where
  "prop_nil = 0"




definition
  constraint_const :: "prop => prop" ("constraint _" [5] 10)
where
  "constraint_const(P) == P"

lemma constraintI: "PROP P ==> constraint (PROP P)"
  by (subst constraint_const_def)
lemma constraintD: "constraint (PROP P) ==> (PROP P)"
  by (simp add: constraint_const_def)

definition
  foconstraint_const :: "prop => prop" ("foconstraint _" [5] 10)
where
  "foconstraint_const(P) == P"

lemma foconstraintI: "PROP P ==> foconstraint (PROP P)"
  by (subst foconstraint_const_def)


definition
  primunify_const :: "'a :: {} => 'a => prop" ("primunify _ _")
where
  "primunify_const (t1,t2) == (t1 == t2)"

lemma primunifyI: "t1 == t2 ==> primunify t1 t2"
  by (simp add: primunify_const_def)

lemma primunify_rev_def: "(primunify t1 t2) == (t2 == t1)"
  apply rule
  by (simp add: primunify_const_def)+



definition
  fresh_unifvar_const :: "i => 'a :: {} => prop"
where
  "fresh_unifvar_const (u,x) == PROP Trueprop(True)"

abbreviation
  fresh_unifvar_abbrev :: "'a :: {} => prop" ("freshunifvar _") where
  "fresh_unifvar_abbrev(x) == PROP fresh_unifvar_const (0, x)"

lemma fresh_unifvarI: "freshunifvar x"
  by (simp add: fresh_unifvar_const_def)


definition
  dep_restr_const :: "'a::{} => 'b::{} => prop" ("deprestr _ _") where
  "dep_restr_const(t1, t2) == Trueprop(True)"

lemma deprestrI: "deprestr t1 t2"
  by (simp add: dep_restr_const_def)



definition
  expl_app :: "('a :: {} => 'b :: {}) => 'a => 'b" (infixr "$" 200) where
  "t1 $ t2 == t1(t2)"


definition
  protect_eta_redex_var where
  "protect_eta_redex_var(t) == t"












lemma gen_colljudI: "P == Trueprop(True) ==> PROP P" by simp

ML {*
  val max_polym = singleton (Variable.polymorphic @{context})

  structure MetaRec = MetaRec (
    val True = @{term "True"}
    val conjunctionE = @{thm conjunctionE}

    val try_const_name = @{const_name "try_const"}
    val tryI = @{thm tryI}
    val brule_const_name = @{const_name brule_const}
    val brule_const_def = @{thm brule_const_def}
    val frule_const_name = @{const_name frule_const}
    val frule_const_def = @{thm frule_const_def}
    val exact_rule_const_name = @{const_name exact_rule_const}
    val exact_rule_const_def = @{thm exact_rule_const_def}

    val constraint_headterm = @{term constraint_const} |> max_polym
    val constraintI = @{thm constraintI}
    val foconstraint_headterm = @{term foconstraint_const} |> max_polym
    val foconstraintI = @{thm foconstraintI}
    val fresh_unifvar_headterm = @{term fresh_unifvar_const} |> max_polym
    val fresh_unifvarI = @{thm fresh_unifvarI}
    val unify_headterm = @{term primunify_const} |> max_polym
    val unifyI = @{thm primunifyI}
    val deprestr_headterm = @{term "dep_restr_const"} |> max_polym
    val deprestrI = @{thm deprestrI}

    val note_headterm = @{term note_const} |> max_polym
    val note_const_def = @{thm note_const_def}
    val define_headterm = @{term define_const} |> max_polym
    val defineI = @{thm defineI}
    val concat_names_headterm = @{term concat_names_const} |> max_polym
    val concat_namesI = @{thm concat_namesI}
   
    val mk_Trueprop = FOLogic.mk_Trueprop
    val dest_Trueprop = FOLogic.dest_Trueprop

    (* just for application of collector judgements *)
    val unit_ty = @{typ "i"}
    val unit_elem = @{term "0"}

    val proplist_ty = @{typ proplist}
    fun mk_prop_cons t1 t2 = @{term prop_cons} $ t1 $ t2
    val prop_nil = @{term prop_nil}
    
    val gen_colljudI = @{thm gen_colljudI}

    val expl_app_const_name = @{const_name expl_app}
    val expl_app_def = @{thm expl_app_def}

    val matchout_headterm = @{term matchout_const} |> max_polym
    val matchout_def = @{thm matchout_const_def}
    val matchoutI = @{thm matchoutI}

    val prf_displayT = @{typ "i"}
    fun app_prf_displayt t1 t2 = @{term "ZF.apply"} $ t1 $ t2

    fun protect_eta_redex_var_const ty =
      Const(@{const_name protect_eta_redex_var},
        Sign.const_instance @{theory} (@{const_name protect_eta_redex_var}, [ty]))
    val protect_eta_redex_var_def = @{thm protect_eta_redex_var_def}
  );
*}



setup {* MetaRec.setup *}





ML {*

  fun zfy_list (t :: ts) = @{term Cons} $ t $ zfy_list ts
    | zfy_list [] = @{term Nil}

  fun metaize_list (Const (@{const_name Cons}, _) $ t $ ts) =
        t :: metaize_list ts
    | metaize_list (Const (@{const_name Nil}, _)) = []


  fun zfy_pair (t1, t2) = @{term ZF.Pair} $ t1 $ t2

  fun metaize_pair (Const (@{const_name ZF.Pair}, _) $ t1 $ t2) = (t1, t2)
    | metaize_pair t = raise TERM ("metaize_pair: not a pair", [t])

  fun mk_freshunifvar t =
    let val T = fastype_of t
    in
      Const(@{const_name fresh_unifvar_const}, @{typ i} --> T --> @{typ prop})
        $ @{term 0} $ t
    end
  fun dest_freshunifvar (Const (@{const_name fresh_unifvar_const}, _) $ _ $ t) = t
    | dest_freshunifvar t = raise TERM ("not a freshunifvar", [t])
*}

end
