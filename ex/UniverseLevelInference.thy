theory UniverseLevelInference
imports "../ZFMetaRec"
begin




ML {*
  val B_x = @{cpat "% z::i. ?B(x::i, z, f(z)) :: i"} |> Thm.term_of
  val prod = @{cpat "% z::i. PROD x:?C(f(z)). ?D(x, z)"} |> Thm.term_of
  val env' = 
    StructUnify.unify @{theory} (B_x, prod) (Envir.empty 1)
  val B_x' = Envir.norm_term env' B_x |> cterm_of @{theory}
  val prod' = Envir.norm_term env' prod |> cterm_of @{theory}
*}

ML {*
  val A1 = @{cpat "?B(x::i)"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val env' = 
    StructUnify.unify @{theory} (A1, A2) (Envir.empty 1)
  val A1' = Envir.norm_term env' A1 |> cterm_of @{theory}
  val A2' = Envir.norm_term env' A2|> cterm_of @{theory}
*}

ML {*
  val A1 = @{cpat "?B(x::i, x) :: i"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val env = Envir.empty 1
  val env2 = StructUnify.unify @{theory} (A1, A2) env
  val A1' = Envir.norm_term env2 A1 |> cterm_of @{theory}
*}


ML {*
  val A1 = @{cpat "?B(x::i)"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val B1 = @{cpat "?D(x :: i) :: i"} |> Thm.term_of
  val B2 = @{cpat "PROD x:?E. ?F(x)"} |> Thm.term_of
  val env = Envir.empty 1
  val env2 = StructUnify.unify @{theory} (A1, A2) env
  val A2' = Envir.norm_term env2 A2 |> cterm_of @{theory}
  val B1' = Envir.norm_term env2 B1 |> cterm_of @{theory}
  val B2' = Envir.norm_term env2 B2 |> cterm_of @{theory}
  val env3 = StructUnify.unify @{theory} (B1, B2) env2
  val A2'' = Envir.norm_term env3 A2 |> cterm_of @{theory}
*}


(* this is an improper axiomatization of a universe hierarchy:
   we just state closure under the things we need instead of closure under
   the primitive set theoretic constructions (union, replacement etc.) *)
axiomatization
  guniv :: "i => i" ("guniv _" [100] 100)
where
  nat_in_guniv: "i : nat ==> nat : guniv i"  and
  trans_guniv: "i : nat ==> x : A ==> A : guniv i ==> x : guniv i" and
  list_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==> List_ZF.list(A) : guniv i" and
  prod_in_guniv:
    "[|  i : nat  ;  A : guniv i  ;  (!! x. x : A ==> B(x) : guniv i)  |]
     ==> (PROD x:A. B(x)) : guniv i" and
  guniv_in_guniv: "[|  i : nat  ;  j : nat  ;  i < j |] ==> guniv i : guniv j"



lemma guniv_cumul: "[|  i : nat  ;  j : nat  ;  i le j ;  x : guniv i |] ==> x : guniv j"
  apply (cases "i = j") apply simp
  apply (rule trans_guniv[of j x "guniv i"], assumption+)
  apply (rule guniv_in_guniv, assumption+)
  apply (rule Ord_linear_lt[of i j], simp+)
  by (simp add: le_iff)

lemma natelem_in_guniv: "i : nat ==> x : nat ==> x : guniv i"
  apply (rule trans_guniv) apply assumption+ by (rule nat_in_guniv)

(* Pseudo terms that will be elaborated.
   Note that we don't introduce a seperate type to allow the
   reuse of free variables in the pseudoterm when elaborating. *)

definition
  ptuniv :: "i" ("univ") where
  "ptuniv == 0"
definition
  hole :: "i" ("?") where
  "hole == 0"
definition (* $ is taken by ZFMetaRecSyntax, @ is taken by List_ZF *)
  ptapp :: "i => i => i" (infixl "#" 100) where
  "ptapp(f,x) == 0"
definition
  ptlambda :: "(i => i) => i" where
  "ptlambda(b) == 0"
definition
  ptprod :: "i => (i => i) => i" where
  "ptprod(A,F) == 0"

syntax
  "_fun" :: "[pttrn, i] => i"  ("(2fun _./ _)" 10)  (* lam already taken for proper ZF abstractions *)
  "_PI"     :: "[pttrn, i, i] => i"  ("(3PI _:_./ _)" 10)

translations
  "fun x. f"  == "CONST ptlambda(%x. f)"
  "PI x:A. B" == "CONST ptprod(A, %x. B)"

definition
  pteq (infixl "===" 30) where
  "pteq(x,y) == 0"

definition
  typed_eq ("_ ===[_] _") where
  "typed_eq(x,A,y) == if (x = y) then 1 else 0"


(* we use ~> because -> is already taken for the proper set-theoretic simple function space *)
abbreviation
  ptsimplefun :: "i => i => i" (infixr "~>" 60) where
  "A ~> B == ptprod(A, %_. B)"

term "PI x:A~>univ. PI z:A. x # ((fun y. y) # z)"

term "x : y"








(* elaboration rules *)




definition
  elabjud :: "i => i => i => o" ("_ elabto _ : _") where
  [MRjud 1 2]: "elabjud(t, t', A) == t' : A"
definition
  printsasjud :: "i => i => o" ("_ printsas _ ") where
  [MRjud 1 1]: "printsasjud(t, t') == True"


ML {*
  local
    fun dest_jud_name t =
      case MetaRec.decompose_judgement (Context.Proof @{context}) t of
        SOME (jud, _) => jud
      | NONE => error ("internal error in lookup of judgement name in  "
          ^Syntax.string_of_term @{context} t)
  in
    val elabjud_n = dest_jud_name @{prop "t elabto t' : A"}
    val printsasjud_n = dest_jud_name @{prop "t' printsas t"}
  end

*}

(* TODO(feature): bei Ueberlappungen der printsas Regeln warnen *)
ML {*
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

  fun elabMR_decl_attr checked = Scan.lift (Scan.option Parse.int
    >> (fn prio_opt => fn (gctxt, elab_rl) =>
       let
         val prio = the_default 0 prio_opt
         val ctxt = Context.proof_of gctxt
         val printsas_rl = derive_printsas_rule ctxt elab_rl
         val _ =
           case gctxt of (* to avoid output for each local theory layer *)
             Context.Theory _ => Output.writeln ("generated printing rule\n  "
               ^Display.string_of_thm ctxt printsas_rl^"\n")
           | _ => ()
         val add_rule = if checked then MetaRec.add_rule else MetaRec.add_rule_unchecked
         val gctxt2 = gctxt |> fold (add_rule prio) [elab_rl, printsas_rl]
       in (SOME gctxt2, SOME elab_rl) end))
  end
*}


setup {*
  Attrib.setup (Binding.name "elabMR") (elabMR_decl_attr true)
    "Declaration of elaboration metarec clauses"
  #> Attrib.setup (Binding.name "elabMR_unchecked") (elabMR_decl_attr false)
    "Declaration of unchecked elaboration metarec clauses"
*}


definition
  constraint_typing :: "i => i => o" ("_ <: _") where
  [MRjud 2 0]: "constraint_typing (t, A) == t : A"
definition
  syn_constraint_typing :: "i => i => o" ("_ :> _") where
  [MRjud 1 1]: "syn_constraint_typing (t, A) == t : A"

definition
  constraint_meta_typ :: "'a::{} => ('a => prop) => prop" ("_ <:: _") where
  [MRjud 2 0]: "constraint_meta_typ (t, A) == A(t)"
definition
  syn_constraint_meta_typ :: "'a::{} => ('a => prop) => prop" ("_ ::> _") where
  [MRjud 1 1]: "syn_constraint_meta_typ (t, A) == A(t)"

lemma [MRjud 2 0]: "i < j == i < j" by simp

definition
  univ_less (infixl "u<" 50) where
  [MRjud 2 0]: "univ_less(x,y) == x < y"

(* NB: Ordinal.le(x,y) is just an abbreviation for x < succ(y), so we cannot reuse this *)
definition
  univ_leq (infixl "u<=" 50) where
  [MRjud 2 0]: "univ_leq(x,y) == x le y"

(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* low prio rule for type inference of free variable x *)
(* FIXME?: statt immer neue Unifvar zu generieren bei bereits vorhandenem constraint (x <: A')
   sofort  Unifikation A == A'  durchfuehren. Entspricht also on-the-fly constraint simplification mit der
   Typ-Constraint-Sharing-Regel von unten. Problematisch weil constraint discharge nur global am Ende
   erfolgen kann. *)
lemma [elabMR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;  foconstraint (i <: nat)  ;  constraint (x <: A) |] ==>
  x elabto x : A"
 unfolding elabjud_def constraint_const_def constraint_typing_def .

lemma [elabMR]: "[|
    t1 elabto t1' : T  ;
    t2 elabto t2' : T'  ;
    unify T T' |] ==>
  (t1 === t2) elabto (t1' ===[T] t2') : bool"
  unfolding bool_def elabjud_def typed_eq_def
  by simp

(* NB: no printsas rule for this, rule for printing variables is used instead  *)
lemma [MR_unchecked]: "[|
    freshunifvar x  ;  freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;  foconstraint (i <: nat)  ;  constraint (x <: A) |] ==>
  ? elabto x : A"
 unfolding elabjud_def constraint_const_def constraint_typing_def .

lemma [elabMR_unchecked]: "[|
    t1 elabto t1' : T  ;
    freshunifvar A  ;  freshunifvar B  ;
    unify T (PROD x:A. B(x))  ;
    t2 elabto t2' : A'  ;
    unify A A'  |] ==>
 (t1 # t2) elabto (t1' ` t2') : B(t2')"
  unfolding elabjud_def unify_const_def
  by (rule apply_type)


(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;   foconstraint (i <: nat) ;
    !! x.  x elabto x : A  ==>  t(x) elabto t'(x) : B(x)  |] ==>
  (fun x. t(x)) elabto (lam x:A. t'(x)) : (PROD x:A. B(x))"
  unfolding elabjud_def fresh_unifvar_const_def
  by (rule lam_type)

(* NB: not elabMR registered to avoid overlapping printsas rule with rule above *)
lemma [MR]: "[|
    A elabto A' : guniv i  ;
    !! x.  x elabto x : A'  ==>  t(x) elabto t'(x) : B(x)  |] ==>
  (lam x:A. t(x)) elabto (lam x:A'. t'(x)) : (PROD x:A'. B(x))"
  unfolding elabjud_def fresh_unifvar_const_def
  by (rule lam_type)



lemma [elabMR]: "[|
    A elabto A' : guniv i  ;  foconstraint (i <: nat)  ;
    !! x.  x elabto x : A'  ==>  B(x) elabto B'(x) : guniv j  ;  foconstraint (j <: nat)  ;
    freshunifvar k  ;  foconstraint (k <: nat)  ;  foconstraint (i u<= k)  ;
    foconstraint (j u<= k)  |] ==>
  (PI x:A. B(x)) elabto (PROD x:A'. B'(x)) : guniv k"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def fresh_unifvar_const_def univ_leq_def
  apply (rule prod_in_guniv)
  apply assumption
  apply (rule guniv_cumul[of i k], assumption+)
  by (rule guniv_cumul[of j k], assumption+)

(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar j  ;
    foconstraint (i <: nat)  ;  foconstraint (j <: nat)  ;   foconstraint (i u< j)  |] ==>
  univ elabto (guniv i) : (guniv j)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def univ_less_def
  by (rule guniv_in_guniv)

(* NB: avoid overlap with printsas rule with univ elaboration rule above *)
lemma [MR_unchecked]: "[|
    freshunifvar j  ;
    i elabto i' : A  ;  unify A nat  ;
    foconstraint (i' <: nat)  ;  foconstraint (j <: nat)  ;   foconstraint (i' u< j)  |] ==>
  (guniv i) elabto (guniv i') : (guniv j)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def unify_const_def univ_less_def
  by (rule guniv_in_guniv)

lemma [elabMR]: "[|
    freshunifvar i  ;  foconstraint (i <: nat)  |] ==>
  nat elabto nat : (guniv i)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (rule nat_in_guniv)




(* constraint simplification *)

lemma [impl_frule]: "x elabto x : A ==> x :> A"
  by (simp add: syn_constraint_typing_def elabjud_def)

lemma [MR]: "
    constraint (t <: A) ==>
  t <: A"
  by (simp add: constraint_const_def)

lemma [MR]: "
    constraint (t <:: A) ==>
  t <:: A"
  by (simp add: constraint_const_def)

lemma [MR]: "
    try (t :> A) ==>
  t <: A"
  by (simp add: syn_constraint_typing_def constraint_typing_def try_const_def)

lemma [MR]: "
    try (t ::> A) ==>
  t <:: A"
  by (simp add: syn_constraint_meta_typ_def constraint_meta_typ_def try_const_def)




definition
  mPi :: "('a::{} => prop) => ('a => 'b::{} => prop) => ('a => 'b) => prop" where
  "mPi(P, Q) == (% f. (!! x. PROP P(x) ==> PROP Q(x, f(x))))"
abbreviation
  msPi where
  "msPi(A, B) == mPi(% x. Trueprop(x:A), B)"
abbreviation
  mssPi where
  "mssPi(A, B) == mPi(% x. Trueprop(x:A), % x y. Trueprop(y : B(x)))"

syntax
  "_MPI" :: "[pttrn, 'a => prop, 'c=>prop] => (('a => 'c) => prop)" ("(3MPI _ : _./ _)" 10) 
  "_MsPI" :: "[pttrn, i, 'c=>prop] => ((i => 'c) => prop)" ("(3MsPI _ : _./ _)" 10) 
  "_MssPI" :: "[pttrn, i, i] => ((i => i) => prop)" ("(3MssPI _ : _./ _)" 10) 
translations
  "MPI x : P. Q" == "CONST mPi(P, % x. Q)"
  "MsPI x : A. B" == "CONST msPi(A, % x. B)"
  "MssPI x : A. B" == "CONST mssPi(A, % x. B)"

abbreviation
  metafun1 :: "i => ('b::{} => prop) => (i => 'b) => prop" (infixr "=>" 30)
where
  "metafun1(A, P2) == (MsPI x : A. P2)"
abbreviation
  metafun2 :: "i => i => (i => i) => prop" (infixr "=>" 30)
where
  "metafun2(A, B) == (MssPI x : A. B)"

term "MPI x : P. Q(x)"
term "MsPI x : A. B(x)"
term "MPI x : (% x. Trueprop(x:A)). B(x)"
term "MPI x : (% x. Trueprop(x:A)). (% y. Trueprop (y:B(x)))"
term "MsPI x : A. B"
term "MssPI x : A. B"


(* NB: contextual discharge relies on removal of non-relevant fixes and assms in front of
      the resulting constraints.
      Cannot be realized as an constraint simplification rule that is executed
      as part of the propagation machinery, because the fixes, assms context has to
      be gone then already.
   E.g. in
      (fun x. fun y. f x y) elabto (lam x:A. lam y:B(x). f x y) : A -> B(x) -> C(x)
   we encounter the constraint  (!! x. x:A ==> B(x) <: guniv ?i)
   which has to be simplified to  B <:: A => guniv ?i  *)
(* FIXME: contextual discharge in context order instead of argument order *)
(* NB: only realizes contextual discharge of typing constraints,
     because x :> A is only issued for fixes x. *)
(* TODO: if we ever map typing constraints f <:: P to ZF-constraints f <: B,
   the case of inferring the types of newly defined constants from their definition
   gets more involved, as we need to postprocess occurrences  ?B ` x  in the inferred
   type back to  ?B2(x) by ?B := (% x:A. ?B2(x)),
   to avoid need of unification modulo ZF-beta during type inferences involving
   the new constant *)

(* bad, because this creates ZF-functions for type constructors and so creates the need
    for unification modulo ZF-beta *)
(* lemma typ_constraint_zf_ctxt_discharge_MR[MR]: "[|
     freshunifvar f  ;
     !! x. try (unify (appt(x)) (f ` x))  ; try (x :> A)  ;
     f <: A -> B  |] ==>
   appt(x) <: B"
  unfolding try_const_def unify_const_def elabjud_def
    constraint_typing_def syn_constraint_typing_def
  by simp *)

(* NB: the next 2 rules feature a B(x) non-pattern in non-primary input position.
   They can only be applied usefully by metarec if x is a free variable. *)
  
(* TODO: unchecked for now because variable availability analysis is
     cautious about non-pattern match against input B(x) *)
lemma typ_constraint_ctxt_discharge_MR[MR_unchecked]: "[|
     try (x :> A)  ;
     f <:: MsPI x : A. B(x)  |] ==>
   f(x) <:: B(x)"
  unfolding try_const_def unify_const_def elabjud_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp

(* TODO: unchecked for now because variable availability analysis is
     cautious about non-pattern match against input B(x) *)
lemma typ_constraint_ctxt_discharge_MR2[MR_unchecked]: "[|
     try (x :> A)  ;
     f <:: MssPI x : A. B(x) |] ==>
   f(x) <: B(x)"
  unfolding try_const_def unify_const_def elabjud_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp


(* NB: useful when a constraint F <:: A => B gets instantiated with F:=(%x. ...)
   due to delayed structural unifications *)
lemma [MR]: "[|
    !! x. x :> A ==> f(x) <:: B  |] ==>
  (% x. f(x)) <:: A => B"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def .
lemma [MR]: "[|
    !! x. x :> A ==> f(x) <: B  |] ==>
  (% x. f(x)) <:: A => B"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def constraint_typing_def .
  



lemma [MR]: "
    foconstraint (i <: nat) ==>
  nat <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def
  by (rule nat_in_guniv)

lemma [MR]: "[|
    foconstraint (i <: nat)  ;
    A <: guniv i  ;  !! x. x :> A ==> B(x) <: guniv i  |] ==>
  (PROD x:A. B(x)) <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def syn_constraint_typing_def
  by (rule prod_in_guniv)

(* NB: i,j are always universe level variables, so the constraint (i u< j) cannot really
   be solved right now and can at best be refuted if i = j *)
lemma [MR]: "[|
    foconstraint (i <: nat) ;  foconstraint (j <: nat)  ;  foconstraint (i u< j) |] ==>
  guniv i <: guniv j"
  unfolding foconstraint_const_def constraint_typing_def univ_less_def
  by (rule guniv_in_guniv)



schematic_lemma "(PROD x:A. PROD y:B(x). C(x, y)) <: guniv i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops






lemma constraint_typ_apply: "
  [|  x elabto x' : A  ;  g <: (PROD x:A. B(x))  |] ==> g ` x' <: B(x')"
  unfolding constraint_typing_def elabjud_def
  by (rule apply_type)

(* could be useful for more general type constraint context discharge
   into dependent products *)
ML {*
  (* returns SOME ((C', proof of normalized C0 with hyp C'), new context) on success *)
  fun typ_constraint_ctxt_discharger rel_fixes C0 ctxt =
    let
      val C = MetaRec.norm_with_env_in_run_state ctxt C0
      val gctxt = Context.Proof ctxt


      val rel_assms = MetaRec.get_assms gctxt |> map_filter (fn assm =>
        case MetaRec.decompose_judgement gctxt assm of
          SOME ("elabjud_jud", (x, [], [x', A ])) =>
            if member (op =) rel_fixes x andalso x = x' then
              SOME ((x, A), assm)
            else
              NONE
        | _ => NONE)
     
      fun zfapply_typ_constraint_prf h' larg B ctxt3 =
        case find_first (fn ((x, _), _) => larg = x) rel_assms of
          SOME ((x, A), assm) =>
            let
              val C2 = @{term constraint_typing} $ h' $ (@{term Pi} $ A $ Term.lambda larg B)
              (* prf3 proves C2 under hyp C3 *)
              val ((C3, prf3), ctxt4) =
                case typ_constraint_ctxt_discharger rel_fixes C2 ctxt3 of
                  SOME subres => subres
                | NONE => ((C2, MetaRec.assumption_prf C2), ctxt3)
              val (prf_res, ctxt5) = MetaRec.mps_match_on_freshthm_prf @{thm constraint_typ_apply}
                [MetaRec.assumption_prf assm, prf3] ctxt4
            in
              SOME ((C3, prf_res), ctxt5)
            end
        | NONE => NONE

    in
      case MetaRec.decompose_judgement gctxt C of
        SOME ("constraint_typing_jud", (t, [B], _)) =>
          let val (h, args) = Term.strip_comb t
          in
            case try Term.dest_Var h of
              NONE =>
                (case h of
                  Const(@{const_name apply}, _) $ h' $ larg =>
                    zfapply_typ_constraint_prf h' larg B ctxt
                | _ => NONE)
            | SOME (ixn, hT) =>
                (case try split_last args of
                  NONE => NONE
                | SOME (args', larg) =>
                    let
                      val v'T = map fastype_of args' ---> Term.body_type hT
                      val (v', ctxt2) = MetaRec.genvar_on_run_state (fst ixn) v'T ctxt
                      val h' = list_comb (v', args')
                      val v'app = @{term "apply"} $ h' $ larg |> fold_rev Term.lambda args
                      val ctxt3 = ctxt2 |> Context.proof_map (MetaRec.map_env_in_run_state
                        (curry Envir.update ((ixn, hT), v'app)))
                    in zfapply_typ_constraint_prf h' larg B ctxt3 end)
           end
      | _ => NONE
    end
*}









ML {*
  fun elab ctxt t =
    exception_trace (fn () =>
      let
        val (th, [elab_t, _]) = MetaRec.metarec_fully_discharged ctxt elabjud_n (t, [])
        val (_, [t']) = MetaRec.metarec_fully_discharged ctxt printsasjud_n
          (elab_t, [])
        val _ =
          if t aconv t' then ()
          else warning ("elab: print-translated elaboration is not original input:\n  "
            ^Syntax.string_of_term ctxt t
            ^"\n  "^Syntax.string_of_term ctxt t')
      in
        th
      end)

  fun elab_with_expected_error exp_err_match ctxt t =
    let
      val err_msg =
        (let val _ = elab ctxt t
        in NONE end)
        handle ERROR msg => SOME msg
    in
      if not (is_some err_msg) then
        error "we expected elaboration to fail"
      else if not (match_string exp_err_match (the err_msg)) then
        error ("elaboration failed as expected, but error message did not match:\n\n"
          ^the err_msg)
      else
        let val _ = Output.writeln ("elaboration failed as expected. error message follows:\n\n"
          ^the err_msg^"\n\n")
        in () end
    end
*}
(* NB: exception traces seem better with deactivated debugging *)

ML {*  elab @{context} @{term "x :: i"}  *}

ML {*  elab @{context} @{term "(fun x. x)"}  *}

(* NB: no typing constraint sharing of  ?A22 <: guniv ?i39,  ?A22 <: guniv ?i16  yet*)
ML {*  elab @{context} @{term "f # x"}  *}


(* tests of derivations with occurences of schematic variables in goals *)
schematic_lemma "(PROD x:?XT(z). ?YT(z,x)) <: guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(PROD x:?XT_(z). ?YT(z,x)) <: guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(PROD x:?XT3434(z). ?YT2435(z,x)) <: guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(% z. PROD x:?A(z). ?B(z,x)) <:: ?A2 => guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(% z. PROD x:?A(z). ?B(z,x)) <:: C => guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops



(* NB: employs structural unification for  ?B(x) == (PROD y:?C. ?D(y)),  i.e.
     ?B := (% x. PROD y:?C'(x). ?D'(x, y)),   ?C := ?C'(t)    ?D := ?D'(t) *)
ML {*  elab @{context} @{term "f # x # y"}  *}

ML {*  elab @{context} @{term "f # x # x # x"}  *}

ML {*  elab @{context} @{term "f # x # x # x # x"}  *}

ML {*
  val fixes = Variable.dest_fixes @{context} |> map snd
  val constraints = Variable.constraints_of @{context} |> fst |> Vartab.dest |> filter (fn ((n, ix), _) => ix = ~1)
            |> map (fn ((n, _), T) => Free(n,T) |> Syntax.string_of_term @{context})
*}


ML {*  elab @{context} @{term "(fun f. fun x. blub(f, x))"}  *}

(* FIXME: type constraint for bla is not contextually discharged, because
     bla does not have all context elements as arguments that its inferred type may depend on.
   Unification variables in inferred type for a term may only
   depend on those *fixes* that the term really contains *)
ML {*  elab @{context} @{term "(fun f. fun x. bla(x))"}  *}

(* FIXME: contextual discharge of typing constraint for bla only works if
     the order of contextual arguments is the same as their occurrence in the context,
     due to dependent type formation in contextual discharge rule.
     The order of contextual discharge should be based on the order in the context,
     not the argument order, but this seems hard to achieve *)
ML {*  elab @{context} @{term "(fun f. fun x. blub(x, f))"}  *}

(* NB: no unification of universe constraints for the same type yet *)
ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}


ML {*  elab @{context} @{term "(fun f. fun g. fun x. f # (g # x))"}  *}


(* FIXME?: abstracted universe level annotations lead to unsatisfiable first-order constraints
     for universe levels that are used in subterms.
   we may not unlift them in that case or we need local constraint discharge.
   This should be resolvable by careful local type inference? *)
(* ML {*  elab @{context} @{term "(lam i:nat. lam x:guniv i. fun f. f # x)"} *} *)

(* but this works *)
ML {*  elab @{context} @{term "(lam x:guniv i. fun f. f # x)"} *}



(* fails with occurs check *)
ML {*  elab_with_expected_error "unification of * and * failed" @{context} @{term "(fun x. x # x)"} *}











definition
 universe_inconsistency where
 [MRjud 1 0]: "universe_inconsistency(x) == False"


(* constraint loeser *)
(* ueber constraint handling rules die die Ableitungsschritte tracen? wir sollten uns auch
   merken welche Regelanwendung ein constraint erzeugt hat! *)
(* TODO: forward rules werden nicht fair angewandt, aber haben ja auch keine Simplification-Regeln
    also egal bzgl. Terminierung? *)
(* vllt CHRs am einfachsten zu implementieren wenn wir Propagation-Regel als Simplification-Regeln
   kodieren. !!! Dann kann man das auch als eine Art Multi-Head-Narrowing ansehen !!!
   Nervig wird dann hier vor allem die staendige Permutation der Metakonjunktionen im Goal so das
   eine Regel passt. Mit Konversions vermutlich zu nervig, stattdessen mit neuem Subgoal arbeiten
   das man mit viel conjI, conjE und assumption loest *)
(* bzgl. Constraint-Minimierung: klassisch bei CHRs soll alle Minimierung ueber Simplification passieren,
   aber das reicht uns nicht weil ja die Propagierungsresultate die nicht vereinfacht wurden noch
   rumschwirren. Kann man vllt einfach sagen das man die urspruenglichen Constraints nimmt, ohne die
   die vereinfacht wurden und zusaetzlich dazu die Vereinfachungsresultate? Aber so kriegt man ja
   die Redundanzen in den urspruenglichen Constraints nicht eliminiert!!

   Ansonsten: Gerichteten Hyper-Graph (Knoten sind Constraints, Kanten sind von einer
   Menge von Constraints zu einem dadurch implizierten Menge von Constraints) aufbauen der repraesentiert
   welche der urspruenglichen Constraints und vereinfachten Constraints
   einander implizieren (ggf nach Instantiierung?).
   Zur Minimierung dann eine kleinstmoegliche Menge von Constraints zuruecklassen (die nicht vereinfacht wurden)
   von denen alle anderen Constraints aus erreichbar sind im Hyper-Graph.
   Aus starken Zusammenhangskomponenten die nicht anders erreichbar sind nimmt man dann also
   nur ein Constraint. *)
(* Gesamt-Algorithmus ist dann wie folgt:
     * Constraint-Propagierung, d.h. alle relevanten Konsequenzen aus Constraints generieren
       und die Generierungsrelation als Hypergraph verwalten
     * dabei Vereinfachung (ggf. Eliminierung oder Gesamt-Fehlschlag) mancher Constraints 
       (wird als bidirektionale Kante im Hypergraph verwaltet, wobei die Constraints die vereinfacht
        wurden nicht genutzt werden duerfen; die Vereinfachung kann Unifikation
       als Seiteneffekt anstossen; ggf. Backtracking ueber solche Regelanwendungen weil sie
       globale Auswirkungen haben, oder nehmen wir Konfluenz an?)
     * Wahl einer minimalen Menge von Constraints die die Gesamtmenge erzeugen (modulo den Vereinfachungen) *)
(* wie bei echten CHRs matchen wir die Regeln bloss und nutzen dann ggf. explizite Unifikation in den Premissen *)

(* relevant for constraint subsumption of  i u<= j *)
lemma [constraint_propag_rule]: "i u< j ==> i u<= j"
  unfolding univ_less_def univ_leq_def
  by (rule Ordinal.leI)
  

lemma [constraint_propag_rule]: "i u< j &&& j u< k ==> i u< k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.lt_trans)

lemma [constraint_propag_rule]: "i u< j &&& j u<= k ==> i u< k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.lt_trans2)

lemma [constraint_propag_rule]: "i u<= j &&& j u< k ==> i u< k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.lt_trans1)

(* NB: we avoid looping on  i u<= i &&& i u<= i ==> i u<= i *)
lemma [constraint_propag_rule]: "try (intensionally_inequal (i, j)) ==> i u<= j &&& j u<= k ==> i u<= k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.le_trans)

lemma [constraint_simp_rule]: "universe_inconsistency(0) ==> (i u< j &&& j u< i)"
  apply (rule Pure.conjunctionI)
  by (simp add: universe_inconsistency_def)+

  (* NB: no try around unify. corresponds to CHR  (i <= j , j <= i) == (i = j) *)
lemma [constraint_simp_rule]: "[| unify i j  ;  constraint (i <: nat)  ;  constraint (j <: nat)  |] ==>
  (i u<= j &&& j u<= i)"
  unfolding univ_less_def univ_leq_def
  apply (rule Pure.conjunctionI)
  by (simp add: unify_const_def constraint_const_def constraint_typing_def)+

 (* actually a specialization of the rule above *)
lemma [constraint_simp_rule]: "constraint (i <: nat) ==> i u<= i"
  unfolding univ_less_def univ_leq_def
  by (simp add: constraint_const_def constraint_typing_def)

(* NB: this is not a simplification rule because we have to consider all combinations *)
lemma [constraint_propag_rule]: "[|  unify A A2  ; t <: A &&& t <: A2 |] ==> True"
  by (simp add: constraint_const_def unify_const_def conjunctionI)
lemma [constraint_propag_rule]: "[|  unify A A2  ; t <:: A &&& t <:: A2 |] ==> True"
  by (simp add: constraint_const_def unify_const_def conjunctionI)



ML {*  elab_with_expected_error "unification of * and * failed" @{context} @{term "x # x"} *}

(* NB: now the guniv constraints for ?A22 have been unified due to the constraint sharing rule *)
ML {*  elab @{context} @{term "f # x"}  *}

(* NB: now the universe constraints get unified due to the constraint sharing rule *)
ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}


(* TODO(feature): discharge nat-upwards-joining constraints  i u<= k,  j u<= k
   by setting  k := max(i,j)  if k does not occur in resulting judgement  *)
ML {*  elab @{context} @{term "lam f : guniv i ~> guniv i. f # (guniv j)"} *}

ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv i. f # (guniv i)"} *}
ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv j ~> guniv i. f # (guniv j) # (guniv i)"} *}
ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv j ~> guniv k ~> guniv i. f # (guniv j) # (guniv k) # (guniv i)"} *}





(* test of postprocessing that unlifts of first-order vars (here: universe level vars) *)
(* FIXME: undischarged context of (?B482(x__, guniv ?i97)_ <: guniv ?i22) constraint
     because of non-variable argument. revision/specialization of structural unification algo? *)
ML {*  elab @{context} @{term "g # univ # (f # univ)"}  *}






ML {*
  fun test_constraint_simp ctxt0 Cs =
    let
      val ctxt0 = ctxt0 |> fold Variable.declare_term Cs
        |> Variable.add_fixes_direct ([] |> fold Term.add_free_names Cs)
      val ctxt = ctxt0
        |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt0))
        |> Context.proof_map (MetaRec.map_constraints_in_run_state (K Cs))
      val ((Cs', implied_Cs), ctxt2) = MetaRec.constraint_simplification true ctxt
      val cert = cterm_of (Proof_Context.theory_of ctxt0)
    in
      (Cs' |> map cert, map (fst #> cert) implied_Cs)
    end
*}

ML {*
  val res = test_constraint_simp @{context} [@{prop "i u< j"}, @{prop "j u< k"}, @{prop "i u< k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context} [@{prop "i u< j"}, @{prop "j u< k"}, @{prop "k u< l"}, @{prop "i u< l"}, @{prop "j u< l"}]
  val _ = if length (snd res) = 2 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context} [@{prop "i u< j"}, @{prop "j u< k"}, @{prop "i u<= k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context} [@{prop "i u<= j"}, @{prop "j u< k"}, @{prop "i u< k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context} [@{prop "i u< j"}, @{prop "j u<= k"}, @{prop "k u< l"}, @{prop "i u< l"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}





(* examples *)





definition
  dict_ty (infixl "dictof" 50) where
  [MRjud 1 1]: "dict_ty(d,C) == d : C"


definition
  monoid where
   "monoid(A,e,m) == e : A  &  m : A -> A -> A
     & (ALL x:A. ALL y:A. ALL z:A. m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z)
     & (ALL x:A. m ` x ` e = x) & (ALL x:A. m ` e ` x = x)"

definition
  monoids where
  "monoids(A) == { <e, m> : (A * (A -> A -> A)). monoid(A,e,m) }"

lemma monoidI: "e : A ==> m : A -> A -> A ==>
   (!! x y z. x:A ==> y:A ==> z:A ==> m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z) ==>
   (!! x. x:A ==> m ` x ` e = x) ==>
   (!! x. x:A ==> m ` e ` x = x) ==>
   monoid(A,e,m)"
  by (simp add: monoid_def)

lemma monoidsI: "e : A ==> m : A -> A -> A ==>
   (!! x y z. x:A ==> y:A ==> z:A ==> m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z) ==>
   (!! x. x:A ==> m ` x ` e = x) ==>
   (!! x. x:A ==> m ` e ` x = x) ==>
   <e, m> dictof monoids(A)"
  by (simp add: monoids_def monoid_def dict_ty_def)

definition
  monoid_neutral where
  "monoid_neutral == fst"

definition
  monoid_mult where
  "monoid_mult == snd"

lemma monoid_unfold: "mon dictof monoids(A) ==> monoid(A, monoid_neutral(mon), monoid_mult(mon))"
  apply (simp add: monoids_def monoid_neutral_def monoid_mult_def dict_ty_def)
  apply (erule conjE)
  apply (erule splitE, assumption)
  by simp

lemma monoidsI_via_laws: "m : A * (A -> A -> A) ==> monoid(A, monoid_neutral(m), monoid_mult(m)) ==> m dictof monoids(A)"
  apply (simp add: dict_ty_def monoids_def monoid_def)
  apply (erule SigmaE)
  by (simp add: monoid_neutral_def monoid_mult_def)


lemma monoid_lawsD: assumes mon: "monoid(A,e,m)"
  shows "e : A"
    and "m : A -> A -> A"
    and "(!! x y z. x:A ==> y:A ==> z:A ==>
       m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z)"
    and "(!! x. x:A ==> m ` x ` e = x)"
    and "(!! x. x:A ==> m ` e ` x = x)"
  apply (insert mon)
  by (simp add: monoid_def)+

lemma monoids_lawsD: assumes m: "m dictof monoids(A)"
  shows "monoid_neutral(m) : A"
    and "monoid_mult(m) : A -> A -> A"
    and "(!! x y z. x:A ==> y:A ==> z:A ==>
       monoid_mult(m) ` x ` (monoid_mult(m) ` y ` z) = monoid_mult(m) ` (monoid_mult(m) ` x ` y) ` z)"
    and "(!! x. x:A ==> monoid_mult(m) ` x ` monoid_neutral(m) = x)"
    and "(!! x. x:A ==> monoid_mult(m) ` monoid_neutral(m) ` x = x)"
  by (simp add: dict_ty_def monoid_unfold[OF m, simplified monoid_def])+




definition
  group where
  "group(A,e,m,inv) == monoid(A,e,m)
     & inv : A -> A
     & (ALL x:A. m ` x ` (inv ` x) = e) & (ALL x:A. m ` (inv ` x) ` x = x)"

lemma groupI: "inv : A -> A ==>
   monoid(A,e,m) ==>
   (!! x. x:A ==> m ` x ` (inv ` x) = e) ==>
   (!! x. x:A ==> m ` (inv ` x) ` x = x) ==>
   group(A,e,m,inv)"
  by (simp add: group_def)

lemma groupI2: "e : A ==> m : A -> A -> A ==> inv : A -> A ==>
   (!! x y z. x:A ==> y:A ==> z:A ==> m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z) ==>
   (!! x. x:A ==> m ` x ` e = x) ==>
   (!! x. x:A ==> m ` e ` x = x) ==>
   (!! x. x:A ==> m ` x ` (inv ` x) = e) ==>
   (!! x. x:A ==> m ` (inv ` x) ` x = x) ==>
   group(A,e,m,inv)"
   by (simp add: group_def monoid_def)

definition
  groups where
  "groups(A) == { <e, m, inv> : (A * (A -> A -> A) * (A -> A)). group(A,e,m,inv) }"

lemma group_dict_ty: "g dictof groups(A) ==> g : A * (A -> A -> A) * (A -> A)"
  by (simp add: dict_ty_def groups_def)

lemma groupsI: "e : A ==> m : A -> A -> A ==> inv : A -> A ==>
   (!! x y z. x:A ==> y:A ==> z:A ==> m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z) ==>
   (!! x. x:A ==> m ` x ` e = x) ==>
   (!! x. x:A ==> m ` e ` x = x) ==>
   (!! x. x:A ==> m ` x ` (inv ` x) = e) ==>
   (!! x. x:A ==> m ` (inv ` x) ` x = x) ==>
   <e, m, inv> dictof groups(A)"
  by (simp add: groups_def group_def monoid_def dict_ty_def)


definition
  group_neutral where
  "group_neutral == fst"

definition
  group_mult where
  "group_mult(g) = fst (snd (g))"

definition
  group_inv where
  "group_inv(g) = snd (snd (g))"

lemma group_unfold: "g dictof groups(A) ==> group(A, group_neutral(g), group_mult(g), group_inv(g))"
  apply (simp add: groups_def group_neutral_def group_mult_def group_inv_def dict_ty_def)
  apply (erule conjE)
  apply (erule splitE, assumption)
  apply (erule splitE[where A="A -> A -> A", where B="% _. A -> A"], simp)
  by simp

lemma group_lawsD: assumes g: "group(A,e,m,i)"
  shows "e : A"
    and "m : A -> A -> A"
    and "i : A -> A"
    and "(!! x y z. x:A ==> y:A ==> z:A ==>
       m ` x ` (m ` y ` z) = m ` (m ` x ` y) ` z)"
    and "(!! x. x:A ==> m ` x ` e = x)"
    and "(!! x. x:A ==> m ` e ` x = x)"
    and "(!! x. x:A ==> m ` x ` (i ` x) = e)"
    and "(!! x. x:A ==> m ` (i ` x) ` x = x)"
  apply (insert g)
  by (simp add: group_def monoid_def)+

lemma groups_lawsD: assumes g: "g dictof groups(A)"
  shows "group_neutral(g) : A"
    and "group_mult(g) : A -> A -> A"
    and "group_inv(g) : A -> A"
    and "(!! x y z. x:A ==> y:A ==> z:A ==>
       group_mult(g) ` x ` (group_mult(g) ` y ` z) = group_mult(g) ` (group_mult(g) ` x ` y) ` z)"
    and "(!! x. x:A ==> group_mult(g) ` x ` group_neutral(g) = x)"
    and "(!! x. x:A ==> group_mult(g) ` group_neutral(g) ` x = x)"
    and "(!! x. x:A ==> group_mult(g) ` x ` (group_inv(g) ` x) = group_neutral(g))"
    and "(!! x. x:A ==> group_mult(g) ` (group_inv(g) ` x) ` x = x)"
  by (simp add: dict_ty_def group_unfold[OF g, simplified group_def monoid_def])+

definition
  monoid_of_group
  where "monoid_of_group(g) = <group_neutral(g), group_mult(g)>"

lemma groups_are_monoids: "g dictof groups(A) ==> monoid_of_group(g) dictof monoids(A)"
  apply (rule monoidsI_via_laws)
  apply (simp add: monoid_of_group_def)
  apply (rule conjI)
  apply (rule groups_lawsD, assumption)+
  apply (drule group_unfold)
  by (simp add: group_def monoid_of_group_def
    group_neutral_def group_mult_def monoid_neutral_def monoid_mult_def)

lemma group_is_monoid: "group(A,e,m,inv) ==> monoid(A,e,m)"
  by (simp add: group_def)

definition
  prod_group_neutral where
  "prod_group_neutral(A,B,eA,eB) ==<eA, eB>"

definition
  prod_group_mult where
  "prod_group_mult(A,B,mA,mB) == lam x:A*B. lam y:A*B. <mA ` fst(x) ` fst(y), mB ` snd(x) ` snd(y)>"

definition
  prod_group_inv where
  "prod_group_inv(A, B, invA, invB) == lam x:A*B. <invA ` fst(x), invB ` snd(x)>"

definition
  prod_group where
  "prod_group(A, B, gA, gB) = <
      prod_group_neutral(A, B, group_neutral(gA), group_neutral(gB)),
      prod_group_mult(A, B, group_mult(gA), group_mult(gB)),
      prod_group_inv(A, B, group_inv(gA), group_inv(gB))>"


lemma prod_group_neutral_simp: "group_neutral (prod_group(A,B,gA,gB)) == prod_group_neutral(A,B,group_neutral(gA),group_neutral(gB))"
  by (simp add: group_neutral_def prod_group_def prod_group_neutral_def)
lemma prod_group_mult_simp:"group_mult (prod_group(A,B,gA,gB)) == prod_group_mult(A,B,group_mult(gA),group_mult(gB))"
  by (simp add: group_mult_def prod_group_def prod_group_mult_def)
lemma prod_group_inv_simp:"group_inv (prod_group(A,B,gA,gB)) == prod_group_inv(A,B,group_inv(gA),group_inv(gB))"
  by (simp add: group_inv_def prod_group_def prod_group_inv_def)


lemma prod_group_in_groups: assumes gA: "gA dictof groups(A)" and gB: "gB dictof groups(B)"
    shows "prod_group(A,B,gA,gB) dictof groups(A*B)"
  unfolding prod_group_def  prod_group_neutral_def prod_group_mult_def prod_group_inv_def
  apply (rule groupsI)
   apply (rule, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply (typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply (rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   thm groups_lawsD(2)[OF gA]
   apply (simp only: beta groups_lawsD(2)[OF gA])
   apply (subst beta, typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply (subst beta, typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply simp
   apply (rule conjI)
   apply (rule groups_lawsD[OF gA], typecheck+)
   apply (rule groups_lawsD[OF gB], typecheck+)

   apply (subst beta, assumption)
   apply (subst beta, typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply simp
   apply (erule SigmaE, simp)
   apply (rule conjI)
   apply (rule groups_lawsD[OF gA], typecheck+)
   apply (rule groups_lawsD[OF gB], typecheck+)

   apply (subst beta, typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply (subst beta, assumption)
   apply simp
   apply (erule SigmaE, simp)
   apply (rule conjI)
   apply (rule groups_lawsD[OF gA], typecheck+)
   apply (rule groups_lawsD[OF gB], typecheck+)

   apply (subst beta, assumption)
   apply (subst beta, typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply simp
   apply (erule SigmaE, simp)
   apply (rule conjI)
   apply (rule groups_lawsD[OF gA], typecheck+)
   apply (rule groups_lawsD[OF gB], typecheck+)

   apply (subst beta, typecheck, rule groups_lawsD[OF gA], rule groups_lawsD[OF gB])
   apply (subst beta, assumption)
   apply simp
   apply (erule SigmaE, simp)
   apply (rule conjI)
   apply (rule groups_lawsD[OF gA], typecheck+)
   by (rule groups_lawsD[OF gB], typecheck+)


lemma monoid_prod: assumes A1mon: "monoid(A1,e1,m1)" and A2mon: "monoid(A2,e2,m2)"
  shows "monoid(A1*A2,prod_group_neutral(A1,A2,e1,e2), prod_group_mult(A1,A2,m1,m2))"
  unfolding prod_group_neutral_def prod_group_mult_def
  apply (rule monoidI)
  apply (typecheck, rule monoid_lawsD[OF A1mon], rule monoid_lawsD[OF A2mon])
  apply (typecheck add: monoid_lawsD(2)[OF A1mon] monoid_lawsD(2)[OF A2mon])
  apply (subst beta, assumption)
  apply (subst beta, typecheck add: monoid_lawsD(2)[OF A1mon] monoid_lawsD(2)[OF A2mon])+
  apply simp
  apply (rule conjI)
  apply (rule monoid_lawsD[OF A1mon], typecheck)
  apply (rule monoid_lawsD[OF A2mon], typecheck)
  apply (subst beta, typecheck add: monoid_lawsD(2)[OF A1mon] monoid_lawsD(2)[OF A2mon])+
  apply (rule monoid_lawsD(1)[OF A1mon], rule monoid_lawsD(1)[OF A2mon])
  apply (erule SigmaE, simp)
  apply (rule conjI)
  apply (rule monoid_lawsD[OF A1mon], typecheck)
  apply (rule monoid_lawsD[OF A2mon], typecheck)
  apply (subst beta, typecheck add: monoid_lawsD(2)[OF A1mon] monoid_lawsD(2)[OF A2mon])+
  apply (rule monoid_lawsD(1)[OF A1mon], rule monoid_lawsD(1)[OF A2mon])
  apply (subst beta, typecheck add: monoid_lawsD(2)[OF A1mon] monoid_lawsD(2)[OF A2mon])+
  apply simp
  apply (erule SigmaE, simp)
  apply (rule conjI)
  apply (rule monoid_lawsD[OF A1mon], typecheck)
  by (rule monoid_lawsD[OF A2mon], typecheck)


 lemma group_prod: assumes
  g1: "group(A1,e1,m1,i1)" and g2: "group(A2,e2,m2,i2)"
 shows "group(A1 * A2, prod_group_neutral(A1,A2,e1,e2),
    prod_group_mult(A1,A2,m1,m2), prod_group_inv(A1,A2,i1,i2))"
  apply (rule groupI)
  apply (simp add: prod_group_inv_def, typecheck, rule group_lawsD(3)[OF g1], rule group_lawsD(3)[OF g2])
  apply (rule monoid_prod[OF group_is_monoid[OF g1] group_is_monoid[OF g2]])
  unfolding prod_group_mult_def prod_group_inv_def prod_group_neutral_def
  apply (subst beta, typecheck)
  apply (subst beta, typecheck, rule group_lawsD(3)[OF g1], rule group_lawsD(3)[OF g2])
  apply (erule SigmaE, simp)
  apply (rule conjI)
  apply (rule group_lawsD[OF g1], assumption)
  apply (rule group_lawsD[OF g2], assumption)
  apply (subst beta, typecheck,  rule group_lawsD(3)[OF g1], rule group_lawsD(3)[OF g2])
  apply (subst beta, assumption)+
  apply simp
  apply (erule SigmaE, simp)
  apply (rule conjI)
  apply (rule group_lawsD[OF g1], assumption)
  by (rule group_lawsD[OF g2], assumption)
  




definition
  gmult where
  "gmult == 0"
definition
  gunit where
  "gunit == 0"
definition
  ginv where
  "ginv == 0"


lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar d ; 
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  ;
    foconstraint (d dictof groups(A)) |] ==>
  gmult elabto (group_mult(d)) : A -> A -> A"
  apply (simp add: elabjud_def constraint_const_def foconstraint_const_def)
  by (rule groups_lawsD)

lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar d  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  ;
    foconstraint (d dictof groups(A)) |] ==>
  gunit elabto (group_neutral(d)) : A"
  apply (simp add: elabjud_def constraint_const_def foconstraint_const_def)
  by (rule groups_lawsD)

lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar d  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  ;
    foconstraint (d dictof groups(A)) |] ==>
  ginv elabto (group_inv(d)) : A -> A"
  apply (simp add: elabjud_def constraint_const_def foconstraint_const_def)
  by (rule groups_lawsD)

lemma [constraint_simp_rule]: "[|
    freshunifvar dA  ;  freshunifvar dB  ;
    unify d (prod_group(A,B,dA,dB))  ;
    foconstraint (dA dictof groups(A))  ;
    foconstraint (dB dictof groups(B))  |] ==>
  d dictof groups(A * B)"
  apply (simp add: unify_const_def constraint_const_def foconstraint_const_def)
  by (rule prod_group_in_groups)

lemma [constraint_propag_rule]: "d dictof groups(A) ==> monoid_of_group(d) dictof monoids(A)"
  by (rule groups_are_monoids)

(* NB: not a constraint simplification rule because we have to consider all combinations (d1,d2) *)
lemma dict_sharing[constraint_propag_rule]: "
   [|  unify d1 d2  ;  d1 dictof C &&& d2 dictof C  |] ==> True"
  by simp


ML {*
  elab @{context} @{term "gmult # x # y === gmult # x # (gmult # y # gunit)"}
*}


ML {*
  val pats = [@{cpat "?d dictof groups(A * B)"},
    @{cpat "?d' dictof monoids(A)"}] |> map (Thm.term_of #> FOLogic.mk_Trueprop)
  val res = exception_trace (fn () => test_constraint_simp  @{context} pats)
  val _ = if length (snd res) = 2 then () else error "expected constraint simplification"
*}
  










(* note that this is still slightly improper since we reuse Larry's list operator instead
   of a proper type constructor formulation
     list : (PI i:nat. guniv i -> guniv i)  *)

definition
  "list' == (lam i:nat. lam A:guniv i. List_ZF.list(A))"

lemma list'_ty: "list' : (PROD i:nat. guniv i -> guniv i)"
  unfolding list'_def
  apply typecheck
  by (rule list_in_guniv)

lemma [MR]: "[|
    foconstraint (i <: nat)  ;    A <: guniv i  |] ==>
  (list' ` i ` A) <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def  list'_def
  apply simp
  by (rule list_in_guniv)


definition
  "nil' == (lam i:nat. lam A:guniv i. List_ZF.Nil)"
definition
  "cons' == (lam i:nat. lam A:guniv i. lam x:A. lam xs:(list'`i`A). List_ZF.Cons(x,xs))"
definition
  "map' == (lam i : nat. lam A : guniv i. lam B : guniv i. lam f : (A -> B). lam xs : (list' ` i ` A).
     List_ZF.map((% x. f ` x), xs) )"

lemma nil'_ty : "nil' : (PROD i:nat. PROD A:guniv i. list' ` i ` A)"
  unfolding nil'_def list'_def
  apply typecheck
  by simp 

lemma cons'_ty : "cons' : (PROD i:nat. PROD A:guniv i. A -> list' ` i ` A -> list' ` i ` A)"
  unfolding cons'_def list'_def
  apply typecheck
  by simp

definition
  list :: "i" where
  "list == 0"
definition
  map :: "i" where
  "map == 0"
(* also we are reusing List_ZF.{Nil,Cons} and their [..]-Syntax for pseudo-term lists *)



lemma [elabMR]: "[|
    freshunifvar i  ;  foconstraint (i <: nat)  |] ==>
  list elabto (list' ` i) : guniv i -> guniv i"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (typecheck add: list'_ty)

lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  |] ==>
  Nil elabto (nil' ` i ` A) : list' ` i ` A"
  unfolding elabjud_def foconstraint_const_def constraint_const_def constraint_typing_def
  by (typecheck add: nil'_ty)

(* TODO: actually we could use a checking judgements  i <= nat, A <= guniv i
   here instead of emitting a constraint *)
lemma [elabMR_unchecked]: "[|
    t elabto t' : A  ;
    ts elabto ts' : list' ` i ` A2  ;
    unify A A2  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)   |] ==>
  (Cons(t,ts)) elabto (cons' ` i ` A ` t' ` ts') : (list' ` i ` A)"
  unfolding elabjud_def constraint_const_def foconstraint_const_def
    unify_const_def constraint_typing_def
  by (typecheck add: cons'_ty)



(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar B  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  ;  constraint (B <: guniv i)  |] ==>
  map elabto (map' ` i ` A ` B) : (A -> B) -> list' ` i ` A -> list' ` i ` B"
  unfolding elabjud_def foconstraint_const_def constraint_const_def constraint_typing_def
  by (simp add: map'_def list'_def)



ML {*  elab @{context} @{term "(map # f # [nat])"}  *}















(* Dinge die man beweisen sollte in einem Papier
     * Bezug zur Typisierung mit Typsystem mit nicht-triv Universenlevelausdruecken und insbesondere
         =========================
           univ i : univ (i + 1)
     * trivial: soundness bzgl Typsystem mit Universenlevel-Annotationen und vorgegebenen
       Universenlevel-Constraints
     * completeness dazu auch ?

     * zyklische Abhaengigkeiten zwischen freien Variablen und ihren den Typen, zB
         x : A(y) ==> y : B(x) ==> t(x,y) : C(x,y)
       ist bei uns moeglich weil Typisierungsregeln first-class sind und wir also nicht
       zwingend Typisierungsconstraints zu dependent products dischargen muessen!
       Dependent type theories koennen das nicht weil weder (% x y. t(x,y)) noch (% y x. t(x,y))
       typisierbar sind also muss man dann zu grober Typisierung von x,y und
       explizitem Beweisen x in A(y), y in B(x) uebergehen , d.h.
         (% x y : UnivElem. % p : proof(x in A(y)). % q : proof (y in B(x)). t(x,y))

       Grosse Auswirkungen??
         * Ist das innovativ bei Sharing-Problematik bei Records? eher nicht weil sobald man Variablen
           fuer Fields statt Projektionsanwendung shared ist man bei dem Ansatz von Spitters.
           Die dependent record fields im very dependent types paper sind auch wohlgeordnet.
         * man will Typkonstruktionen ja weiterhin schrittweise definieren und nicht fuer
           eine Menge von Variablen mit mutually-recursive Typisierung. Ausser man fuehrt irgendwann
           Vektorvariablen ein.

       Ulf Norell nennt das "insane pi-types" https://github.com/UlfNorell/insane
       circular signatures https://github.com/gelisam/circular-sig sollten auch einfach
         moeglich sein, weil das auf locales mit entsprechenden Annahmen fuehrt (fuer
         die es ja keine Einschraenkung gibt)

    * (fuer spaeter): interessante spezialisierte Typisierungsregeln fuer definierte Typkonstruktoren
        monotone A (<=) := { f : A -> A | ALL x1 x2 : A. x1 <= x2 --> f x1 <= f x2 }
      mit Typisierungsregel
            [|  !! x1 x2.  x1 <= x2  ==>  t x1 <= t x2  |] ==>
          t : monotone A
      oder gleich mit Relators und generalized parametricity?
    * very-dependent types ueber induktive Definitionen und entsprechende Typisierungsregeln.
      Interessant oder kann das Coq auch ueber inductive Types und iota-Reduktion?
*)






