theory UniverseLevelInference
imports "../ZFMetaRec" "../DmitriySubtyping" (* AC *)
begin




ML {*
  val B_x = @{cpat "% z::i. ?B(x::i, z, f(z)) :: i"} |> Thm.term_of
  val prod = @{cpat "% z::i. PROD x:?C(f(z)). ?D(x, z)"} |> Thm.term_of
  val (env', _) = 
    StructUnify.unify true @{theory} (B_x, prod) (EnvDiff.empty 1, [])
  val B_x' = EnvDiff.norm_term env' B_x |> cterm_of @{theory}
  val prod' = EnvDiff.norm_term env' prod |> cterm_of @{theory}
*}

ML {*
  val A1 = @{cpat "?B(x::i)"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val (env', _) = 
    StructUnify.unify true @{theory} (A1, A2) (EnvDiff.empty 1, [])
  val A1' = EnvDiff.norm_term env' A1 |> cterm_of @{theory}
  val A2' = EnvDiff.norm_term env' A2 |> cterm_of @{theory}
*}

ML {*
  val A1 = @{cpat "?B(x::i, x) :: i"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val env = EnvDiff.empty 1
  val (env2, _) = StructUnify.unify true @{theory} (A1, A2) (env, [])
  val A1' = EnvDiff.norm_term env2 A1 |> cterm_of @{theory}
*}


ML {*
  val A1 = @{cpat "?B(x::i)"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val B1 = @{cpat "?D(x :: i) :: i"} |> Thm.term_of
  val B2 = @{cpat "PROD x:?E. ?F(x)"} |> Thm.term_of
  val env = EnvDiff.empty 1
  val (env2, _) = StructUnify.unify true @{theory} (A1, A2) (env, [])
  val A2' = EnvDiff.norm_term env2 A2 |> cterm_of @{theory}
  val B1' = EnvDiff.norm_term env2 B1 |> cterm_of @{theory}
  val B2' = EnvDiff.norm_term env2 B2 |> cterm_of @{theory}
  val (env3, _) = StructUnify.unify true @{theory} (B1, B2) (env2, [])
  val A2'' = EnvDiff.norm_term env3 A2 |> cterm_of @{theory}
*}


(* Direct axiomatization of a hierarchy of Grothendiek universes
   (i.e. universes that are closed under all set-theoretic constructions).
   Equiconsistent to existence of strongly inaccessible cardinals.  *)
axiomatization
  guniv :: "i => i" ("guniv _" [100] 100)
where
  (* we use nat instead of Inf, because Inf is only used to construct nat anyway *)
  nat_in_guniv: "i : nat ==> nat : guniv i" and
  pow_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==> Pow(A) : guniv i" and
  union_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==> Union(A) : guniv i" and
  trans_guniv: "[|  i : nat  ;  x : A  ;  A : guniv i  |] ==> x : guniv i" and
  guniv_in_guniv: "[|  i : nat  ;  j : nat  ;  i < j  |] ==> guniv i : guniv j" and
  (* PrimReplace(A,P) is a completely abstract set if P is non-functional, so no harm is done
     because gunivs are nonempty anyways.
     Weakening this axiom to functional P would also suffice, because Replace ensures artificial
     functionality of P anyway and we never encounter raw PrimReplace terms. *)
  primreplace_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==> PrimReplace(A, P) : guniv i"


lemma trans_guniv2 : "[| i: nat  ;  A : guniv i |] ==> A <= guniv i"
  by (auto intro: trans_guniv)

lemma guniv_cumul: "[|  i : nat  ;  j : nat  ;  i le j ;  x : guniv i |] ==> x : guniv j"
  apply (cases "i = j") apply simp
  apply (rule trans_guniv[of j x "guniv i"], assumption+)
  apply (rule guniv_in_guniv, assumption+)
  apply (rule Ord_linear_lt[of i j], simp+)
  by (simp add: le_iff)

lemma guniv_sub: "[|  i : nat  ;  j : nat  ;  i le j  |] ==> guniv i <= guniv j"
  by (auto intro: guniv_cumul)

lemma guniv_subD: "[|  guniv i <= guniv j  ;  i : nat  ;  j : nat  |] ==> i le j"
  apply (rule Ord_linear_lt[of i j], simp+)
  apply (auto intro: Ordinal.leI)
  apply (drule guniv_in_guniv[of j i], assumption+)
  apply (subgoal_tac "guniv j : guniv j")
  apply (rule mem_irrefl, assumption)
  by auto
  


lemma empty_in_guniv: "i : nat ==> 0 : guniv i"
  apply (rule trans_guniv[where A=nat])
  by (auto intro: nat_in_guniv)

lemma guniv_subclosed: "[| i : nat  ;  A <= B  ;  B : guniv i |] ==> A : guniv i"
  by (auto intro: trans_guniv pow_in_guniv)

lemma replace_in_guniv: "[| i : nat  ; A : guniv i |] ==>
   { y. x:A, F(x,y) } : guniv i"
  unfolding Replace_def
  by (rule primreplace_in_guniv)

lemma repfun_in_guniv:  "[| i : nat  ; A : guniv i |] ==>
   { F(x). x:A } : guniv i"
  unfolding RepFun_def
  by (rule replace_in_guniv)

lemma collect_in_guniv: "[| i : nat  ;  A : guniv i  |] ==>
   { x : A . P(x) } : guniv i"
  unfolding Collect_def
  by (rule replace_in_guniv)

lemma upair_in_guniv: "[| i : nat  ;  a : guniv i  ;  b : guniv i   |] ==>
   Upair(a,b) : guniv i"
  unfolding Upair_def
  apply (rule replace_in_guniv, assumption)
  apply (rule pow_in_guniv, assumption)
  apply (rule pow_in_guniv, assumption)
  by (rule empty_in_guniv)

lemma un_in_guniv: "[| i : nat  ;  A : guniv i  ;  B : guniv i |] ==>
   A Un B : guniv i"
  unfolding Un_def
  apply (rule union_in_guniv, assumption)
  by (rule upair_in_guniv)

lemma inter_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==>
   Inter(A) : guniv i"
  unfolding Inter_def
  apply (rule collect_in_guniv, assumption)
  by (rule union_in_guniv)

lemma int_in_guniv: "[|  i : nat  ;  A : guniv i  ;  B : guniv i |] ==>
   A Int B : guniv i"
  unfolding Int_def
  apply (rule inter_in_guniv, assumption)
  by (rule upair_in_guniv)
  

lemma cons_in_guniv: "[|  i : nat  ;  a : guniv i  ;  A : guniv i  |] ==>
  cons(a,A) : guniv i"
  unfolding cons_def
  apply (rule un_in_guniv, assumption)
  by (rule upair_in_guniv)

lemma singleton_in_guniv: "[|  i : nat  ;  a : guniv i  |] ==>
  { a } : guniv i"
  apply (rule cons_in_guniv, assumption+)
  by (rule empty_in_guniv)

lemma sigma_in_guniv: "[| i : nat  ;  A : guniv i  ;  !! x . x : A ==> B(x) : guniv i  |] ==>
  (SUM x:A. B(x)) : guniv i"
  unfolding Sigma_def
  apply (rule union_in_guniv, assumption)
  by (rule repfun_in_guniv)


lemma prod_in_guniv: "[|  i : nat  ;  A : guniv i  ;  (!! x. x : A ==> B(x) : guniv i)  |]
     ==> (PROD x:A. B(x)) : guniv i"
  unfolding Pi_def
  apply (rule collect_in_guniv, assumption)
  apply (rule pow_in_guniv, assumption)
  by (rule sigma_in_guniv)


lemma lfp_in_guniv: "[|  i : nat  ;  D : guniv i  |] ==> lfp(D,h) : guniv i"
  unfolding lfp_def
  apply (rule inter_in_guniv, assumption)
  apply (rule collect_in_guniv, assumption)
  by (rule pow_in_guniv)

lemma smalluniv_in_guniv: "[|  i : nat  ;  A : guniv i  |]  ==> Univ.univ(A) : guniv i"
  unfolding univ_def Vfrom_def transrec_def wfrec_def wftrec_def
  apply (rule un_in_guniv, assumption+)
  apply (rule union_in_guniv, assumption)
  apply (rule repfun_in_guniv, assumption)
  by (rule nat_in_guniv)


lemma list_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==> List_ZF.list(A) : guniv i"
  unfolding list_def
  apply (rule lfp_in_guniv, assumption)
  by (rule smalluniv_in_guniv)








(* Pseudo terms that will be elaborated.
   Note that we don't introduce a seperate type to allow the
   reuse of free variables in the pseudoterm when elaborating. *)

definition
  ptuniv :: "i" ("univ") where
  "ptuniv == 0"
definition
  hole :: "i" ("?") where
  "hole == 0"
definition (* TODO: use $ instead *)
  ptapp :: "i => i => i" (infixl "#" 100) where
  "ptapp(f,x) == 0"
definition
  ptlambda :: "(i => i) => i" where
  "ptlambda(b) == 0"
definition
  ptprod :: "i => (i => i) => i" where
  "ptprod(A,F) == 0"
definition
  pteq :: "i => i => i" (infixl "===" 30) where
  "pteq(x,y) == 0"
definition
  ptannot :: "i => i => i" ("_ annotyped _") where
  "ptannot(t,A) == 0"
definition
  ptmquant :: "(i => prop) => prop" (binder "!!st " 1) where
  "ptmquant(P) == Trueprop(True)"

(* TODO: is it possible to engineer the coexistence of normal and old-style application syntax ?
   using a transformation function with priority over the normal application syntax transformation function?
   Why does parsing not terminate with both application syntaxes active? *)
(*
abbreviation
  ptapp2 :: "i => i => i" ("_/ _" [1000, 1000] 1000) where
  "ptapp2 == ptapp"

term "f  (x  y)"
*)


syntax
  "_fun" :: "[pttrn, i] => i"  ("(2fun _./ _)" 10)  (* lam already taken for proper ZF abstractions *)
  "_PI"     :: "[pttrn, i, i] => i"  ("(3PI _:_./ _)" 10)

translations
  "fun x. f"  == "CONST ptlambda(%x. f)"
  "PI x:A. B" == "CONST ptprod(A, %x. B)"

(* we use ~> because -> is already taken for the proper set-theoretic simple function space *)
abbreviation
  ptsimplefun :: "i => i => i" (infixr "~>" 60) where
  "A ~> B == ptprod(A, %_. B)"

term "PI x:A~>univ. PI z:A. x # ((fun y. y) # z)"
term "PI x:A. B"

term "x : y"



definition
  typed_eq ("_ ===[_] _") where
  "typed_eq(x,A,y) == if (x = y) then 1 else 0"
definition
  typed_pair :: "i => i => i => i" ("<_, _> typed _") where
  "typed_pair(t1, t2, A) == <t1, t2>"





definition
  inf_lvl_const ("inflvl _") where
  [MRjud 1 0]: "inf_lvl_const(i) == True"

(* TODO(refactor): use univlvlE in proofs instead of 
     apply (simp add: univlvl_def, elim conjE).
   And avoid reintroduction of univlvls from its definition. *)
(* TODO(refactor!): univlvls can start from 0 again, now that univpred is not needed anymore *)
definition
  univlvl where "univlvl == nat"

lemma univlvlE: "i : univlvl ==> (i : nat ==> P) ==> P"
  by (simp add: univlvl_def)
lemma univlvlDnat: "i : univlvl ==> i : nat"
  by (simp add: univlvl_def)

lemma univlvl_in_guniv: "i : nat ==> univlvl : guniv i"
  apply (subst univlvl_def)
  by (rule nat_in_guniv)
  

definition
  univ_less (infixl "u<" 50) where
  [MRjud 2 0]: "univ_less(x,y) == x < y"

(* NB: Ordinal.le(x,y) is just an abbreviation for x < succ(y), so we cannot reuse this *)
definition
  univ_leq (infixl "u<=" 50) where
  [MRjud 2 0]: "univ_leq(x,y) == x le y"

definition
  univ_max (infixl "umax" 80) where
  "i umax j == max(i,j)"

lemma univlvl_to_natD: "i : univlvl ==> i : nat"
  by (simp add: univlvl_def)


definition
  "first_univlvl == 1"
definition
  "usucc == succ"

lemma uleq_refl: "i : nat ==> i u<= i"
  by (simp add: univ_leq_def)
lemma univ_leq_is_less_usucc: "(i u<= j) == (i u< usucc(j))"
  by (simp add: univ_leq_def univ_less_def usucc_def)
lemma univ_less_is_usucc_leq: "(i u< j) ==> usucc(i) u<= j"
  by (simp add: univ_leq_def univ_less_def usucc_def)
lemma usucc_less_from_interm: "i u< j ==> j u< k ==> usucc(i) u< k"
  apply (simp add: univ_less_def usucc_def succ_lt_iff)
  apply (auto intro: Ordinal.lt_trans)
  apply (subgoal_tac "i < i")
    prefer 2 apply (blast intro: Ordinal.lt_trans2)
  by (rule lt_irrefl)
  


lemma umax_nat_ty: "i : nat ==> j : nat ==> (i umax j) : nat"
  by (simp add: univ_max_def max_def)
lemma umax_univlvl_ty: "i : univlvl ==> j : univlvl ==> (i umax j) : univlvl"
  by (simp add: univ_max_def max_def)
lemma first_univlvl_ty: "first_univlvl : univlvl"
  by (simp add: first_univlvl_def univlvl_def)
lemma usucc_univlvl_ty: "i : univlvl ==> usucc(i) : univlvl"
  by (simp add: usucc_def univlvl_def)

lemma umax_larger1: "i : univlvl ==> i u<= (i umax j)"
  by (simp add: max_def univ_max_def univ_leq_def univlvl_def)
lemma umax_larger2: "i : univlvl ==> j : univlvl ==> j u<= (i umax j)"
   apply (simp add: max_def univ_max_def univ_leq_def univlvl_def)
   apply (rule impI) apply (simp add: not_le_iff_lt) by (rule leI)
lemma umax_sup: "i u<= k ==> j u<= k ==> (i umax j) u<= k"
  by (simp add: max_def univ_max_def univ_leq_def)
lemma umax_less_sup: "i u< k ==> j u< k ==> (i umax j) u< k"
  by (simp add: max_def univ_max_def univ_leq_def)
  

lemma univ_leq_from_less: "i u< j ==> i u<= j"
  apply (simp add: univ_leq_def univ_less_def)
  by (rule Ordinal.leI)

lemma guniv_subD2: "[|  guniv i <= guniv j  ;  i : univlvl  ;  j : univlvl  |] ==> i u<= j"
  apply (simp add: univlvl_def univ_leq_def)
  by (rule guniv_subD)







definition
  "univannot_prod_fun == (lam k:univlvl. lam A:guniv k. lam B:A->guniv k.  (PROD x:A. B ` x))"
definition
  "univannot_prod (k, A, B) == univannot_prod_fun ` k ` A ` (lam x:A. B(x))"

lemma univannot_prod_def3: "univannot_prod(k, A, B) == (lam k:univlvl. lam A:guniv k. lam B:A->guniv k.  (PROD x:A. B ` x))
  ` k ` A ` (lam x:A. B(x))"
  by (simp add: univannot_prod_def univannot_prod_fun_def)

lemma univannot_prod_def2: "k : univlvl ==> A : guniv k ==> (!! x. x : A ==> B(x) : guniv k) ==>
  univannot_prod (k, A, B) == (PROD x:A. B (x))"
  apply (subgoal_tac "(lam x:A. B(x)) : A -> guniv k")
  apply (simp add: univannot_prod_def univannot_prod_fun_def cong: Pi_cong)
  by typecheck
  

definition
  annot_metalam :: "i => (i => 'a::{}) => (i => 'a)" where
  "annot_metalam(A, body) == body"

definition
  univannot_lam :: "i => i => (i => i) => i" where
  "univannot_lam(k, A, body) == (lam x:A. body(x))"

syntax
  "_PRODu"     :: "[i, pttrn, i, i] => i"  ("(3PRODu _ _:_./ _)" 10)
  "_mlam" :: "[pttrn, i, i] => i" ("(3mlam _:_./ _)" 10)
  "_lamu" :: "[i, pttrn, i, i] => i" ("(3lamu _ _:_./ _)" [100, 100, 100, 30] 10)
translations
  "PRODu k x:A. B" == "CONST univannot_prod(k, A, %x. B)"
  "mlam x:A. t" == "CONST annot_metalam(A, % x. t)"
  "lamu k x:A. t" == "CONST univannot_lam(k, A, % x. t)"

abbreviation
  simple_univannot_fun :: "i => i => i => i" ("_ ->[_] _" [31, 80, 30] 30) where
  "(A ->[i] B) == (PRODu i _:A. B)"

term "PRODu i x:A. B(x)"
ML {*
 @{term "A ->[k] B ->[k2] C"};;
 @{term "(A ->[k] A) ->[k] B ->[k2] C"}
*}
term "PRODu i _:A. B"

term "mlam x:A. t(x)"
term "lamu k x:A. t(x)"
ML {* @{cpat "lamu k x:(?A). t(x)"} *}


lemma produ_on_good_args: "k : univlvl ==> A : guniv k ==> (!! x. x:A ==> B(x) : guniv k) ==>
   (PRODu k x:A. B(x)) = (PROD x:A. B(x))"
  apply (subgoal_tac "(lam x:A. B(x)) : A -> guniv k")
  defer 1
  apply (typecheck, assumption)
  unfolding univannot_prod_def3
  by (simp cong: Pi_cong)


lemma lam_type_rev: assumes lamty: "(lam x:A. t(x)) : (PROD x:A. B(x))" and aty: "a : A" shows "t(a) : B(a)"
proof -
  have ta_expand: "t(a) = (lam x:A. t(x)) ` a"
    by (simp add: lamty aty)
  show "t(a) : B(a)"
    apply (subst ta_expand)
    apply (rule apply_type)
    by (rule lamty, rule aty)
qed

lemma produ_triv_on_bad_lvl: "k \<notin> univlvl ==> (PRODu k x:A. B(x)) = 0"
  apply (simp add: univannot_prod_def3)
  by (simp add: apply_def)

lemma produ_triv_on_bad_dom: "A \<notin> (guniv k) ==> (PRODu k x:A. B(x)) = 0"
  apply (simp add: univannot_prod_def3 produ_triv_on_bad_lvl)
  by (simp add: apply_def)

lemma produ_triv_on_bad_cod: "\<not> (ALL x:A. B(x) : guniv k) ==> (PRODu k x:A. B(x)) = 0"
  apply (simp add: univannot_prod_def3 produ_triv_on_bad_lvl produ_triv_on_bad_dom)
  apply (simp add: apply_def)
  by (auto intro: lam_type_rev)

lemma nontriv_produ_means_good_args: "(PRODu k x:A. B(x)) ~= 0 ==> k : univlvl & A : guniv k & (ALL x:A. B(x) : guniv k)"
  by (auto intro: produ_triv_on_bad_lvl produ_triv_on_bad_dom produ_triv_on_bad_cod)
  


(* raison d'etre of PRODu *)
lemma produ_in_guniv: "
    k : univlvl ==>
  (PRODu k x:A. B(x)) : guniv k"
  unfolding univannot_prod_def3
  apply (cases "A : guniv k", cases "(lam x:A. B(x)) : A -> guniv k")
  apply simp
  apply (rule prod_in_guniv) apply (auto elim: univlvlE)
  apply (rule lam_type_rev, assumption+)
  apply (blast intro: empty_in_guniv dest: univlvlDnat)
  apply (simp add: apply_def)
  by (blast intro: empty_in_guniv dest: univlvlDnat)


(* argument as follows:
     trivial if (PRODu k1 x:A. B(x)) = 0
     otherwise we have A : guniv k, B : A -> guniv k
      what is missing is B2 : A -> guniv k2  *)
(* only used in supunify, infunify, subunify, which could be extended to lookup constraints and
   produce stronger result that includes univ-typing of output *)
lemma weaken_produ: "[|  k1 : univlvl  ;   k2 : univlvl  ;
    k1 u<= k2  ;  !! x. x:A ==> B(x) <= B2(x)  ;
    !! x. x:A ==> B2(x) : guniv k2 |] ==>
  (PRODu k1 x:A. B(x)) <= (PRODu k2 x:A. B2(x))"
  unfolding univ_leq_def
  apply (cases "(PRODu k1 x:A. B(x)) = 0")
  apply simp
  apply (drule nontriv_produ_means_good_args, elim conjE)
  apply (subgoal_tac "A : guniv k2")
    prefer 2
    apply (blast intro: guniv_cumul[of k1 k2 A] dest: univlvlDnat)
  apply (simp add: produ_on_good_args)
  by (auto intro: Pi_weaken_type)

 
lemma produ_pi_simp: "[|
   i : univlvl  ;  j : univlvl  ;  k : univlvl  ;
   A : guniv i  ;  !! x. x:A ==> B(x) : guniv j  ;
   i u<= k  ;  j u<= k   |] ==>
  (PRODu k x:A. B(x)) == (PROD x:A. B(x))"
  unfolding univ_leq_def
  apply (rule eq_reflection)
  apply (subgoal_tac "A : guniv k")
    prefer 2 apply (blast intro: guniv_cumul[of i k A] univlvlDnat)
  apply (subgoal_tac "!! x. x:A ==> B(x) : guniv k")
    prefer 2 apply (blast intro: guniv_cumul[of j k] univlvlDnat)
  by (simp add: produ_on_good_args)


lemma produI: "[|
    i : univlvl  ;  j : univlvl  ;  k : univlvl  ;
    A : guniv i  ;
    !! x. x : A ==> B(x) : guniv j  ;
    i u<= k  ;  j u<= k  ;
    f : (PROD x:A. B(x)) |] ==>
  f : (PRODu k x:A. B(x))"
  by (subst produ_pi_simp[of i j k A B])

lemma produ_prodrefI: "[|
    i : univlvl  ;  j : univlvl  ;  k : univlvl  ;
    A : guniv i  ;
    !! x. x : A ==> B(x) : guniv j  ;
    i u<= k  ;  j u<= k  ;
    f : (PROD x:A. C(x))  ;
    !! x. x : A ==> f ` x : B(x)  |] ==>
  f : (PRODu k x:A. B(x))"
  apply (subst produ_pi_simp[of i j k A B], assumption+)
  by (rule Pi_type)

lemma produ_lamI: "[|
    i : univlvl  ;  j : univlvl  ;  k : univlvl  ;
    A : guniv i  ;
    A = A'  ;
    i u<= k  ;
    !! x. x : A ==> t(x) : B(x)  ;
    !! x. x : A ==> B(x) : guniv j  ;
    j u<= k  |] ==>
  (lam x:A. t(x)) : (PRODu k x:A'. B(x))"
  apply (subst produ_pi_simp[of i j k A' B], simp+)
  by (rule lam_type)

lemma produ_piE: "[|
  f : (PRODu k x:A. B(x))  ;
  A : guniv i  ;  !! x. x:A ==> B(x) : guniv j  ;
  i : univlvl  ;  j : univlvl  ;  k : univlvl  ;
  i u<= k  ;  j u<= k  ;
  f : (PROD x:A. B(x)) ==> P  |]
  ==> P"
  by (simp add: produ_pi_simp)







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









(* elaboration rules *)




definition
  elabjud :: "i => i => i => o" ("_ elabto _ : _") where
  [MRjud 1 2]: "elabjud(t, t', A) == t' : A"
definition
  metaelab_const :: "prop => prop => prop" ("metaelab _ _") where
  [MRjud 1 1]: "metaelab_const(P, P') == Trueprop(True)"
definition
  printsasjud :: "'a::{} => 'b::{} => o" ("_ printsas _ " [10, 10] 10) where
  [MRjud 1 1]: "printsasjud(t, t') == True"
definition
  synthty_const :: "i => i => o" ("_ synthty _") where
  [MRjud 1 1]: " t synthty A == t : A"
definition
  metasynthty_const :: "'a :: {} => ('a => prop) => prop" ("_ metasynthty _") where
  [MRjud 1 1]: " t metasynthty P == PROP P(t)"
definition
  refty_const :: "i => i => o" ("_ refty _") where
  [MRjud 1 1]: " t refty A == t : A"
definition
  metarefty_const :: "'a :: {} => ('a => prop) => prop" ("_ metarefty _") where
  [MRjud 2 0]: " t metarefty P == PROP P(t)"
definition
  zfnorm_const :: "'a :: {} => 'a => prop" ("zfnorm _ _") where
  [MRjud 1 1]: "zfnorm t t' == (t == t')"

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


(* customized unification judgements *)
definition
  supunify_const :: "i => i => i => o" ("supunify _ _ _") where
  [MRjud 2 1]: "supunify A B C == (A <= C) & (B <= C)" 
definition
  infunify_const :: "i => i => i => o" ("infunify _ _ _") where
  [MRjud 2 1]: "infunify A B C == (C <= A) & (C <= B)" 
definition
  infmetaunify_const :: "('a :: {} => prop) => ('a :: {} => prop) => ('a => prop) => prop"
    ("infmetaunify _ _ _") where
  [MRjud 2 1]: "infmetaunify A B C == ((!! x. PROP C(x) ==> PROP A(x)) &&&
    (!! x. PROP C(x) ==> PROP B(x)))" 
definition
  subunify_const :: "i => i => o" ("subunify _ _") where
  [MRjud 2 0]: "subunify A B == (A <= B)"
definition
  submetaunify_const :: "('a :: {} => prop) => ('a => prop) => prop"
    ("submetaunify _ _") where
  [MRjud 2 0]: "submetaunify P Q == (!! x. PROP P(x) ==> PROP Q(x))"




(* FIXME: rules for refty analogous to <: rules, without the ones for
    contextual discharge and constraint generation.
    How to share rules betweens these judgements? *)



(* TODO: restrict to variables x *)
lemma [impl_frule]: "x synthty A ==> x elabto x : A"
  by (simp add: synthty_const_def elabjud_def)
(* for variable assumption tracking *)
lemma [impl_frule]: "x elabto x : A ==> x :> A"
  by (simp add: syn_constraint_typing_def elabjud_def)
lemma [impl_frule]: "x elabto x : A ==> x synthty A"
  by (simp add: synthty_const_def elabjud_def)
(* for assumption -> constraint propagation *)
lemma [impl_frule]: "x synthty A ==> x <: A"
  by (simp add: synthty_const_def constraint_typing_def)



lemma elab_to_synthty_rewr: "t elabto t' : A' == t' synthty A'"
  by (simp add: elabjud_def synthty_const_def)

lemma true_mimp_rewr: "(True ==> PROP P) == PROP P"
 by simp

lemma refl_unif_mimp_rewr: "(primunify t t ==> PROP P) == PROP P"
  apply (simp add: primunify_const_def)
  apply rule
  apply simp
  by simp

lemma freshunifvar_triv_rewr: "(PROP fresh_unifvar_const(kind, x)) == Trueprop(True)"
  by (simp add: fresh_unifvar_const_def)

ML_file "elab_rule_processing.ML"
setup {* ElabRuleProcessing.setup *}



lemma [moding_rewrite]: "(constraint (t <: A)) == Trueprop(t synthty A)"
  by (simp add: synthty_const_def constraint_const_def constraint_typing_def)
lemma [moding_rewrite]: "Trueprop(t <: A) == Trueprop(t synthty A)"
  by (simp add: synthty_const_def constraint_typing_def)




(* TODO(opt!): check with ML if there is no ZF-beta redex, then abort early without change *)
lemma [MR]: "
  zfnorm t t"
  by (simp add: zfnorm_const_def)

lemma [MR]: "[|
    zfnorm t1 t1'  ;
    zfnorm t2 t2'  |] ==>
  zfnorm t1(t2) t1'(t2')"
 by (simp add: zfnorm_const_def)

lemma [MR]: "[|
    !! x . zfnorm t(x) t'(x)  |] ==>
  zfnorm (% x. t(x)) (% x. t'(x))"
 by (simp add: zfnorm_const_def)

lemma [MR]: "[|
    zfnorm A A'  ;
    !! x . x synthty A' ==> zfnorm t(x) t'(x)  |] ==>
  zfnorm (lamu k x:A. t(x)) (lamu k x:A'. t'(x))"
 by (simp add: zfnorm_const_def synthty_const_def univannot_lam_def)

lemma [MR]: "[|
    zfnorm t1 t1'  ;
    zfnorm t2 t2'  |] ==>
  zfnorm (t1 ` t2) (t1' ` t2')"
 by (simp add: zfnorm_const_def)

(* Pure's beta-reduction happens implicitly *)
(* FIXME?: subunify synthesized type of a into A or join them with zfnorm? *)
lemma [MR]: "[|
    a synthty A  ;
    zfnorm a a'  ;
    zfnorm t(a') t' |] ==>
  zfnorm ((lamu k x:A. t(x)) ` a) t'"
 by (simp add: zfnorm_const_def synthty_const_def univannot_lam_def)




lemma [MR]: "t printsas t" by (simp add: printsasjud_def)
lemma [MR]: "[|
    t1 printsas t1'  ;
    t2 printsas t2'  |] ==>
  t1(t2) printsas t1'(t2')"
  by (simp add: printsasjud_def)



(* synthesis rules for unification variables during elaboration *)
lemma [MR]: "
    try (exconstraint (?? A. (x <: A)) (x <: A))  ==>
  x synthty A"
  by (simp add: try_const_def ex_constraint_const_def constraint_typing_def synthty_const_def)
lemma [MR]: "
    try (exconstraint (?? A. (x <:: A)) (x <:: A))  ==>
  x metasynthty A"
  by (simp add: try_const_def ex_constraint_const_def constraint_meta_typ_def metasynthty_const_def)

(* very low prio synthty rule. necessary for type-checking in
    object-language unification *)
lemma [MR]: "[|
    t1 metasynthty (MssPI x:A. B(x))  ;
    t2 synthty A'  ;
    subunify A' A  |] ==>
  t1(t2) synthty B(t2)"
  unfolding metasynthty_const_def synthty_const_def mPi_def subunify_const_def
  by auto

lemma [MR]: "[|
    t1 metasynthty (MPI x : P. Q(x))  ;
    t2 metarefty P  |] ==>
  t1(t2) metasynthty Q(t2)"
  unfolding metasynthty_const_def metarefty_const_def mPi_def .

lemma [MR]: "[|
    try( t1 metasynthty (MsPI x : A. Q(x)) )  ;
    t2 synthty A'  ;
    subunify A' A  |] ==>
  t1(t2) metasynthty Q(t2)"
  unfolding metasynthty_const_def mPi_def try_const_def synthty_const_def
   subunify_const_def
  by (drule subsetD)

lemma [MR]: "
    try (t synthty A)  ==>
  t metasynthty (% t. Trueprop (t : A))"
  unfolding synthty_const_def metasynthty_const_def try_const_def . 

lemma [MR]: "[|
    !! x. t(x) metasynthty P(x)  |] ==>
  (% x. t(x)) metasynthty (MPI x : (% x. Trueprop(True)). P(x))"
  unfolding metasynthty_const_def mPi_def .

(* FIXME? also allow annotation of mlam with meta-predicates? *)
lemma [MR]: "[|
    !! x. x synthty A ==> t(x) metasynthty B(x)  |] ==>
 (mlam x:A. t(x)) metasynthty (MsPI x:A. B(x))"
 unfolding metasynthty_const_def mPi_def synthty_const_def annot_metalam_def .


lemma [MR]: "[|
    t metasynthty P'  ;  submetaunify P' P  |] ==>
  t metarefty P"
  unfolding metarefty_const_def metasynthty_const_def submetaunify_const_def .

lemma [MR]: "
  t metarefty (% x. Trueprop(True))"
  by (simp add: metarefty_const_def)





definition
  elabbrack :: "i => o" where
  "elabbrack(pt) == True"
(* Dmitriy saves *)
declare [[coercion "elabbrack :: i => o"]]
(* TODO: invisible printing of elabbrack *)

definition
  truenessbrack :: "i => o" where
  "truenessbrack(t) == (t = 1)"
(* TODO: invisible printing of truenessbrack *)












(* nonemptyness derivations for types

definition 
  nonempty :: "i => o" where
  [MRjud 1 0]: "nonempty(A) == (A ~= 0)"

lemma nonempty_altdef: "(Trueprop(nonempty(A))) == (Trueprop (EX x. x : A))"
  apply (simp add: nonempty_def)
  apply (rule equal_intr_rule[of "A~=0", of "EX x. x:A"])
  by auto

lemma [impl_frule]: "x synthty A ==> nonempty(A)"
 by (auto simp add: nonempty_altdef synthty_const_def)

lemma [MR]: "[|
    !! x. x synthty A ==> nonempty (B(x)) |] ==>
  nonempty (PRODu k x:A. B(x))"
  unfolding nonempty_altdef univannot_prod_def3 synthty_const_def
  by (rule AC.AC_Pi)

lemma [MR]: "
    constraint (i <: univlvl) ==>
  nonempty (guniv i)"
  unfolding nonempty_altdef constraint_const_def univlvl_def constraint_typing_def
  apply (rule exI)
  by (rule nat_in_guniv) *)






(* FIXME?: actually use unification modulo beta,ZF-beta instead of primunify, only use primunify
   for performance if no ZF-applications occur in terms *)


(* TODO(refactor?): supunify only needed for elaboration of equality.
  Can we simulate it? Unlikely? *)

lemma [MR]: "
    primunify A B  ==>
  supunify A B A"
  by (simp add: primunify_const_def supunify_const_def)

lemma [MR]: "[|
    primunify A1 A2 ;
    supunify (guniv k1) (guniv k2) (guniv k')  ;
    constraint (k1 <: univlvl)  ;   constraint (k2 <: univlvl)  ;   constraint (k' <: univlvl)  ;
    !! x. supunify B1(x) B2(x) B(x)  ;
    !! x. x synthty A1 ==> B(x) <: guniv k'  |]  ==>
  supunify (PRODu k1 x:A1. B1(x)) (PRODu k2 x:A2. B2(x)) (PRODu k' x:A1. B(x))"
  apply (simp add: primunify_const_def supunify_const_def constraint_const_def constraint_typing_def synthty_const_def)
  apply (elim conjE)
  apply (drule guniv_subD2, assumption+)
  apply (drule guniv_subD2, assumption+)
  unfolding univ_leq_def
  apply (rule conjI)

  apply (cases "(PRODu k1 x:A2. B1(x)) = 0")
    apply simp
  apply (drule nontriv_produ_means_good_args, elim conjE)
  apply (subgoal_tac "A2 : guniv k'")
    prefer 2
    apply (blast intro: guniv_cumul[of k1 k' A2] univlvlDnat)
  apply (simp add: produ_on_good_args)
  apply (blast intro: Pi_weaken_type)

  apply (cases "(PRODu k2 x:A2. B2(x)) = 0")
    apply simp
  apply (drule nontriv_produ_means_good_args, elim conjE)
  apply (subgoal_tac "A2 : guniv k'")
    prefer 2
    apply (blast intro: guniv_cumul[of k2 k' A2] univlvlDnat)
  apply (simp add: produ_on_good_args)
  by (blast intro: Pi_weaken_type)


lemma [MR]: "[|
    try (noexconstraint (i u<= j))  ;
    try (noexconstraint (j u<= i))  ;
    freshFOunifvar k  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (k <: univlvl)  ;
    constraint (i u<= k)  ;  constraint (j u<= k)  |] ==>
  supunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: supunify_const_def constraint_const_def constraint_typing_def
    univ_leq_def univlvl_def)
  apply (rule conjI)
  by (rule guniv_sub, assumption+)+

(* TODO(correctness): does this rely on persistent uniqueness of i'? *)
lemma [MR]: "[|
   try (exconstraint (?? i'. i u<= i') (i u<= i'))  ;
   supunify (guniv i') (guniv j) (guniv k)  ;
   constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
   constraint (i' <: univlvl)|] ==>
  supunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: supunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (elim conjE)
  apply (subgoal_tac "guniv i <= guniv i'")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto

(* TODO(correctness): does this rely on persistent uniqueness of j'? *)
lemma [MR]: "[|
   try (exconstraint (?? j'. j u<= j') (j u<= j'))  ;
   supunify (guniv i) (guniv j') (guniv k)  ;
   constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
   constraint (j' <: univlvl) |] ==>
  supunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: supunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (elim conjE)
  apply (subgoal_tac "guniv j <= guniv j'")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto

lemma [MR]: "
  supunify A A A"
  by (simp add: supunify_const_def)




lemma [MR]: "
    primunify A B  ==>
  infunify A B A"
  by (simp add: primunify_const_def infunify_const_def)

lemma [MR]: "[|
    primunify A1 A2 ;
    infunify (guniv k1) (guniv k2) (guniv k')  ;
    constraint (k1 <: univlvl)  ;  constraint (k2 <: univlvl)  ;  constraint (k' <: univlvl)  ;
    !! x. infunify B1(x) B2(x) B(x)  ;
    !! x. x synthty A1 ==> B1(x) <: guniv k1  ;
    !! x. x synthty A2 ==> B2(x) <: guniv k2  |]  ==>
  infunify (PRODu k1 x:A1. B1(x)) (PRODu k2 x:A2. B2(x)) (PRODu k' x:A1. B(x))"
  apply (simp add: primunify_const_def infunify_const_def constraint_const_def constraint_typing_def synthty_const_def)
  apply (elim conjE)
  apply (drule guniv_subD2, assumption+)+
  apply (cases "(PRODu k' x:A2. B(x)) = 0")
    apply simp
  apply (drule nontriv_produ_means_good_args, elim conjE)
  apply (rule conjI)
  by (rule weaken_produ, blast+)+


(* NB: special treatment of the i <= j, j <= i cases is necessary to avoid infinite
   generation of guniv k constraints via typing constraint merge rule *)
lemma [MR]: "[|
    freshFOunifvar k  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (k <: univlvl)  ;  constraint (inflvl k)  ;
    constraint (k u<= i)  ;  constraint (k u<= j)  |] ==>
  infunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univ_leq_def univlvl_def)
  apply (rule conjI)
  by (rule guniv_sub, assumption+)+

(* TODO(correctness): does this rely on persistent uniqueness of i'? *)
lemma [MR]: "[|
    try (exconstraint (?? i'. i' u<= i) (i' u<= i))  ;
    try (intensionally_inequal (i', i))  ;
    infunify (guniv i') (guniv j) (guniv k)  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (i' <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (elim conjE)
  apply (subgoal_tac "guniv i' <= guniv i")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto

(* TODO(correctness): does this rely on persistent uniqueness of j'? *)
lemma [MR]: "[|
    try (exconstraint (?? j'. j' u<= j) (j' u<= j))  ;
    try (intensionally_inequal (j', j))  ;
    infunify (guniv i) (guniv j') (guniv k)  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (j' <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (elim conjE)
  apply (subgoal_tac "guniv j' <= guniv j")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto


(*lemma [MR]: "[|
    try (exconstraint  (?? j'. j' u<= j) (j' u<= j))  ;
    try (exconstraint (inflvl j'))  ;
    constraint (j' u<= i)  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (j' <: univlvl) |] ==>
  infunify (guniv i) (guniv j) (guniv j')"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (rule conjI)
  apply (rule guniv_sub, assumption+)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint  (?? i'. i' u<= i) (i' u<= i))  ;
    try (exconstraint (inflvl i'))  ;
    constraint (i' u<= j)  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (i' <: univlvl) |] ==>
  infunify (guniv i) (guniv j) (guniv i')"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (rule conjI)
  apply (rule guniv_sub, assumption+)
  by (rule guniv_sub, assumption+)
*)

lemma [MR]: "[|
    try (exconstraint (inflvl i))  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (i u<= j)  |] ==>
  infunify (guniv i) (guniv j) (guniv i)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint (inflvl j))  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (j u<= i)  |] ==>
  infunify (guniv i) (guniv j) (guniv j)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint  (inflvl i)) ;
    try (exconstraint  (inflvl j)) ;
    primunify i j  |] ==>
  infunify (guniv i) (guniv j) (guniv i)"
  by (simp add: infunify_const_def primunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)

lemma [MR]: "[|
    try (exconstraint  (i u<= j)) ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv i)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint  (j u<= i)) ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv j)"
  apply (simp add: infunify_const_def constraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "
  infunify A A A"
  by (simp add: infunify_const_def)




lemma [MR]: "
    primunify A B  ==>
  infmetaunify A B A"
  by (simp add: infmetaunify_const_def primunify_const_def conjunctionI)

lemma [MR]: "
    infunify A B C ==>
  infmetaunify (% x. Trueprop(x : A)) (% x. Trueprop(x : B)) (% x. Trueprop(x : C))"
  apply (simp add: infmetaunify_const_def infunify_const_def)
  apply (rule conjunctionI)
  by auto


lemma [MR]: "[|
    primunify A1 A2  ;  
    !! x. infmetaunify B1(x) B2(x) B(x) |] ==>
  infmetaunify mPi(A1, B1) mPi(A2, B2) mPi(A1, B)"
  apply (simp add: infmetaunify_const_def primunify_const_def mPi_def all_conjunction)
  apply (erule conjunctionE)
  apply (rule conjunctionI)
  apply (drule meta_spec)+
  apply (rule_tac P="PROP B(xa, x(xa))" and Q="PROP B1(xa, x(xa))" in meta_mp, assumption)
  apply (rule_tac P="PROP A2(xa)" and Q="PROP B(xa, x(xa))" in meta_mp, assumption, assumption)
  apply (rule_tac P="PROP B(xa, x(xa))" and Q="PROP B2(xa, x(xa))" in meta_mp, assumption)
  by (rule_tac P="PROP A2(xa)" and Q="PROP B(xa, x(xa))" in meta_mp, assumption, assumption)

lemma [MR]: "
  infmetaunify A A A"
  by (simp add: infmetaunify_const_def primunify_const_def conjunctionI)





lemma [MR]: "
    primunify A B  ==>
  subunify A B"
by (simp add: primunify_const_def subunify_const_def)

(* TODO(opt?): similiar optimizations as in infunify useful? *)
lemma [MR]: "[|
    constraint (i <: univlvl)  ;
    constraint (j <: univlvl)  ;
    constraint (i u<= j)  |]  ==>
  subunify (guniv i) (guniv j)"
  apply (simp add: subunify_const_def constraint_const_def constraint_typing_def univ_leq_def univlvl_def)
  by (rule guniv_sub)

lemma [MR]: "[|
    primunify A1 A2  ;
    subunify (guniv k1) (guniv k2)  ;
    constraint (k1 <: univlvl)  ;  constraint (k2 <: univlvl)  ;
    !! x. subunify B1(x) B2(x)  ;
    !! x. x synthty A2 ==> B2(x) <: guniv k2  |] ==>
  subunify (PRODu k1 x:A1. B1(x)) (PRODu k2 x:A2. B2(x))"
  apply (simp add: subunify_const_def primunify_const_def constraint_const_def constraint_typing_def synthty_const_def)
  apply (drule guniv_subD2, assumption+)
  by (rule weaken_produ, assumption+)


lemma [MR]: "
  subunify A A"
  by (simp add: subunify_const_def)
  



lemma [MR]: "
    primunify A B  ==>
  submetaunify A B"
  by (simp add: submetaunify_const_def primunify_const_def)

lemma [MR]: "
    subunify A B ==>
  submetaunify (% x. Trueprop(x : A)) (% x. Trueprop(x : B))"
  apply (auto simp add: submetaunify_const_def subunify_const_def)
  proof -
    assume subH:"A <= B" fix x assume xA: "x : A" show "x : B"
    by (rule subsetD[OF subH xA])
  qed


lemma [MR]: "[|
    submetaunify A2 A1  ;  
    !! x. submetaunify B1(x) B2(x) |] ==>
  submetaunify mPi(A1, B1) mPi(A2, B2)"
  by (simp add: submetaunify_const_def primunify_const_def mPi_def)

lemma [MR]: "
  submetaunify A A"
  by (simp add: submetaunify_const_def)




definition
  deepexconstraint_const :: "prop => prop => prop" ("deepexconstraint _ _") where
  [MRjud 1 1]: "deepexconstraint_const (PROP P, PROP Q) == PROP Q"


definition "deepexconstraint_lookup = 0"

lemma [MR]: "[|
    exconstraint (?? A. x <: A) (x <: A)  |] ==>
  deepexconstraint (?? A. x <: A) (x <: A)"
  by (simp add: deepexconstraint_const_def ex_constraint_const_def)
lemma [MR]: "[|
    exconstraint (?? P. x <:: P) (x <:: P)  |] ==>
  deepexconstraint (?? P. x <:: P) (x <:: P)"
  by (simp add: deepexconstraint_const_def ex_constraint_const_def)

(* eases type synthesis of elaborated terms by using existing univlvls via unknown_univlvl_constraint *)
lemma [MR]: "[|
    try (x synthty A)  |] ==>
  deepexconstraint (?? A. x <: A) (x <: A)"
  by (simp add: synthty_const_def deepexconstraint_const_def try_const_def constraint_typing_def)

(* TODO(correctness): general MPI treatment necessary? *)
lemma [MR]: "[|
    deepexconstraint (?? A. f <:: A) (f <:: (MssPI x:A. B(x)))  ;
    x synthty A'  ;  subunify A' A  |] ==>
  deepexconstraint (?? A. f(x) <: A) (f(x) <: B(x))"
  by (auto simp add: deepexconstraint_const_def synthty_const_def mPi_def subunify_const_def
    constraint_meta_typ_def constraint_typing_def)
lemma [MR]: "[|
    deepexconstraint (?? A. f <:: A) (f <:: (MsPI x:A. P(x)))  ;
    x synthty A'  ;  subunify A' A  |] ==>
  deepexconstraint (?? A. f(x) <:: A) (f(x) <:: P(x))"
  apply (simp add: deepexconstraint_const_def synthty_const_def mPi_def subunify_const_def
    constraint_meta_typ_def)
  by (drule subsetD)
  


definition
  unknown_typing_foconstraint_for where
  [MRjud 1 1]: "unknown_typing_foconstraint_for(x, A) == (x <: A)"
definition
  unknown_typing_constraint_for where
  [MRjud 1 1]: "unknown_typing_constraint_for(x, A) == (x <: A)"
definition
  unknown_univ_constraint_for where
  [MRjud 1 1]: "unknown_univ_constraint_for(A, i) == (A <: guniv i & i <: univlvl)"


(* NB: in the case of atomic terms that are opqapue to type inference,
     fresh unifvar A does not depend on local context.
     This is essential in order to avoid a context-dependent typing constraint for x,
     which should be a free variable so does not depend on the context.
       We could probably avoid this by providing a deprestr constraint
     simplification rule deprestr x A  ==> x <: A  for atoms x. *)
lemma [MR_unchecked]: "[|
    freshFOunifvar i  ;  constraint (i <: univlvl)  ;
    freshUNLIFTEDunifvar A  ;
    constraint (A <: guniv i)  ;  x <: A |] ==>
  unknown_typing_foconstraint_for (x, A)"
  by (simp add: unknown_typing_foconstraint_for_def constraint_const_def)

lemma [MR]: "
    try (deepexconstraint (?? A. x <: A) (x <: A))  ==>
  unknown_typing_foconstraint_for (x, A)"
  by (simp add: unknown_typing_foconstraint_for_def try_const_def deepexconstraint_const_def)



lemma [MR_unchecked]: "[|
    freshunifvar A  ;  freshFOunifvar i  ;  constraint (i <: univlvl)  ;
    A <: guniv i  ;  x <: A |] ==>
  unknown_typing_constraint_for (x, A)"
  by (simp add: unknown_typing_constraint_for_def constraint_const_def
    constraint_const_def)

lemma [MR]: "
    try (deepexconstraint (?? A. x <: A) (x <: A))  ==>
  unknown_typing_constraint_for (x, A)"
  by (simp add: unknown_typing_constraint_for_def try_const_def deepexconstraint_const_def)



(* NB: important to make i a first-order unification variable
    without dependencies before context dependency analysis for (A <: guniv i) constraint.
    Since A may be composite, we don't issue constraint (A <: guniv i) directly, but simplify
    right away. *)
definition "unknown_univ_constraint_for_fresh == 0"

lemma [MR_unchecked]: "[|
    freshFOunifvar i  ;  constraint (i <: univlvl)  ;  A <: guniv i  |] ==>
  unknown_univ_constraint_for (A, i)"
  by (simp add: unknown_univ_constraint_for_def constraint_const_def
    constraint_const_def)


lemma [MR]: "[|
    try (deepexconstraint (?? U. A <: U) (A <: guniv i))  ;
    constraint (i <: univlvl)  |] ==>
  unknown_univ_constraint_for (A, i)"
  by (simp add: unknown_univ_constraint_for_def try_const_def deepexconstraint_const_def constraint_const_def)






(* low prio rule for type inference of free variable x *)
(* NB: we don't need a synthty rule for variables, because these
  synthty judgement applications are declared in context already by elab_infer *)
(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts
   in wellformedness checking *)
lemma [MR_unchecked]: "
    unknown_typing_foconstraint_for (x, A) ==>
  x elabto x : A"
 unfolding elabjud_def unknown_typing_foconstraint_for_def constraint_typing_def .


(* NB: in the case of non-atomic terms that are opaque to type inference
    we use general non-first-order constraints, as f or x might contain local fixes.
   We don't have to treat the (% x. f(x)) case because elaboration creates sets *)
lemma [MR_unchecked]: "
    unknown_typing_constraint_for (f(x), A) ==>
  f(x) elabto f(x) : A"
 unfolding elabjud_def constraint_typing_def unknown_typing_constraint_for_def .



(* NB: subunify premises left as is in synthesis rule. (can lead to u<= constraint generation) *)
(* NB: It is important to create same context for B(x) universe constraint generation as it
    would be in (PRODu k x:A. B(x)) type synthesis so that later lookup of
    those lifted local universe constraints has same discharged context, hence the
    (x elabto x : A) instead of a (x synthty A) assumption.  *)
lemma [elabMR_unchecked]: "[|
    t1 elabto t1' : T  ;
    freshFOunifvar k  ;  freshunifvar A  ;  freshunifvar B  ;
    primunify T (PRODu k x:A. B(x))  ;
    unknown_univ_constraint_for (A, i)  ;
    !! x. x elabto x : A  ==>  unknown_univ_constraint_for (B(x), j)  ;
    constraint (k <: univlvl)  ;  constraint (i u<= k)  ;  constraint (j u<= k)  ;
    t2 elabto t2' : A2  ;
    subunify A2 A  |] ==>
 (t1 # t2) elabto (t1' ` t2') : B(t2')"
  unfolding elabjud_def primunify_const_def subunify_const_def
    fresh_unifvar_const_def unknown_univ_constraint_for_def constraint_const_def constraint_typing_def
  apply (elim conjE)
  apply (erule produ_piE, assumption, blast, blast, blast, blast, assumption+)
  by (auto intro: apply_type)
(* generated synthesis rule (still quite involved because we need to discharge k:univlvl, A:guniv k, B:A->(guniv k)
   in order to make t1':(PRODu k x:A. B(x)) usable):
   \<lbrakk>  t1' synthty (PRODu k x:A. B(x));   unknown_univ_constraint_for(A, i);
      \<And>x. x synthty A \<Longrightarrow> unknown_univ_constraint_for(B(x), j);
      k synthty univlvl;   constraint i u<= k;   constraint j u<= k;
      t2' synthty A2;   subunify A2 A  \<rbrakk> \<Longrightarrow>
    (t1' ` t2') synthty B(t2')  *)
  


(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* TODO(refactor): can we reuse domain-annotated lam-rule below? *)
(* NB: synthesizablity of a type for B(x) depends on synthty rule that
    employs constraint lookup for type unification variables.
      It is important to create same context for B(x) type synthesis as for
    t(x) elaboration so that lookup of lifted local constraints has same
    discharged context, hence the (x elabto x : A) instead of a
    (x synthty A) assumption.  *)
(* NB: constraint (i <: univlvl) is stated after A <: guniv i, so that automatic derivation of
   synthesis rule can discover i's groundness and rewrite constraint (i <: univlvl)
   to (i synthty univlvl) *)
lemma [elabMR_unchecked]: "[|
    freshunifvar A  ;  freshFOunifvar i  ;  freshFOunifvar k  ;
    constraint (k <: univlvl)  ;
    A <: guniv i  ;  constraint (i <: univlvl)  ;
    !! x.  x elabto x : A  ==>  t(x) elabto t'(x) : B(x)  ;
    !! x.  x elabto x : A  ==>  B(x) synthty (guniv j)  ;
    constraint (j <: univlvl)  ;   constraint (i u<= k)  ;  constraint (j u<= k)  |] ==>
  (fun x. t(x)) elabto (lamu k x:A. t'(x)) : (PRODu k x:A. B(x))"
  unfolding elabjud_def univannot_lam_def constraint_const_def constraint_typing_def synthty_const_def
  apply (subst produ_pi_simp[of i j k A B], assumption+)
  by (rule lam_type)


(* NB: not elabMR registered to avoid overlapping printsas rule with rule above *)
(* NB: we provide an elaboration of lam terms instead of lamu terms, because nobody will want to
  write universe-level annotations *)
lemma [MR_unchecked]: "[|
    A elabto A' : U  ;
    freshFOunifvar i  ;  freshFOunifvar k  ;
    primunify U (guniv i)  ;
    constraint (i <: univlvl)  ;  constraint (k <: univlvl)  ;
    !! x.  x elabto x : A'  ==>  t(x) elabto t'(x) : B(x)  ;
    !! x.  x elabto x : A'  ==>  B(x) synthty (guniv j)  ;
    constraint (j <: univlvl)  ;  constraint (i u<= k)  ;  constraint (j u<= k)  |] ==>
  (lam x:A. t(x)) elabto (lamu k x:A'. t'(x)) : (PRODu k x:A'. B(x))"
  apply (simp add: elabjud_def univannot_lam_def constraint_const_def constraint_typing_def
    synthty_const_def primunify_const_def)
  apply (subst produ_pi_simp[of i j k A' B], assumption+)
  by (rule lam_type) 
(* generated synthesis rule:
  \<lbrakk> k synthty univlvl;   A synthty (guniv i);   i synthty univlvl;
    \<And> x. x synthty A \<Longrightarrow> ?t'(x) synthty B(x);
    \<And> x. x synthty A \<Longrightarrow> B(x) synthty (guniv j);
    j synthty univlvl;   constraint i u<= k;   constraint j u<= k\<rbrakk> ==>
  (lamu k x:A. t'(x)) synthty (PRODu k x:A. B(x)) *)


(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* NB: no direct matching of U, U2 against (guniv _) because U, U2 could
     be type unification variables *)
lemma PI_elab[MR_unchecked]: "[|
    A elabto A' : U  ;
    freshFOunifvar i  ;  primunify U (guniv i)  ;  constraint (i <: univlvl)  ;
    !! x.  x elabto x : A'  ==>  B(x) elabto B'(x) : U2(x)  ;
    freshFOunifvar j  ;  primunify U2 (% x. guniv j)  ;  constraint (j <: univlvl)  ;
    freshFOunifvar k  ;  constraint (k <: univlvl)  ;
    constraint (i u<= k)  ;  constraint (j u<= k)  |] ==>
  (PI x:A. B(x)) elabto (PRODu k x:A'. B'(x)) : guniv k"
  apply (simp add: elabjud_def constraint_const_def constraint_typing_def)
  by (rule produ_in_guniv)


lemma [MR] : "[|
   A' printsas A  ;
   !! x. x printsas x  ==> B'(x) printsas B(x) |] ==>
  (PRODu k x:A'. B'(x)) printsas (PI x:A. B(x))"
  by (simp add: printsasjud_def)

(* NB: x elabto x assumption avoids shortcoming of current exconstraint regarding
     the non-availability of factual consequences when discharge lifted constraint assumptions
     on constraint reuse.
       But should not matter anymore now, since we do the contextual
     discharge of constraints on-the-fly. *)
lemma [MR]: "[|
    k synthty univlvl  ;
    A synthty (guniv i)  ;  i synthty univlvl  ;
    !! x.  x elabto x : A ==> B(x) synthty (guniv j)  ;
    j synthty univlvl  ;  constraint (i u<= k)  ;  constraint (j u<= k)  |] ==>
  (PRODu k x:A. B(x)) synthty (guniv k)"
  unfolding synthty_const_def
  by (rule produ_in_guniv)


(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* FIXME?: to achieve deterministic synthesis for guniv i as for univlvl-annotated tycos,
   we would need synthesis with caching of larger level:

       [|  freshFOunifvar j  ;  constraint (j <: univlvl)  ;  constraint (i u< j)  |] ==>
       guniv i  synthty  guniv j

         try (exconstraint (?? j. inclvl i j))  ==>
       guniv i  synthty  guniv j

   always introducing fresh j is wasteful but not that bad regarding unification. *)
lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;  freshFOunifvar j  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;   constraint (i u< j)  |] ==>
  univ elabto (guniv i) : (guniv j)"
  apply (simp add: elabjud_def constraint_const_def constraint_typing_def univ_less_def univlvl_def)
  by (rule guniv_in_guniv)

(* NB: avoid overlap with printsas rule with univ elaboration rule above *)
(* FIXME?: better employ a  deprestr () i'  premise? *)
lemma [MR_unchecked]: "[|
    freshFOunifvar j  ;
    i elabto i' : A  ;  primunify A univlvl  ;
    constraint (i' <: univlvl)  ;  constraint (j <: univlvl)  ;   constraint (i' u< j)  |] ==>
  (guniv i) elabto (guniv i') : (guniv j)"
  apply (simp add: elabjud_def constraint_const_def constraint_typing_def univ_less_def univlvl_def)
  by (rule guniv_in_guniv)

lemma natelab[elabMR]: "[|
    freshFOunifvar i  ;  constraint (i <: univlvl)  |] ==>
  nat elabto nat : (guniv i)"
  unfolding elabjud_def constraint_const_def constraint_typing_def
  apply (erule univlvlE)
  by (rule nat_in_guniv)

lemma [elabMR]: "[|
    freshFOunifvar i  ;  constraint (i <: univlvl)  |] ==>
  univlvl elabto univlvl : (guniv i)"
  unfolding elabjud_def constraint_const_def constraint_typing_def
  apply (erule univlvlE)
  by (rule univlvl_in_guniv)


lemma [elabMR]: "[|
    t1 elabto t1' : T1  ;
    t2 elabto t2' : T2  ;
    supunify T1 T2 T' |] ==>
  (t1 === t2) elabto (t1' ===[T'] t2') : bool"
  unfolding bool_def elabjud_def typed_eq_def supunify_const_def
  by simp

(* NB: no printsas, synth rule for this *)
(* TODO: discharge universe level constraints that are only necessary from elaboration of A
  (after completed elaboration) *)
lemma [MR_unchecked]: "[|
    t elabto t' : A'  ;
    A elabto A'2 : U  ;
    primunify A' A'2  |] ==>
  (t annotyped A) elabto t' : A'"
  unfolding elabjud_def .

(* NB: no printsas, synth rule for this, rule for printing variables
   and variable type synthesis assumption is used instead  *)
lemma [MR_unchecked]: "[|
    freshunifvar x  ;  freshunifvar A  ;  freshFOunifvar i  ;
    A <: guniv i  ;  constraint (i <: univlvl)  ;  x <: A |] ==>
  ? elabto x : A"
 unfolding elabjud_def constraint_const_def constraint_typing_def .

(* TODO: dependent pairs based on local type inference
   or explicitly typed syntax     <t1, t2> annotyped SIGMA x:T1. T2(x)
   or mixture via partially annotyped elaboration invocation for implicit arguments
   (which loosely corresponds to purely syntactic local type inference?) *)
(* lemma [elabMR]: "[|
    t1 elabto t1' : A1  ;
    t2 elabto t2' : A2  |] ==>
    <t1, t2> elabto (<t1', t2'> typed (A1 * A2)) : A1 * A2"
  unfolding elabjud_def typed_pair_def by (rule SigmaI) *)


definition
  sum_abstract_as_const ("_ abstractas _") where
  "(t abstractas x) == t"

(* the insane unificationist approach! no synthty rule inference because
   of fancy abstract non-pattern unification constraint (abstract solution
   might be possible via structural unification) *)
lemma [MR]: "[|
    t1 elabto t1' : A  ;
    t2 elabto t2' : T2  ;
    freshunifvar B  ;
    primunify (B(t1')) T2 |] ==>
    <t1, t2> elabto (<t1', t2'> typed (SUM x:A. B(x))) : (SUM x:A. B(x))"
  by (simp add: elabjud_def primunify_rev_def typed_pair_def)
lemma [MR_unchecked]: "[|
    t1 elabto t1' : A  ;
    !! x'. x elabto x' : A ==> t2 elabto t2'(x') : B(x')  |] ==>
    <t1 abstractas x, t2> elabto (<t1', t2'(t1')> typed (SUM x:A. B(x))) : (SUM x:A. B(x))"
  by (simp add: elabjud_def typed_pair_def sum_abstract_as_const_def)
lemma [MR]: "[|
    t1' printsas t1  ;  t2' printsas t2  |] ==>
  (<t1', t2'> typed A) printsas <t1, t2>"
  by (simp add: printsasjud_def)
lemma [MR]: "[|
    t1' synthty A  ;  t2' synthty B(t1')  |] ==>
  (<t1', t2'> typed (SUM x:A. B(x))) synthty (SUM x:A. B(x))"
  by (simp add: synthty_const_def typed_pair_def)

(* FIXME:  use univ-annotated SUM and formulate elaboration rule for it *)



lemma [MR]: "
  metaelab (PROP P) (PROP P)"
  by (simp add: metaelab_const_def)

lemma [MR]: "[|
    t elabto t' : A  |] ==>
  metaelab (elabbrack(t)) (truenessbrack(t'))"
  by (simp add: metaelab_const_def)

(* TODO(feature): allow constraints over x and discharge them into P'.
     => interpretation of  LOCDISCH x jud Cs := Cs ==> jud  special form? *)
lemma [MR]: "[|
    !! x. metaelab (PROP P(x)) (PROP P'(x))  |] ==>
  metaelab (!! x. PROP P(x)) (!! x. PROP P'(x))"
  by (simp add: metaelab_const_def)

(* NB: special case instead of elaboration of standalone synthty judgements,
     to avoid dependence of A' on x *) 
lemma [MR]: "[|
    A elabto A' : U  ;
    !! x. x synthty A' ==> metaelab (PROP P(x)) (PROP P'(x))  |] ==>
  metaelab (!! x. x synthty A ==> PROP P(x))
    (!! x. x synthty A' ==> PROP P'(x))"
  by (simp add: metaelab_const_def)

lemma [MR]: "[|
    metaelab (!! x. x synthty ? ==> PROP P(x)) (PROP Q)  |] ==>
  metaelab (!!st x. (PROP P(x))) (PROP Q)"
  by (simp add: metaelab_const_def)

lemma [MR]: "[|
    metaelab (PROP P) (PROP P')  ;
    PROP P' ==> metaelab (PROP Q) (PROP Q')  |] ==>
  metaelab (PROP P ==> PROP Q) (PROP P' ==> PROP Q')"
  by (simp add: metaelab_const_def)

lemma [MR]: "[|
    metaelab (PROP P) (PROP P')  ;
    metaelab (PROP Q) (PROP Q')  |] ==>
  metaelab (PROP P &&& PROP Q) (PROP P' &&& PROP Q')"
  by (simp add: metaelab_const_def)




lemma [MR]: "[|
  !! x. (PROP P(x)) printsas (PROP P'(x))  |] ==>
  (!! x. PROP P(x)) printsas (!! x. PROP P'(x))"
  by (simp add: printsasjud_def)

(* lemma [MR]: "[|
  !! x. (PROP P(x)) printsas (PROP P'(x))  |] ==>
  (!! x. x synthty A ==> PROP P(x)) printsas (!!st x. PROP P'(x))"
  by (simp add: printsasjud_def) *)

lemma [MR]: "[|
    (PROP P) printsas (PROP P')  ;
    (PROP Q) printsas (PROP Q')  |] ==>
  (PROP P ==> PROP Q) printsas (PROP P' ==> PROP Q')"
  by (simp add: printsasjud_def)

lemma [MR]: "[|
    PROP P printsas PROP P'  ;
    PROP Q printsas PROP Q'  |] ==>
  (PROP P &&& PROP Q) printsas (PROP P' &&& PROP Q')"
  by (simp add: printsasjud_def)

lemma [MR]: "[|
    t printsas t'  |] ==>
  Trueprop(truenessbrack(t)) printsas Trueprop(elabbrack(t'))"
  by (simp add: printsasjud_def)

(* TODO(feature): printing rule for  (x <: A) ==> PROP P
     where x <: A is only printed if x occurs in printing of P *)
lemma [MR]: "[|
    A printsas A'  |] ==>
  Trueprop(x <: A) printsas Trueprop(x <: A')"
 by (simp add: printsasjud_def)  



(* constraint simplification *)

lemma [MR]: "[|
    deprestr t A  ;  constraint (t <: A)  |] ==>
  t <: A"
  by (simp add: constraint_const_def)

lemma [MR]: "[|
    deprestr t A  ;  constraint (t <:: A)  |] ==>
  t <:: A"
  by (simp add: constraint_const_def)

lemma [MR]: "[|
    try (deepexconstraint (?? B. t <: B) (t <: B))  ;
    subunify B A  |] ==>
  t <: A"
  by (auto simp add: try_const_def deepexconstraint_const_def
    subunify_const_def constraint_typing_def)


lemma [MR]: "[|
    try (deepexconstraint (?? B. t <:: B) (t <:: B))  ;
    submetaunify B A  |] ==>
  t <:: A"
  by (simp add: try_const_def deepexconstraint_const_def
    submetaunify_const_def constraint_meta_typ_def)


lemma [MR]: "[|
    try (t :> A')  ;  subunify A' A  |] ==>
  t <: A"
  by (auto simp add: syn_constraint_typing_def constraint_typing_def try_const_def subunify_const_def)
lemma [MR]: "[|
    try (t ::> A')  ;  submetaunify A' A  |] ==>
  t <:: A"
  by (auto simp add: syn_constraint_meta_typ_def constraint_meta_typ_def try_const_def submetaunify_const_def)




(* NB: contextual discharge relies on removal of non-relevant fixes and assms in front of
      the resulting constraints.
      Cannot be realized as an constraint simplification rule that is executed
      as part of the propagation machinery, because the fixes, assms context has to
      be gone then already.
   E.g. in
      (fun x. fun y. f x y) elabto (lam x:A. lam y:B(x). f x y) : A -> B(x) -> C(x)
   we encounter the constraint  (!! x. x:A ==> B(x) <: guniv ?i)
   which has to be simplified to  B <:: A => guniv ?i  *)
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



    

(* NB: the following rules feature a B(x) non-pattern in non-primary input position.
   They can only be applied usefully by metarec if x is a free variable, esp. a fixed one. *)
(* TODO: they are unchecked for now because variable availability analysis is
     cautious about non-pattern match against input B(x) *)


(* rules for "pseudo-contextual" discharge, mainly to calculate proper tyco constraints
  from constraints about tycos partially applied to toplevel terms, resulting from delayed unifications *)
lemma typ_constraint_pseudoctxt_discharge_MR[MR_unchecked]: "[|
     unknown_typing_foconstraint_for (x, A)  ;
     f <:: MsPI x : A. B(x)  |] ==>
   f(x) <:: B(x)"
  unfolding try_const_def unknown_typing_foconstraint_for_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def 
  by simp

lemma typ_constraint_pseudoctxt_discharge_MR2[MR_unchecked]: "[|
     unknown_typing_foconstraint_for (x, A)  ;
     f <:: MssPI x : A. B(x) |] ==>
   f(x) <: B(x)"
  unfolding try_const_def unknown_typing_foconstraint_for_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp

(* NB: necessary because execution of delayed unifications can introduce ZF-applications in constraints *)
(* TODO(refactor): PRODu introduction shared with application rule *)
lemma typ_constraint_pseudoctxt_zfdischarge[MR_unchecked]: "[|
     unknown_typing_foconstraint_for (x, A)  ;
     A synthty (guniv i)  ;  i synthty univlvl  ;
     freshFOunifvar k  ;  constraint (k <: univlvl)  ;
     !! x.  x elabto x : A  ==>  B(x) synthty (guniv j)  ;  j synthty univlvl  ;
     constraint (i u<= k)  ;  constraint (j u<= k)  ;
     f <: PRODu k x:A. B(x) |] ==>
   f ` x <: B(x)"
  unfolding try_const_def elabjud_def unknown_typing_foconstraint_for_def constraint_const_def
    constraint_typing_def syn_constraint_typing_def  synthty_const_def
  apply (erule produ_piE, assumption+)
  by simp


lemma typ_constraint_ctxt_discharge_MR[MR_unchecked]: "[|
     try (x :> A)  ;
     f <:: MsPI x : A. B(x)  |] ==>
   f(x) <:: B(x)"
  unfolding try_const_def elabjud_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp

lemma typ_constraint_ctxt_discharge_MR2[MR_unchecked]: "[|
     try (x :> A)  ;
     f <:: MssPI x : A. B(x) |] ==>
   f(x) <: B(x)"
  unfolding try_const_def elabjud_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp

(* NB: necessary because execution of delayed unifications can introduce ZF-applications in constraints *)
(* TODO(refactor): PRODu introduction shared with application rule *)
lemma typ_constraint_ctxt_zfdischarge[MR_unchecked]: "[|
     try (x :> A)  ;
     A synthty (guniv i)  ;  i synthty univlvl  ;
     freshFOunifvar k  ;  constraint (k <: univlvl)  ;
     !! x.  x elabto x : A  ==>  B(x) synthty (guniv j)  ;  j synthty univlvl  ;
     constraint (i u<= k)  ;  constraint (j u<= k)  ;
     f <: PRODu k x:A. B(x) |] ==>
   f ` x <: B(x)"
  unfolding try_const_def elabjud_def constraint_typing_def syn_constraint_typing_def
    synthty_const_def constraint_const_def
  apply (erule produ_piE, assumption+)
  by simp




(* NB: useful when a discharged constraint F <:: A => B gets instantiated with F:=(%x. ...)
   due to delayed structural unifications *)
lemma [MR]: "[|
    !! x. x :> A ==> f(x) <:: B(x)  |] ==>
  (% x. f(x)) <:: (MsPI x:A. B(x))"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def .
lemma [MR]: "[|
    !! x. x :> A ==> f(x) <: B(x)  |] ==>
  (% x. f(x)) <:: (MssPI x:A. B(x))"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def constraint_typing_def .

(* useful for discharge of later projective instantations *)
lemma [MR]: "
     t <:: B ==>
  (% x. t) <:: A => B"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def
  proof - assume H: "PROP B(t)" fix x assume "x : A" show "PROP B(t)" by (rule H) qed
lemma [MR]: "
     t <: B ==>
  (% x. t) <:: A => B"
  unfolding mPi_def constraint_typing_def constraint_meta_typ_def syn_constraint_typing_def
  proof - assume H: "t : B" fix x assume "x : A" show "t : B" by (rule H) qed


(* delayed unifications can introduce lamus into constraints, but should be rare *)
lemma [MR]: "[|
    A synthty (guniv i)  ;  !! x. x synthty A ==> B(x) synthty (guniv j)  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;  constraint (k <: univlvl)  ;
    constraint (i u<= k)  ;  constraint (j u<= k)  ;
    !! x. x :> A ==> t(x) <: B(x)  |] ==>
  (lamu k x:A. t(x)) <: (PRODu k x:A. B(x))"
  unfolding univannot_lam_def constraint_typing_def syn_constraint_typing_def constraint_const_def synthty_const_def
  apply (subst produ_pi_simp[of i j k A B], assumption+)
  by (rule lam_type)


(* NB: for unlifting of univlvls (they can become lifted due to
  delayed structural unifications).
  Not necessary anymore because of fovars concept *)
(* lemma [MR]: "[|
    freshunifvar f'  ;
    primunify (% x. f(x)) (% x. f')  ;
    f' <: univlvl  |] ==>
  f(x) <: univlvl"
  by (simp add: primunify_const_def) *)
  


lemma [MR]: "
    constraint (i <: univlvl) ==>
  nat <: guniv i"
  unfolding constraint_const_def constraint_typing_def
  apply (erule univlvlE)
  by (rule nat_in_guniv)
lemma [MR]: "
    constraint (i <: univlvl) ==>
  univlvl <: guniv i"
  unfolding constraint_const_def constraint_typing_def
  apply (erule univlvlE)
  by (rule univlvl_in_guniv)


(* FIXME: why unknown_univ_constraint_for instead of synthesis of univ of A?! *)
lemma [MR]: "[|
    constraint (i <: univlvl)  ;   constraint (k <: univlvl)  ;
    constraint (k u<= i)  |] ==>
  (PRODu k x:A. B(x)) <: guniv i"
  unfolding constraint_const_def constraint_typing_def syn_constraint_typing_def
     univ_leq_def unknown_univ_constraint_for_def
  apply (rule guniv_cumul[of k i])
  apply (blast dest: univlvlDnat)+
  by (rule produ_in_guniv[of k A B])

(* NB: i,j are always universe level variables, so the constraint (i u< j) cannot really
   be solved right now and can at best be refuted if i = j *)
lemma [MR]: "[|
    constraint (i <: univlvl) ;  constraint (j <: univlvl)  ;  constraint (i u< j) |] ==>
  guniv i <: guniv j"
  unfolding constraint_const_def constraint_typing_def univ_less_def
  apply (elim univlvlE)
  by (rule guniv_in_guniv)



schematic_lemma "(PRODu k1 x:A. PRODu k2 y:B(x). C(x, y)) <: guniv i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops






(*lemma constraint_typ_apply: "
  [|  x elabto x' : A  ;  g <: (PRODu k x:A. B(x))  |] ==> g ` x' <: B(x')"
  unfolding constraint_typing_def elabjud_def
  apply (erule produ_piE)
  by (rule apply_type) *)

(* could be useful for more general type constraint context discharge *)
(*ML {*
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
              val (prf_res, ctxt5) = MetaRec.mps_match_on_thm_prf @{thm constraint_typ_apply}
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
*}*)









ML {*
  fun elab ctxt t =
    CumulTiming.print_block "elab" ["metarec_no_constraintsimp", "chr_constraint_simplification",
      "termhg_trancl", "metarec_constraint_simp", "metarec_structural_unifications", "replay_prf",
      "add_assm_terms_internal", "reconsider_instantiated_constraints",
      "metarec_constraint_simp_instantiated_contraints"]
    (fn () =>
    exception_trace (fn () =>
      let
        val _ = tracing ("====== starting elaboration of "^Syntax.string_of_term ctxt t
          ^" ========")
        val (th, [elab_t, _]) = MetaRec.metarec_fully_discharged ctxt ElabRuleProcessing.elabjud_n (t, [])
        val _ = tracing ("====== finished elaboration of "^Syntax.string_of_term ctxt t
          ^" to "^Syntax.string_of_term ctxt elab_t^" ========")

        val (_, [t']) = MetaRec.metarec_fully_discharged ctxt ElabRuleProcessing.printsasjud_n
          (elab_t, [])
        val _ =
          if t aconv t' then ()
          else warning ("elab: print-translated elaboration is not original input:\n  "
            ^Syntax.string_of_term ctxt t
            ^"\n  "^Syntax.string_of_term ctxt t')
      in
        th
      end))

  
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

ML {*  elab @{context} @{term "f # x"}  *}


(* tests of derivations with occurences of schematic variables in goals *)
schematic_lemma "(PRODu ?k x:?XT(z). ?YT(z,x)) <: guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(PRODu ?k x:?XT_(z). ?YT(z,x)) <: guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(PRODu ?k x:?XT3434(z). ?YT2435(z,x)) <: guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(% z. PRODu ?k x:?A(z). ?B(z,x)) <:: ?A2 => guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops
schematic_lemma "(% z. PRODu ?k x:?A(z). ?B(z,x)) <:: C => guniv ?i"
  apply (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})
  oops


setup {*
Context.theory_map (MetaRec.set_trace_depth (MetaRec.TraceDepth {
  rule_trace_level_depth = 3, rule_trace_max_levels = 2, msg_trace_depth = 3}))
*}

(* NB: employs structural unification for  ?B(x) == (PROD y:?C. ?D(y)),  i.e.
     ?B := (% x. PROD y:?C'(x). ?D'(x, y)),   ?C := ?C'(t)    ?D := ?D'(t) *)
ML {*  elab @{context} @{term "f # x # y"}  *}

ML {*  elab @{context} @{term "f # x # y # z"}  *}

ML {*  elab @{context} @{term "f # x # x # x"}  *}

ML {*  elab @{context} @{term "f # x # x # x # x"}  *}


ML {*
  val fixes = Variable.dest_fixes @{context} |> map snd
  val constraints = Variable.constraints_of @{context} |> fst |> Vartab.dest |> filter (fn ((n, ix), _) => ix = ~1)
            |> map (fn ((n, _), T) => Free(n,T) |> Syntax.string_of_term @{context})
*}


ML {*  elab @{context} @{term "(fun x. bla # x)"}  *}
ML {*  elab @{context} @{term "(fun f. fun x. bla # x)"}  *}

ML {*  elab @{context} @{term "(fun x. fun y. blub # x # y)"}  *}
ML {*  elab @{context} @{term "(fun x. fun y. blub # y # x)"}  *}

ML {*  elab @{context} @{term "(fun f. fun x. blub(f, x))"}  *}

ML {*  elab @{context} @{term "(fun f. fun x. blub(x, f))"}  *}
ML {*  elab @{context} @{term "(fun f. fun x. bla(x))"}  *}



ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}

ML {*  elab @{context} @{term "(fun f. fun g. fun x. f # (g # x))"}  *}

(* minor FIXME: "non-trivial" composite unification variable dependencies don't seem useful.
  Prune in unification right away? *)
(* FIXME: pseudo-contextual discharge does not handle application to abstraction *)
ML {*  elab @{context} @{term "f # (fun g. g # x) # y"}  *}

ML {*  elab @{context} @{term "(fun f. f # (fun y. (fun x. (fun g. g # x)) # y))"}  *}



(* FIXME?: abstracted universe level annotations lead to unsatisfiable first-order constraints
     for universe levels that are used in subterms.
   we may not unlift them in that case or we need local constraint discharge.
   This should be resolvable by careful local type inference? *)
(* ML {*  elab @{context} @{term "(lam i:univlvl. lam x:guniv i. fun f. f # x)"} *} *)

(* but this works *)
ML {*  elab @{context} @{term "(lam x:guniv i. fun f. f # x)"} *}



(* fails with occurs check *)
ML {*  elab_with_expected_error "unification of * and * failed" @{context} @{term "(fun x. x # x)"} *}











definition
 universe_inconsistency where
 [MRjud 1 0]: "universe_inconsistency(x) == False"


(* NB: we introduce (sometimes) artificial dependencies on univlvl constraints
   for all univlvl related CHRs because of the following: 
     univlvl constraint for intermediate univlvl vars are sometimes not derivationally 
   needed in constraint minimization of initial constraints, because transitivity chains
   using inequations with intermediate univlvl vars do not need their univlvl constraints,
   so are correctly left out.
     Later problem would be that hidden univlvl discharge optimization assumes all univlvl vars
   have univlvl constraints. This makes derivations generally slightly slower due to processing
   of useless premises and another possibility would be to include univlvl constraints into
   the univlvl inequation definition. *)
 
(* relevant for constraint subsumption of  i u<= j *)
lemma [constraint_propag_rule]: "[| constraint (i <: univlvl)  ;  constraint (j <: univlvl) |] ==>
    i u< j ==> i u<= j"
  by (rule univ_leq_from_less)
  

lemma [constraint_propag_rule]: "[| constraint (i <: univlvl) ; constraint (j <: univlvl) ; constraint (k <: univlvl) |] ==>
    i u< j &&& j u< k ==> i u< k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.lt_trans)

lemma [constraint_propag_rule]: "[| constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;  constraint (k <: univlvl) |] ==>
    i u< j &&& j u<= k ==> i u< k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.lt_trans2)

lemma [constraint_propag_rule]: "[| constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;  constraint (k <: univlvl) |] ==>
    i u<= j &&& j u< k ==> i u< k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.lt_trans1)

(* NB: we avoid looping on  i u<= i &&& i u<= i ==> i u<= i
   FIXME: was looping just a bug here?
     simp rule for i u<= i should have priority. *)
lemma [constraint_propag_rule]: "
  [| try (intensionally_inequal (i, j))  ;
     constraint (i <: univlvl)  ;  constraint (j <: univlvl) ;  constraint (k <: univlvl)  |] ==>
  i u<= j &&& j u<= k ==> i u<= k"
  unfolding univ_less_def univ_leq_def
  apply (erule conjunctionE) by (rule Ordinal.le_trans)

lemma [constraint_simp_rule]: "universe_inconsistency(0) ==> i u< i"
  by (simp add: universe_inconsistency_def)+

  (* NB: no try around unify. corresponds to CHR  (i <= j , j <= i) == (i = j) *)
  (* TODO(opt): we could make this rule no_re_eval_on_head_reconsideration *)
lemma [constraint_simp_rule]: "[| primunify i j  ;  constraint (i <: univlvl)  ;  constraint (j <: univlvl)  |] ==>
  (i u<= j &&& j u<= i)"
  unfolding univ_less_def univ_leq_def univlvl_def
  apply (rule Pure.conjunctionI)
  by (simp add: primunify_const_def constraint_const_def constraint_typing_def)+

  (* FIXME: actually a specialization of the rule above for j := i,
     so should be unecessary as a simp CHR, in particular because
     only first matching simp CHR is executed on a constraint combination? *)
  (* TODO(opt): we could make this rule no_re_eval_on_head_reconsideration *)
lemma [constraint_simp_rule]: "constraint (i <: univlvl) ==> i u<= i"
  unfolding univ_less_def univ_leq_def univlvl_def
  by (simp add: constraint_const_def constraint_typing_def)





lemma [MR]: "i <: univlvl ==> i u<= i"
  unfolding univ_less_def univ_leq_def univlvl_def
  by (simp add: constraint_const_def constraint_typing_def)





ML {*
  fun test_chr_simp ctxt0 Cs =
    let
      val ctxt0 = ctxt0 |> fold Variable.declare_term Cs
        |> Variable.add_fixes_direct ([] |> fold Term.add_free_names Cs)
      val ctxt = ctxt0
        |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt0))
        |> Context.proof_map (MetaRec.map_constraints_in_run_state (K (Cs
             |> map (fn C => (C, MetaRec.ConstraintTrace [], MetaRec.ActiveConstraint)))))
        |> MetaRec.put_concl_in_lin_ctxt @{prop "True"}
      val ((Cs', implied_Cs), ctxt2) = MetaRec.chr_constraint_simplification true ctxt
      val cert = cterm_of (Proof_Context.theory_of ctxt0)
    in
      (Cs' |> map (fst #> cert), map (fst #> cert) implied_Cs)
    end
  *}



ML {*
  val res = test_chr_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"},
     @{prop "i u< j"}, @{prop "j u< k"}, @{prop "i u< k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_chr_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"}, @{prop "l <: univlvl"},
     @{prop "i u< j"}, @{prop "j u< k"}, @{prop "k u< l"}, @{prop "i u< l"}, @{prop "j u< l"}]
  val _ = if length (snd res) = 2 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_chr_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"},
     @{prop "i u< j"}, @{prop "j u< k"}, @{prop "i u<= k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_chr_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"},
     @{prop "i u<= j"}, @{prop "j u< k"}, @{prop "i u< k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_chr_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"}, @{prop "l <: univlvl"},
     @{prop "i u< j"}, @{prop "j u<= k"}, @{prop "k u< l"}, @{prop "i u< l"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}








definition
  "typing_constraint_merge = 0"
definition
  tracing_if_different where
  [MRjud 3 0]: "tracing_if_different(t1, t2, msg) == True"

lemma [MR]: "
    tracing(msg) ==>
  tracing_if_different(t1, t2, msg)"
  by (simp add: tracing_if_different_def)

lemma [MR]: "
  tracing_if_different(t, t, msg)"
  by (simp add: tracing_if_different_def)

(* NB: these typing constraint merge rules are necessary even with direct sharing of typing
     constraints for term variables, because type unification variables can become identified *)
(* NB: these can be considered constraint simp rules because there are no
   propagation rules that process t <: A, t <:: A constraints further *)
(* NB: no reevaluation if A' is instantiated further constitutes a performance optimization,
    since A' in t <: A' constraints will only ever be <=-refined during constraint simplification *)
lemma [constraint_simp_rule all_matches no_re_eval_on_head_reconsideration symmetric irreflexive]: "[|
    infunify A A2 A'  ;  constraint (t <: A')  |] ==>
  t <: A &&& t <: A2"
    apply (simp add: constraint_const_def infunify_const_def conjunctionI constraint_typing_def)
    by (rule conjunctionI) auto
lemma [constraint_simp_rule all_matches no_re_eval_on_head_reconsideration symmetric irreflexive]: "[|
    infmetaunify A A2 A'  ;  constraint (t <:: A')  |] ==>
  t <:: A &&& t <:: A2"
    apply (simp add: constraint_const_def infmetaunify_const_def constraint_meta_typ_def)
    apply (erule conjunctionE)
    apply (rule conjunctionI)
    by auto


(* NB: CHRs reduce problem to MR clauses, instead of employing CHR chaining,
   for judgement <: which emits constraints for base cases *)
lemma umax_univlvl_Cty[MR no_rule_constraint_propag(*, constraint_simp_rule*)]:
    "i <: univlvl ==> j <: univlvl ==>
  (i umax j) <: univlvl"
  by (simp add: constraint_typing_def umax_univlvl_ty)
lemma first_univlvl_Cty[MR no_rule_constraint_propag(*, constraint_simp_rule*)]:
  "first_univlvl <: univlvl"
  by (simp add: constraint_typing_def first_univlvl_ty)
lemma usucc_univlvl_Cty[MR no_rule_constraint_propag(*, constraint_simp_rule*)]:
    "i <: univlvl ==>
  usucc(i) <: univlvl"
  by (simp add: constraint_typing_def usucc_univlvl_ty)


lemma uless_base: "i <: univlvl ==> i u< usucc(i)"
  by (simp add: univ_less_def univlvl_def constraint_typing_def usucc_def)
  (* NB: univlvl typing premises only necessary for uniformity *)
lemma uless_umax1: "i u< i' ==> i' <: univlvl ==> j <: univlvl ==> i u< i' umax j"
  apply (simp add: univ_max_def univ_less_def max_def)
  apply (rule impI) by (rule Ordinal.lt_trans2)
lemma uless_umax1_direct: "i <: univlvl ==> j <: univlvl ==> i u< usucc(i) umax j"
  by (auto intro: uless_umax1 uless_base usucc_univlvl_Cty)
lemma uless_umax2: "j u< j' ==> i <: univlvl ==> j' <: univlvl ==> j u< i umax j'"
  apply (simp add: univ_max_def univ_less_def max_def univlvl_def constraint_typing_def)
  apply (rule impI) apply (simp add: not_le_iff_lt) by (rule Ordinal.lt_trans)

lemma uleq_base: "i <: univlvl ==> i u<= i"
  apply (simp add: constraint_typing_def)
  by (blast intro: uleq_refl univlvlDnat)
lemma uleq_base_usucc: "i <: univlvl ==> i u<= usucc(i)"
  by (simp add: univ_leq_def univlvl_def constraint_typing_def usucc_def)
  (* NB: univlvl typing premises only necessary for uniformity *)
lemma uleq_umax1: "i u<= i' ==> i' <: univlvl ==> j <: univlvl ==> i u<= i' umax j"
  apply (simp add: univ_max_def univ_leq_def max_def)
  apply (rule impI) by (rule Ordinal.le_trans)
lemma uleq_umax1_direct: "i <: univlvl ==> j <: univlvl ==> i u<= i umax j"
  by (auto intro: uleq_umax1 uleq_base)
lemma uleq_umax1_direct_usucc: "i <: univlvl ==> j <: univlvl ==> i u<= usucc(i) umax j"
  by (auto intro: uleq_umax1 uleq_base_usucc usucc_univlvl_Cty)
lemma uleq_umax2: "j u<= j' ==> i <: univlvl ==> j' <: univlvl ==> j u<= i umax j'"
  apply (simp add: univ_max_def univ_leq_def max_def univlvl_def constraint_typing_def)
  apply (rule impI) apply (simp add: not_le_iff_lt) by (rule leI, rule Ordinal.lt_trans1)

thm umax_sup umax_less_sup


ML_file "hidden_univlvl_discharge.ML"



definition
  findinterm where
  [MRjud 2 1]: "findinterm(i,j,i') == (i u< i' & i' u< j)"

lemma [MR]: "[|
    freshFOunifvar intm_ul  ;  constraint (i u< intm_ul)  ;  constraint (intm_ul u< j)  ;
    constraint (intm_ul <: univlvl) |] ==>
  findinterm(i, j, intm_ul)"
  by (simp add: constraint_const_def findinterm_def)

(* NB: we rely here on the transitivy propagation of constraints that happened before this findinterm
   call from hidden universe level discharge *)
lemma [MR]: "
    try (exconstraint (?? i'. i u< i' &&& i' u< j) (i u< i' &&& i' u< j)) ==>
  findinterm(i, j, i')"
  apply (simp add: try_const_def ex_constraint_const_def findinterm_def)
  apply (erule conjunctionE)
  by (rule conjI)

definition
  "trace_outbound_univlvl_simp == 0"

lemma uleq_umax_sup_simp[constraint_simp_rule]: "
    [|  (* tracing (trace_outbound_univlvl_simp)  ; *)
        constraint (i1 u<= j)  ;  constraint (i2 u<= j)  |] ==>
  i1 umax i2 u<= j"
  unfolding constraint_const_def
  by (rule umax_sup)
  
lemma uless_umax_sup_simp[constraint_simp_rule]: "
    [|  (* tracing (trace_outbound_univlvl_simp)  ; *)
        constraint(i1 u< j)  ;  constraint (i2 u< j)  |] ==>
  i1 umax i2 u< j"
  unfolding constraint_const_def
  by (rule umax_less_sup)

lemma uleq_usucc_lhs_simp[constraint_simp_rule]: "
    [| (* tracing (trace_outbound_univlvl_simp)  ; *)
       constraint (i u< j) |] ==>
  usucc(i) u<= j"
  unfolding constraint_const_def
  by (rule univ_less_is_usucc_leq)

(* NB: reintroduces essential hidden universe level to avoid i+n algebraic universe level expressions *)
(* NB: can lead to cycles just from simp CHR apps, because the found intermediate constraint does not have to be simpler
   and might even be further simplified to the usucc(i) u< j we started from. *)
lemma uless_usucc_lhs_simp[constraint_simp_rule]: "
    findinterm(i, j, i') ==>
  usucc(i) u< j"
  unfolding constraint_const_def findinterm_def
  apply (erule conjE)
  by (rule usucc_less_from_interm)


(* FIXME? do we not want constraint_simp_rules corresponding to uleq_umax{1,2}[_direct[_usucc]] ???
   esp. to simplify trivial constaints such as   ?i u< ... umax usucc(?i) umax ...   right away *)
(* FIXME: constraint simplification rule   i u<= i  should have priority over all others, esp. to
   avoid overly complex simplifications such as
      ... ==> i1 u<= i1 umax i2
      ... ==>  i2 u<= i1 umax i2
      [|  i1 u<= i1 umax i2  ;  i2 u<= i1 umax i2  |]  ==>  i1 umax i2 u<= i1 umax i2
    *)
(* FIXME: constraint simplification rules should completely recursively simplify the constraint
   they act on based on metarec calls to corresponding judgements, instead of emitting potentially
   intermediate constraints that in turn have to be simplified. *)


ML {*
  fun opt_Trueprop_ct2t ct =
    let val t = Thm.term_of ct
    in
      if fastype_of t = @{typ prop} then t
      else FOLogic.mk_Trueprop t
    end

  fun test_univlvl_discharge ctxt0 Cs_cts expected_uninst_uls_cprops =
    let
      val Cs = Cs_cts |> map opt_Trueprop_ct2t
      val expected_uninst_uls = expected_uninst_uls_cprops
          |> map (opt_Trueprop_ct2t #> HiddenUnivlvlDischarge.dest_univlvl ctxt0 #> the)
        handle Option => error ("test_univlvl_discharge: one of the expected_uninst_ul propositions "
         ^"is not a universe level typing constraint judgement") 


      val ctxt0 = ctxt0 |> fold Variable.declare_term Cs
        |> Variable.add_fixes_direct ([] |> fold Term.add_free_names Cs)
      val ctxt = ctxt0
        |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt0))
        |> Context.proof_map (MetaRec.map_constraints_in_run_state (K
             (Cs |> map (fn C => (C, MetaRec.ConstraintTrace [], MetaRec.ActiveConstraint)))))
        |> MetaRec.put_concl_in_lin_ctxt @{prop "True"}
      val ((simpth, uninst_uls, inst_uls), _) =
        HiddenUnivlvlDischarge.calc_hidden_univlvl_discharge Cs ctxt

      val _ =
        if eq_set (op aconv) (uninst_uls, expected_uninst_uls) then ()
        else
          error ("test_univlvl_discharge: expected different universe level instantiation\n"
            ^commas (uninst_uls |> map (Syntax.string_of_term ctxt))
            ^"\nvs  "^commas (expected_uninst_uls |> map (Syntax.string_of_term ctxt)))
     in
       (simpth, uninst_uls, inst_uls |> map (pairself (cterm_of @{theory})))
     end

*}


ML {*
  test_univlvl_discharge @{context}
   [@{cpat "?i <: univlvl"}, @{cpat "?j <: univlvl"}, @{cpat "?k <: univlvl"},
    @{cpat "?i u< ?j"}, @{cpat "?i u< ?k"},
    @{cpat "?A <: guniv ?i"}]
   [@{cpat "?i <: univlvl"}]
*}

ML {*
  test_univlvl_discharge @{context}
   [@{cpat "?i <: univlvl"}, @{cpat "?j <: univlvl"}, @{cpat "?k <: univlvl"},
    @{cpat "?i u<= ?j"}, @{cpat "?i u<= ?k"},
    @{cpat "?A <: guniv ?i"}]
   [@{cpat "?i <: univlvl"}]
*}

ML {*
  test_univlvl_discharge @{context}
   [@{cpat "?i1 <: univlvl"}, @{cpat "?i2 <: univlvl"}, @{cpat "?j <: univlvl"}, @{cpat "?k <: univlvl"},
    @{cpat "?i1 u<= ?j"}, @{cpat "?i2 u<= ?j"}, @{cpat "?j u<= ?k"},
    @{cpat "?A <: guniv ?i1"}, @{cpat "?B <: guniv ?i2"}, @{cpat "?C <: guniv ?k"}]
   [@{cpat "?i1 <: univlvl"}, @{cpat "?i2 <: univlvl"}, @{cpat "?k <: univlvl"}]
*}

ML {*
  test_univlvl_discharge @{context}
   [@{cpat "?i <: univlvl"}, @{cpat "?j1 <: univlvl"}, @{cpat "?j2 <: univlvl"}, @{cpat "?k <: univlvl"},
    @{cpat "?i u<= ?j1"}, @{cpat "?i u<= ?j2"}, @{cpat "?j1 u<= ?j2"}, @{cpat "?j2 u<= ?j1"}, @{cpat "?j2 u<= ?k"},
    @{cpat "?A <: guniv ?i"}, @{cpat "?C <: guniv ?k"}]
   [@{cpat "?i <: univlvl"}, @{cpat "?k <: univlvl"}]
*}

ML {*
  test_univlvl_discharge @{context}
   [@{cpat "?i <: univlvl"}, @{cpat "?j <: univlvl"}, @{cpat "?k <: univlvl"},
    @{cpat "?i u< ?k"}, @{cpat "?j u< ?k"},
    @{cpat "?A <: guniv ?i"}]
   [@{cpat "?i <: univlvl"}]
*}

ML {*
  test_univlvl_discharge @{context}
   [@{cpat "?i <: univlvl"}, @{cpat "?j <: univlvl"}, @{cpat "?k <: univlvl"},
    @{cpat "?i u< ?k"}, @{cpat "?j u< ?k"},
    @{cpat "?A <: guniv ?i"}, @{cpat "?B <: guniv ?j"}]
   [@{cpat "?i <: univlvl"}, @{cpat "?j <: univlvl"}]
*}

setup {*
  HiddenUnivlvlDischarge.setup
*}


definition
  metawitnessuniv_const ("metawitnessuniv _ _") where
  [MRjud 1 1]: "metawitnessuniv A t == PROP A(t)"
definition
  witnessuniv_const ("witnessuniv _ _") where
  [MRjud 1 1]: "witnessuniv A t == t : A"

(* TODO: synthproc that checks whether x is a variable that is not contained
    in "the proposition" (registered during constraint simplification)
    (specification of nonhiddenness would be even better:
       in t elabto t' : A' only the variables in t' and A' are nonhidden) *)
definition
  hiddenvar_const ("hiddenvar _") where
  [MRjud 1 0]: "hiddenvar x == True"


lemma [MR]: "constraint (i <: univlvl) ==>
  witnessuniv (guniv i) 0"
  apply (simp add: witnessuniv_const_def constraint_const_def
    constraint_typing_def)
  apply (erule univlvlE)
  by (rule empty_in_guniv)

(* NB: we are not using lamu because the synthesized term will only be used in the
  instantiation of hidden variables *)
lemma [MR]: "[|
    !! x. witnessuniv (B(x)) t |] ==>
  witnessuniv (PROD x : A. B(x)) (lam x:A. t)"
  apply (simp add: witnessuniv_const_def)
  by (rule lam_type)


lemma [MR]: "[|
    !! x. witnessuniv (B(x)) t |] ==>
  metawitnessuniv (MssPI x : A. B(x)) (% x. t)"
  by (simp add: witnessuniv_const_def metawitnessuniv_const_def mPi_def)

lemma [MR]: "[|
    !! x. metawitnessuniv (B(x)) t |] ==>
  metawitnessuniv (MsPI x : A. B(x)) (% x. t)"
  by (simp add: metawitnessuniv_const_def mPi_def)


(* NB: these are not truly constraint simp rules because the x <: A, x <:: A constraints
   should still be available to other propagation rules *)
lemma (*[constraint_simp_rule]:*) "[|
    try (hiddenvar x)  ;  try (witnessuniv A t)  ;  primunify x t  |] ==>
  x <: A"
  by (simp add: try_const_def witnessuniv_const_def primunify_const_def constraint_typing_def)

lemma (*[constraint_simp_rule]:*) "[|
    try (hiddenvar x)  ;  try (metawitnessuniv A t)  ;  primunify x t  |] ==>
  x <:: A"
  by (simp add: try_const_def metawitnessuniv_const_def primunify_const_def
    constraint_meta_typ_def)





ML {*  elab_with_expected_error "unification of * and * failed" @{context} @{term "x # x"} *}

ML {*  elab @{context} @{term "f # x"}  *}
ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}

(* tests for insane dependent pair type inference *)
ML {*  elab @{context} @{term "<x, f # x>"}  *}
(* FIXME: f not dependently typed, because dependency restriction solution
   for delayed flexflex unification restricts f's body type.
   Instead use dependency accumulation solution for flexflex problems, together
   with deprestr postprocessing of instantiated constraints via usual constraint simp. *)
ML {*  elab @{context} @{term "<g # x, f # x>"}  *}
(* g should be nondependent here *)
ML {*  elab @{context} @{term "<g # x, f # (g # x)>"}  *}
(* g should be dependent here *)
ML {*  elab @{context} @{term "<g # x, f # x # (g # x)>"}  *}
ML {*  CumulTiming.print_block "cumul elab timing" ["hidden_univlvl_discharge_proc"] (fn () =>
   elab @{context} @{term "<x, <g # x, f # x # (g # x)>>"}) *}
ML {*  elab @{context} @{term "<x, <y, f # x # y>>"}  *}
ML {*  elab @{context} @{term "<x, <y, f # y # x>>"}  *}
ML {*  elab @{context} @{term "<h # f # x, i # g # y>"}  *}

(* FIXME: abstractas does not work as expected ?! *)
ML {*  elab @{context} @{term "<x abstractas y, y, x>"} *}
ML {*  elab @{context} @{term "<(g # x) abstractas y, y, g # x, y>"}  *}



(* tests for terminal hidden universe level discharge *)
  (* i73 hidden and terminal *)
ML {*  elab @{context} @{term "(PI x:A. PI y:B(x). C # x # y)"}  *}
ML {*  elab @{context} @{term "f # (PI x:A. B(x))"}  *}
ML {*  elab @{context} @{term "f # (PI x:A. PI y:B(x). C(x,y))"}  *}
  (* also tests contextual discharge of zf-applications *)
ML {*  elab @{context} @{term "f # (PI x:A. PI y:(B # x). C # x # y)"}  *}
ML {*  elab @{context} @{term "f # (PI x:A. PI y:B(x). C(x,y)) # D"}  *}
ML {*  elab @{context} @{term "(lam x:guniv i. fun f. f # x)"} *}


(* test of smash unification ?B(x) == ?B(y) *)
ML {* elab @{context} @{term "f # x === f # y"} *}

(* NB: dependency intersection unification of ?B(x) == ?B2(y) from result types of f,g
     avoids too general type with mutual x,y dependency lifting *)
ML {* elab @{context} @{term "f # x === g # y"} *}

(* tests of dependency restriction solution of flexflex unifications *)
ML {* elab @{context} @{term "f # x === g # x"} *}
ML {* elab @{context} @{term "f # x === g # x # x"} *}
ML {* elab @{context} @{term "f # x === g # x # y"} *}
ML {* elab @{context} @{term "f # x === g # y # x"} *}
ML {* elab @{context} @{term "f # x # z === g # y # x"} *}

ML {* elab @{context} @{term "f # z # x === g # y # x"} *}

(* test of delay of flexflex unifications *)
ML {* elab @{context} @{term "f # x # y === g # x # y"} *}





(* TODO(feature): discharge univlvl-upwards-joining constraints  i u<= k,  j u<= k
   by setting  k := max(i,j)  if k does not occur in resulting judgement  *)
ML {*  elab @{context} @{term "lam f : guniv i ~> guniv i. f # (guniv j)"}  *}

ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv i. f # (guniv i)"} *}
ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv j ~> guniv i. f # (guniv j) # (guniv i)"} *}
ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv j ~> guniv k ~> guniv i. f # (guniv j) # (guniv k) # (guniv i)"} *}





(* test of postprocessing that unlifts of first-order vars (here: universe level vars) *)
(* FIXME: hidden terminal universe level ?i80 not discharged *)
ML {*  elab @{context} @{term "g # univ # (f # univ)"}  *}







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


(* TODO(feature): type of groups cannot depend on local fixes ATM, because we don't yet have
   a notion of local dictionaries that are contextually lifting over fixes.
   (in analogy to contextual discharge of typing constraint constraints)
   (this would implement dictionaries that can make use of bound variables, cf. Agda, Scala). *)

(* NB: we universe levels have to be increasing towards outside along nested PRODus *)
lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;  freshFOunifvar A  ;  freshFOunifvar d ; 
    constraint (i <: univlvl)  ;  A <: guniv i  ;
    constraint (d dictof groups(A)) |] ==>
  gmult elabto (group_mult(d)) : A ->[i] A ->[i] A"
  apply (simp add: elabjud_def constraint_const_def constraint_typing_def)
  apply (subst produ_on_good_args, assumption+)
  apply (rule produ_in_guniv, assumption)
  apply (subst produ_on_good_args, assumption+)
  by (rule groups_lawsD)

lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;  freshFOunifvar A  ;  freshFOunifvar d  ;
    constraint (i <: univlvl)  ;  A <: guniv i  ;
    constraint (d dictof groups(A)) |] ==>
  gunit elabto (group_neutral(d)) : A"
  apply (simp add: elabjud_def constraint_const_def)
  by (rule groups_lawsD)

lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;  freshFOunifvar A  ;  freshFOunifvar d  ;
    constraint (i <: univlvl)  ;  A <: guniv i  ;
    constraint (d dictof groups(A)) |] ==>
  ginv elabto (group_inv(d)) : A ->[i] A"
  apply (simp add: elabjud_def constraint_const_def constraint_typing_def)
  apply (subst produ_on_good_args, assumption+)
  by (rule groups_lawsD)


definition
  dict_refine (infixl "dictrefine" 50) where
  [MRjud 2 0]: "dict_refine(d,C) == d dictof C"

lemma [MR]: "
    constraint (d dictof groups(A)) ==>
  d dictrefine groups(A)"
  by (simp add: primunify_const_def constraint_const_def dict_refine_def)

(* NB: we do not simply put this in the constraint_simp_rule in order to collate
   chains of its application into a single simp CHR application thereby avoiding
   the generation of intermediate dictof constraints *)
(* unchecked to workaround freshFOunifvar "fact inconsistency" *)
lemma [MR_unchecked]: "[|
    freshFOunifvar dA  ;  freshFOunifvar dB  ;
    primunify d (prod_group(A,B,dA,dB))  ;
    dA dictrefine groups(A)  ;
    dB dictrefine groups(B)  |] ==>
  d dictrefine groups(A * B)"
  apply (simp add: primunify_const_def constraint_const_def dict_refine_def)
  by (rule prod_group_in_groups)

lemma [constraint_simp_rule no_re_eval_on_head_reconsideration]: "
    d dictrefine groups(A * B) ==>
  d dictof groups(A * B)"
  by (simp add: primunify_const_def constraint_const_def dict_refine_def)

lemma group_to_monoid_propag[constraint_propag_rule]:
    "d dictof groups(A) ==> monoid_of_group(d) dictof monoids(A)"
  by (rule groups_are_monoids)


(* NB: irreflexivity, i.e. intensional inequality of d1, d2
    is correctness-relevant, because constraint simplification avoids further propagation,
    e.g. with group_to_monoid_propag *)
lemma dict_sharing[constraint_simp_rule all_matches no_re_eval_on_head_reconsideration
    symmetric irreflexive]: "
   [|  try (intensionally_inequal(d1, d2))  ;    primunify d1 d2  ;
       constraint (d1 dictof C)  |] ==>  d1 dictof C &&& d2 dictof C"
  by (simp add: primunify_const_def constraint_const_def conjunctionI)


ML {*
  elab @{context} @{term "gmult # x # y === gmult # x # (gmult # y # gunit)"}
*}


ML {*
  val pats = [@{cpat "?d dictof groups(A * B)"},
    @{cpat "?d' dictof monoids(A)"}] |> map (Thm.term_of #> FOLogic.mk_Trueprop)
  val res = exception_trace (fn () => test_chr_simp  @{context} pats)
  val _ = if length (snd res) = 2 then () else error "expected constraint simplification"
*}









(* note that this is still slightly improper since we reuse Larry's list operator instead
   of a proper type constructor formulation
     list : (PI i:univlvl. guniv i -> guniv i)  *)

definition
  "list' == (lam i:univlvl. lam A:guniv i. List_ZF.list(A))"

lemma list'_ty: "list' : (PROD i:univlvl. guniv i -> guniv i)"
  unfolding list'_def
  apply typecheck
  apply (erule univlvlE)
  by (rule list_in_guniv)

lemma [MR]: "[|
    constraint (i <: univlvl)  ;   constraint (j <: univlvl)  ;
    constraint (i u<= j)  ;
    A <: guniv i  |] ==>
  (list' ` i ` A) <: guniv j"
  unfolding constraint_const_def constraint_typing_def  list'_def univ_leq_def
  apply simp
  apply (elim univlvlE)
  apply (rule list_in_guniv, assumption)
  by (rule guniv_cumul)


definition
  "nil' == (lam i:univlvl. lam A:guniv i. List_ZF.Nil)"
definition
  "cons' == (lam i:univlvl. lam A:guniv i. lam x:A. lam xs:(list'`i`A). List_ZF.Cons(x,xs))"
definition
  "map' == (lam i : univlvl. lam A : guniv i. lam B : guniv i. lam f : (A -> B). lam xs : (list' ` i ` A).
     List_ZF.map((% x. f ` x), xs) )"

lemma nil'_ty : "nil' : (PROD i:univlvl. PROD A:guniv i. list' ` i ` A)"
  unfolding nil'_def list'_def
  apply typecheck
  by simp 

lemma cons'_ty : "cons' : (PROD i:univlvl. PROD A:guniv i. A -> list' ` i ` A -> list' ` i ` A)"
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



lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;  freshFOunifvar j  ;
    constraint (i <: univlvl)  ;  constraint (j <: univlvl)  ;
    constraint (i u< j)  |] ==>
  list elabto (list' ` i) : guniv i ->[j] guniv i"
  unfolding elabjud_def constraint_const_def constraint_typing_def univ_less_def
  apply (rule produI[of j j j "guniv i" "% _. guniv i"], assumption+)
  apply (rule guniv_in_guniv) apply (blast dest: univlvlDnat)+
  apply (rule guniv_in_guniv) apply (blast dest: univlvlDnat)+
  apply (blast intro: uleq_refl univlvlDnat)+
  by (typecheck add: list'_ty)

lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;  freshunifvar A  ;
    constraint (i <: univlvl)  ;  A <: guniv i  |] ==>
  Nil elabto (nil' ` i ` A) : list' ` i ` A"
  unfolding elabjud_def constraint_const_def constraint_typing_def
  by (typecheck add: nil'_ty)

(* TODO: actually we could use a checking judgements  i <= univlvl, A <= guniv i
   here instead of emitting a constraint *)
lemma [elabMR_unchecked]: "[|
    t elabto t' : A  ;
    ts elabto ts' : list' ` i ` A2  ;
    primunify A A2  ;
    constraint (i <: univlvl)  ;  A <: guniv i   |] ==>
  (Cons(t,ts)) elabto (cons' ` i ` A ` t' ` ts') : (list' ` i ` A)"
  unfolding elabjud_def constraint_const_def primunify_const_def constraint_typing_def
  by (typecheck add: cons'_ty)



(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshFOunifvar i  ;    constraint (i <: univlvl)  ;
    freshunifvar A  ;  freshunifvar B  ;
    A <: guniv i  ;  B <: guniv i  |] ==>
  map elabto (map' ` i ` A ` B) : (A ->[i] B) ->[i] list' ` i ` A ->[i] list' ` i ` B"
  unfolding elabjud_def constraint_const_def constraint_typing_def
  apply (simp add: map'_def list'_def)
  thm produ_lamI
  apply (rule produ_lamI, auto intro: prod_in_guniv list_in_guniv uleq_refl dest: univlvlDnat simp: produ_on_good_args)
  by (rule produ_lamI,
    auto intro: prod_in_guniv produ_in_guniv list_in_guniv uleq_refl dest: univlvlDnat simp: produ_on_good_args)




ML {*  elab @{context} @{term "(map # f # [nat])"}  *}








definition
  constraintimp :: "prop => prop => prop" (infixr "=C=>" 1) where
  "constraintimp(P,Q) == (PROP P ==> PROP Q)"




ML {*
  fun mk_truenessbrack t = @{term truenessbrack} $ t
  fun dest_elabbrack (Const (@{const_name elabbrack}, _) $ t) = t
    | dest_elabbrack t = raise TERM ("dest_elabbrack", [t])
  fun mk_constraintimp P1 P2 = @{term constraintimp} $ P1 $ P2
  fun dest_constraintimp (Const (@{const_name constraintimp}, _) $ P1 $ P2) = (P1, P2)
    | dest_constraintimp t = raise TERM ("dest_constraintimp", [t])
  fun dest_constraintimps P =
    case try dest_constraintimp P of
      SOME (C, P2) => dest_constraintimps P2 |> apfst (cons C)
    | NONE => ([], P)
*}


ML_file "../isar_integration.ML"


ML {*
  structure ElabAndPrintingTagging = Proof_Data(
     type T = { printing_enabled : bool, elaborated : bool}
     fun init thy = { printing_enabled = true, elaborated = false }
  );

  val set_elaborated =
     ElabAndPrintingTagging.map (fn {printing_enabled, elaborated} =>
       {printing_enabled=printing_enabled, elaborated=true})
  fun set_printing_enabled b =
     ElabAndPrintingTagging.map (fn {printing_enabled, elaborated} =>
       {printing_enabled=b, elaborated=elaborated})

  fun elab_infer ts ctxt0 =
    let
      val ctxt = ctxt0 |> set_printing_enabled false
      val _ = tracing ("elab_infer input: "^commas (ts |> map (Syntax.string_of_term ctxt)))

      val ((pt_props, other_ts), recomb_ts) = ts |> MetaRec.filter_split (fn t =>
        fastype_of t = Term.propT andalso
        member (op =) (Term.add_const_names t []) @{const_name "elabbrack"})
    in
      if null pt_props orelse (ElabAndPrintingTagging.get ctxt |> # elaborated) then
        NONE
      else
        let
          val ptprops_conj = Logic.mk_conjunction_balanced pt_props
          val ((th, [props_conj']), (delayed_unifs, constraints)) =
            MetaRec.metarec ctxt ElabRuleProcessing.metaelabjud_n (ptprops_conj, [])
          val prop1' :: props' = Logic.dest_conjunction_balanced (length pt_props) props_conj'
           
          val _ = tracing ("elaboration theorem:   "^Display.string_of_thm ctxt th)

          val vars = [] |> fold Term.add_vars
           (prop1' :: props' @ map Logic.mk_equals delayed_unifs @ constraints)
          val unconstrain = fold_rev mk_constraintimp
            (map Logic.mk_equals delayed_unifs @ constraints
            @ map (mk_freshunifvar o Var) vars)
          (* minor FIXME: unvarify could potentially lead to Free name collisions  *)
          val unvarify_with_idxs = map_aterms
            (fn Var((n,ix), T) => Free(n ^ string_of_int ix, T)
              | t => t)
          (* fix unification variables, because checking does not allow schematic variables *)
          val unconstrained_props' = unconstrain prop1' :: props' |> map (unvarify_with_idxs) 

          val _ = tracing ("elaborated\n  "^commas (pt_props |> map (Syntax.string_of_term ctxt))
            ^"\nto\n  "^commas (unconstrained_props' |> map (Syntax.string_of_term ctxt)))
        in
          SOME (recomb_ts unconstrained_props' other_ts, set_elaborated ctxt)
        end
    end


  fun elab_printing ts ctxt0 =
    if ElabAndPrintingTagging.get ctxt0 |> #printing_enabled |> not then
      NONE
    else
      let
        (* avoids looping due to tracing outputs of metarec derivations *)
        val ctxt = ctxt0 |> set_printing_enabled false

        (* NB: using makestring to avoid looping *)
        val _ = tracing ("elab_printing on "^commas (map (Syntax.string_of_term ctxt) ts))

        fun print elab_t =
          MetaRec.metarec_fully_discharged ctxt ElabRuleProcessing.printsasjud_n (elab_t, [])
          |> snd |> hd
        val ((elab_props, other_ts), recomb_ts) = ts |> MetaRec.filter_split (fn t =>
          fastype_of t = Term.propT andalso
          member (op =) (Term.add_const_names t []) @{const_name "truenessbrack"})
      in
        if null elab_props then
          NONE
        else
          let val printed_props = map print elab_props
          in SOME (recomb_ts printed_props other_ts, ctxt) end
      end
*}


ML {**}

(* FIXME: we deactivate elab_printing (which undoes the elaboration) for now, because
    Syntax.string_of_term etc. in metarec code would then also invoke this.
    Regarding elab_infer the situation is ok because it is only run if elabbrack
    is present in input term. *)
setup {*
  Context.theory_map
    (Syntax_Phases.term_check' ~100 "elab_infer" elab_infer
     (* #> Syntax_Phases.term_uncheck' 100 "elab_printing" elab_printing*))
*}


ML {*
  Syntax.check_term @{context} @{prop "f # x === f # y"} |> cterm_of @{theory}
*}


(* NB: unstated constraint assumptions become facts available in assms
   and have to be used to enable qed *)
lemma assumes H0: "(x annotyped A) === y" shows "f # x === f # y"
proof -
  thm H0
  print_facts
  ML_prf {* Assumption.all_assms_of @{context} *}

  have "y === x"
    print_facts
    sorry
  have "f === f"
    print_facts
    sorry

  {
    fix z
    have "y === x &&& x === z"
      print_facts
      sorry
  }
  thm this


  have "y === x ==> f === g"
    print_facts
    sorry 
  thm this

  have "!!st x. f # x === g # x" sorry

  {
    assume "y === z"
    and "x === x"
      print_facts
    have "z === z"
      print_facts
      sorry
  }
  thm this


  show "f # x === f # y"
    print_facts
    sorry
qed (rule assms)+




locale test =
 fixes y z
 assumes H:"y === z" (* TODO: constraints of H should be assumed too *)
begin
  thm H

  lemma loclem: "z === z2" sorry
end




ML_file "../objlang_unify.ML"
ML_file "zf_unify.ML"


ML {* elab @{context} (@{cpat "guniv ?i"} |> Thm.term_of) *}

ML {*
  fun test_obj_unify ctxt00 assms t1 t2 =
    let
      val ts = t1 :: t2 :: assms

      val ctxt0 = ctxt00
        |> Variable.add_fixes_direct ([] |> fold Term.add_free_names ts)
        |> fold Variable.declare_term ts
      val ctxt = ctxt0
        |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt0))
        |> MetaRec.add_assm_terms_internal assms

      val _ = tracing ("============== begin object unification ==================")

      val ctxt2 = Timing.timeit (fn () =>
        ctxt |> ZF_Unify.obj_unify (t1, t2))
      val env2 = MetaRec.get_the_env_in_run_state ctxt2
      val [t1', t2'] = [t1, t2] |> map (EnvDiff.norm_term env2)
    in
      (t1', t2')
    end
*}


ML {*
  val assms = [@{cpat "exactrule (?i synthty univlvl)"}, @{cpat "exactrule (?A synthty (guniv ?i))"},
        @{cpat "exactrule (?x synthty (?A ->[?i] ?A))"}, @{cpat "exactrule (?y synthty (?A ->[?i] ?A ->[?i] ?A))"},
        @{cpat "Trueprop (z synthty ?A)"}]
      |> map Thm.term_of
  val ts = [@{cpat "?x ` z :: i"}, @{cpat "(lamu ?i z:?A. ?x ` z)"}]
    |> map Thm.term_of
  val ctxt0 = @{context}
    |> Variable.add_fixes_direct ([] |> fold Term.add_free_names ts)
    |> fold Variable.declare_term ts
  val ctxt = ctxt0
    |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt0))
    |> MetaRec.add_assm_terms_internal assms
  val otyps = ts |> map (ZFUnifyData.synth_otyp ctxt #> cterm_of @{theory})
     handle ZFUnifyData.SynthFail (ctxt2, msg) => MetaRec.err_with_trace ctxt2 msg
*}

ML {*
  let 
    val assms = [@{cpat "exactrule (?i synthty univlvl)"}, @{cpat "exactrule (?A synthty (guniv ?i))"},
        @{cpat "exactrule (?i <: univlvl)"}, @{cpat "exactrule (?A <: (guniv ?i))"},
        @{cpat "exactrule (?x synthty (?A ->[?i] ?A))"}, @{cpat "exactrule (?y synthty (?A ->[?i] ?A ->[?i] ?A))"}]
      |> map Thm.term_of
    val t1 = @{cpat "(lamu ?i w:?A. (lamu ?i z:?A. (?x ` z)))"} |> Thm.term_of
    val t2 = @{cpat "?y :: i"} |> Thm.term_of
  in
    test_obj_unify @{context} assms t1 t2 |> pairself (cterm_of @{theory})
  end
*}

ML {* *}


(* meta-theory ist schon in der Coq-Literatur abgedeckt:
     atomare Constraints <-> algebraische Constraints in
        Herberlin - Type inference with algebraic universes in CiC
     Universe-Polymorphism in   Sozeau - Universe Polymorphism in Coq
*)

(* Unifikations-Hack entspricht moeglicherweise der Entscheidbarkeit
   eines groesseren Fragments das pattern-Unifikation umfasst:
     gefunden wird die allgemeinste Substitution die die Terme
     unifiziert (nach betaeta-Normalisierungs-Preprocessing),
     modulo beta-eta in Patterns
     und "shallow" (nicht in Argumenten von non-pattern Variablen-Applikationen)
     betaeta Reduktionen in non-patterns.
   I.a. also nicht modulo "deep" betaeta Reduktionen der
   aussubstituierten Terme, weil hier koennte dann sowas wie
      (% i. ?B (?X i)) == (% i. i)
   mit ?B := (% i. i), ?X := (% i. i)
   geloest werden unter Nutzung der "tiefen" Reduktion ?X i = i.
   Bei meiner strukturellen Unifikation ist das hingegen nicht
   loesbar ("weil i nicht direkt in ?B verfuegbar, sondern nur als ?X i").
*)


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





ML {* *}

