theory UniverseLevelInference
imports "../ZFMetaRec" "../DmitriySubtyping"
begin




ML {*
  val B_x = @{cpat "% z::i. ?B(x::i, z, f(z)) :: i"} |> Thm.term_of
  val prod = @{cpat "% z::i. PROD x:?C(f(z)). ?D(x, z)"} |> Thm.term_of
  val (env', _) = 
    StructUnify.unify @{theory} (B_x, prod) (Envir.empty 1, [])
  val B_x' = Envir.norm_term env' B_x |> cterm_of @{theory}
  val prod' = Envir.norm_term env' prod |> cterm_of @{theory}
*}

ML {*
  val A1 = @{cpat "?B(x::i)"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val (env', _) = 
    StructUnify.unify @{theory} (A1, A2) (Envir.empty 1, [])
  val A1' = Envir.norm_term env' A1 |> cterm_of @{theory}
  val A2' = Envir.norm_term env' A2 |> cterm_of @{theory}
*}

ML {*
  val A1 = @{cpat "?B(x::i, x) :: i"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val env = Envir.empty 1
  val (env2, _) = StructUnify.unify @{theory} (A1, A2) (env, [])
  val A1' = Envir.norm_term env2 A1 |> cterm_of @{theory}
*}


ML {*
  val A1 = @{cpat "?B(x::i)"} |> Thm.term_of
  val A2 = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val B1 = @{cpat "?D(x :: i) :: i"} |> Thm.term_of
  val B2 = @{cpat "PROD x:?E. ?F(x)"} |> Thm.term_of
  val env = Envir.empty 1
  val (env2, _) = StructUnify.unify @{theory} (A1, A2) (env, [])
  val A2' = Envir.norm_term env2 A2 |> cterm_of @{theory}
  val B1' = Envir.norm_term env2 B1 |> cterm_of @{theory}
  val B2' = Envir.norm_term env2 B2 |> cterm_of @{theory}
  val (env3, _) = StructUnify.unify @{theory} (B1, B2) (env2, [])
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


lemma zero_in_guniv: "i : nat ==> 0 : guniv i"
  apply (rule trans_guniv[where x=0, where A=nat])
  apply assumption apply simp by (rule nat_in_guniv)


lemma guniv_cumul: "[|  i : nat  ;  j : nat  ;  i le j ;  x : guniv i |] ==> x : guniv j"
  apply (cases "i = j") apply simp
  apply (rule trans_guniv[of j x "guniv i"], assumption+)
  apply (rule guniv_in_guniv, assumption+)
  apply (rule Ord_linear_lt[of i j], simp+)
  by (simp add: le_iff)

lemma guniv_sub: "[|  i : nat  ;  j : nat  ;  i le j  |] ==> guniv i <= guniv j"
  by (auto intro: guniv_cumul)

(* unused *)
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
definition
  pteq :: "i => i => i" (infixl "===" 30) where
  "pteq(x,y) == 0"
definition
  ptannot :: "i => i => i" ("_ annotyped _") where
  "ptannot(t,A) == 0"
definition
  ptmquant :: "(i => prop) => prop" (binder "!!st " 1) where
  "ptmquant(P) == Trueprop(True)"



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


(* TODO(tradeoff): annotating PRODs with universe levels speeds up type synthesis
   (no introduction of universe levels and constraints for them necessary,
    but we need a checking judgement),
   but has to introduce more universe levels during elaboration.  *)
definition
  univannot_prod where
  "univannot_prod(k, A, B) = Pi(A, B)"

syntax
  "_PRODu"     :: "[i, pttrn, i, i] => i"  ("(3PRODu _ _:_./ _)" 10)
translations
  "PRODu i x:A. B" == "CONST univannot_prod(i, A, %x. B)"

abbreviation
  simple_univannot_fun :: "i => i => i => i" ("_ ->[_] _" 60) where
  "(A ->[i] B) == (PRODu i _:A. B)"

term "PRODu i x:A. B(x)"
term "A ->[k] B"
(* FIXME: does not translate to simple_univannot_fun *)
term "PRODu i _:A. B"





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


lemma [MR]: "t printsas t" by (simp add: printsasjud_def)

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




lemma elab_to_synthty_rewr: "t elabto t' : A' == t' synthty A'"
  by (simp add: elabjud_def synthty_const_def)

(* TODO: restrict to variables x *)
lemma [impl_frule]: "x synthty A ==> x elabto x : A"
  by (simp add: synthty_const_def elabjud_def)

lemma true_mimp_rewr: "(True ==> PROP P) == PROP P"
 by simp

lemma refl_unif_mimp_rewr: "(primunify t t ==> PROP P) == PROP P"
  apply (simp add: primunify_const_def)
  apply rule
  apply simp
  by simp

lemma freshunifvar_triv_rewr: "(freshunifvar x) == Trueprop(True)"
  by (simp add: fresh_unifvar_const_def)


ML_file "elab_rule_processing.ML"


setup {*
  Attrib.setup (Binding.name "elabMR") (ElabRuleProcessing.elabMR_decl_attr true)
    "Declaration of elaboration metarec clauses"
  #> Attrib.setup (Binding.name "elabMR_unchecked") (ElabRuleProcessing.elabMR_decl_attr false)
    "Declaration of unchecked elaboration metarec clauses"
  #> Attrib.setup (Binding.name "constraint_moding_rewrite") 
       ElabRuleProcessing.constraint_moding_rewr_decl_attr "Declaration of constraint moding rewrite rules"
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

definition
  inf_lvl_const ("inflvl _") where
  [MRjud 1 0]: "inf_lvl_const(i) == True"



lemma [constraint_moding_rewrite]: "(constraint (t <: A)) == Trueprop(t synthty A)"
  by (simp add: synthty_const_def constraint_const_def constraint_typing_def)
lemma [constraint_moding_rewrite]: "(foconstraint (t <: A)) == Trueprop(t synthty A)"
  by (simp add: synthty_const_def foconstraint_const_def constraint_typing_def)

lemma [MRjud 2 0]: "i < j == i < j" by simp

definition
  univlvl where "univlvl == nat"

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



(* customized unifications *)

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



lemma [MR]: "
    primunify A B  ==>
  supunify A B A"
  by (simp add: primunify_const_def supunify_const_def)

lemma [MR]: "[|
    primunify A1 A2 ;
    !! x. supunify B1(x) B2(x) B(x)  |]  ==>
  supunify (PROD x:A1. B1(x)) (PROD x:A2. B2(x)) (PROD x:A1. B(x))"
  apply (simp add: primunify_const_def supunify_const_def)
  by (auto intro: Pi_weaken_type)

lemma [MR]: "[|
    try (noexconstraint (i u<= j))  ;
    try (noexconstraint (j u<= i))  ;
    freshunifvar k  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    foconstraint (k <: univlvl)  ;
    foconstraint (i u<= k)  ;  foconstraint (j u<= k)  |] ==>
  supunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: supunify_const_def foconstraint_const_def constraint_typing_def
    univ_leq_def univlvl_def)
  apply (rule conjI)
  by (rule guniv_sub, assumption+)+

(* TODO(correctness): does this rely on persistent uniqueness of i'? *)
lemma [MR]: "[|
   try (exconstraint (?? i'. i u<= i') (i u<= i'))  ;
   supunify (guniv i') (guniv j) (guniv k)  ;
   foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
   foconstraint (i' <: univlvl)|] ==>
  supunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: supunify_const_def foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (erule conjE)
  apply (subgoal_tac "guniv i <= guniv i'")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto

(* TODO(correctness): does this rely on persistent uniqueness of j'? *)
lemma [MR]: "[|
   try (exconstraint (?? j'. j u<= j') (j u<= j'))  ;
   supunify (guniv i) (guniv j') (guniv k)  ;
   foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
   foconstraint (j' <: univlvl) |] ==>
  supunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: supunify_const_def foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (erule conjE)
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
    !! x. infunify B1(x) B2(x) B(x)  |]  ==>
  infunify (PROD x:A1. B1(x)) (PROD x:A2. B2(x)) (PROD x:A1. B(x))"
  apply (simp add: primunify_const_def infunify_const_def)
  by (auto intro: Pi_weaken_type)

(* NB: special treatment of the i <= j, j <= i cases is necessary to avoid infinite
   generation of guniv k constraints via typing constraint merge rule *)
lemma [MR]: "[|
    freshunifvar k  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    foconstraint (k <: univlvl)  ;  foconstraint (inflvl k)  ;
    foconstraint (k u<= i)  ;  foconstraint (k u<= j)  |] ==>
  infunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: infunify_const_def foconstraint_const_def constraint_typing_def
    univ_leq_def univlvl_def)
  apply (rule conjI)
  by (rule guniv_sub, assumption+)+

(* TODO(correctness): does this rely on persistent uniqueness of i'? *)
lemma [MR]: "[|
    try (exconstraint (?? i'. i' u<= i) (i' u<= i))  ;
    try (intensionally_inequal (i', i))  ;
    infunify (guniv i') (guniv j) (guniv k)  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    foconstraint (i' <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: infunify_const_def foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (erule conjE)
  apply (subgoal_tac "guniv i' <= guniv i")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto

(* TODO(correctness): does this rely on persistent uniqueness of j'? *)
lemma [MR]: "[|
    try (exconstraint (?? j'. j' u<= j) (j' u<= j))  ;
    try (intensionally_inequal (j', j))  ;
    infunify (guniv i) (guniv j') (guniv k)  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    foconstraint (j' <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv k)"
  apply (simp add: infunify_const_def foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (erule conjE)
  apply (subgoal_tac "guniv j' <= guniv j")
  defer 1
  apply(rule guniv_sub, assumption+)
  by auto


(*lemma [MR]: "[|
    try (exconstraint  (?? j'. j' u<= j) (j' u<= j))  ;
    try (exconstraint (inflvl j'))  ;
    constraint (j' u<= i)  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    foconstraint (j' <: univlvl) |] ==>
  infunify (guniv i) (guniv j) (guniv j')"
  apply (simp add: infunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (rule conjI)
  apply (rule guniv_sub, assumption+)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint  (?? i'. i' u<= i) (i' u<= i))  ;
    try (exconstraint (inflvl i'))  ;
    constraint (i' u<= j)  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    foconstraint (i' <: univlvl) |] ==>
  infunify (guniv i) (guniv j) (guniv i')"
  apply (simp add: infunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  apply (rule conjI)
  apply (rule guniv_sub, assumption+)
  by (rule guniv_sub, assumption+)
*)

lemma [MR]: "[|
    try (exconstraint (inflvl i))  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    constraint (i u<= j)  |] ==>
  infunify (guniv i) (guniv j) (guniv i)"
  apply (simp add: infunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint (inflvl j))  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;
    constraint (j u<= i)  |] ==>
  infunify (guniv i) (guniv j) (guniv j)"
  apply (simp add: infunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint  (inflvl i)) ;
    try (exconstraint  (inflvl j)) ;
    primunify i j  |] ==>
  infunify (guniv i) (guniv j) (guniv i)"
  by (simp add: infunify_const_def primunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)

lemma [MR]: "[|
    try (exconstraint  (i u<= j)) ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv i)"
  apply (simp add: infunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
    univlvl_def univ_leq_def ex_constraint_const_def try_const_def)
  by (rule guniv_sub, assumption+)

lemma [MR]: "[|
    try (exconstraint  (j u<= i)) ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  |] ==>
  infunify (guniv i) (guniv j) (guniv j)"
  apply (simp add: infunify_const_def constraint_const_def
    foconstraint_const_def constraint_typing_def
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

lemma [MR]: "[|
    foconstraint (i <: univlvl)  ;
    foconstraint (j <: univlvl)  ;
    foconstraint (i u<= j)  |]  ==>
  subunify (guniv i) (guniv j)"
  apply (simp add: subunify_const_def foconstraint_const_def constraint_typing_def univ_leq_def univlvl_def)
  by (rule guniv_sub)

lemma [MR]: "[|
    primunify A1 A2  ;
    !! x. subunify B1(x) B2(x)  |] ==>
  subunify (PROD x:A1. B1(x)) (PROD x:A2. B2(x))"
  apply (simp add: subunify_const_def primunify_const_def)
  by (auto intro: Pi_weaken_type)

lemma [MR]: "
  subunify A A"
  by (simp add: subunify_const_def)
  




(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* low prio rule for type inference of free variable x *)
(* TODO(opt)?: statt immer neue Unifvar zu generieren bei bereits vorhandenem constraint (x <: A')
   sofort  Unifikation A == A'  durchfuehren. Entspricht also on-the-fly constraint simplification mit der
   Typ-Constraint-Sharing-Regel von unten. Problematisch weil discharge der Annahmen zu den
   constraints nur global am Ende der metarec Ableitung erfolgen kann. *)
(* NB: in the case of atomic terms that are opqapue to type inference,
     we only use foconstraints, so fresh unifvar A is does not depend on local context.
     This is essential in order to avoid a context-dependent typing constraint for x,
     which should be a free variable so does not depend on the context *)
lemma [elabMR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    foconstraint (A <: guniv i)  ;  foconstraint (i <: univlvl)  ;  foconstraint (x <: A) |] ==>
  x elabto x : A"
 unfolding elabjud_def constraint_const_def foconstraint_const_def constraint_typing_def .


(* NB: in the case of non-atomic terms that are opaque to type inference
    we use general non-first-order constraints, as f or x might contain local fixes.
   We don't have to treat the (% x. f(x)) case because elaboration creates sets *)
lemma [elabMR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;  foconstraint (i <: univlvl)  ;  constraint (f(x) <: A) |] ==>
  f(x) elabto f(x) : A"
 unfolding elabjud_def constraint_const_def foconstraint_const_def constraint_typing_def .


(* FIXME: derivation of synthesis rule does not cope with subunify *)
lemma [elabMR_unchecked]: "[|
    t1 elabto t1' : T  ;
    freshunifvar A  ;  freshunifvar B  ;
    primunify T (PROD x:A. B(x))  ;
    t2 elabto t2' : A2  ;
    subunify A2 A  |] ==>
 (t1 # t2) elabto (t1' ` t2') : B(t2')"
  unfolding elabjud_def primunify_const_def subunify_const_def fresh_unifvar_const_def
  by (auto intro: apply_type)



(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;   foconstraint (i <: univlvl) ;
    !! x.  x elabto x : A  ==>  t(x) elabto t'(x) : B(x)  |] ==>
  (fun x. t(x)) elabto (lam x:A. t'(x)) : (PROD x:A. B(x))"
  unfolding elabjud_def fresh_unifvar_const_def
  by (rule lam_type)


(* NB: not elabMR registered to avoid overlapping printsas rule with rule above *)
lemma [MR]: "[|
    A elabto A' : U  ;
    freshunifvar i  ;  primunify U (guniv i)  ;  foconstraint (i <: univlvl)  ;
    !! x.  x elabto x : A'  ==>  t(x) elabto t'(x) : B(x)  |] ==>
  (lam x:A. t(x)) elabto (lam x:A'. t'(x)) : (PROD x:A'. B(x))"
  unfolding elabjud_def fresh_unifvar_const_def
  by (rule lam_type)



(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* NB: no direct matching of U, U2 against (guniv _) because U, U2 could
     be type unification variables *)
lemma PI_elab[elabMR_unchecked]: "[|
    A elabto A' : U  ;
    freshunifvar i  ;  primunify U (guniv i)  ;  foconstraint (i <: univlvl)  ;
    !! x.  x elabto x : A'  ==>  B(x) elabto B'(x) : U2(x)  ;
    freshunifvar j  ;  primunify U2 (% x. guniv j)  ;  foconstraint (j <: univlvl)  ;
    freshunifvar k  ;  foconstraint (k <: univlvl)  ;  foconstraint (i u<= k)  ;
    foconstraint (j u<= k)  |] ==>
  (PI x:A. B(x)) elabto (PROD x:A'. B'(x)) : guniv k"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def fresh_unifvar_const_def univ_leq_def univlvl_def
  apply (simp add: primunify_const_def)
  apply (rule prod_in_guniv)
  apply assumption
  apply (rule guniv_cumul[of i k], assumption+)
  by (rule guniv_cumul[of j k], assumption+)



(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar j  ;
    foconstraint (i <: univlvl)  ;  foconstraint (j <: univlvl)  ;   foconstraint (i u< j)  |] ==>
  univ elabto (guniv i) : (guniv j)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def univ_less_def univlvl_def
  by (rule guniv_in_guniv)

(* NB: avoid overlap with printsas rule with univ elaboration rule above *)
lemma [MR_unchecked]: "[|
    freshunifvar j  ;
    i elabto i' : A  ;  primunify A univlvl  ;
    foconstraint (i' <: univlvl)  ;  foconstraint (j <: univlvl)  ;   foconstraint (i' u< j)  |] ==>
  (guniv i) elabto (guniv i') : (guniv j)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def primunify_const_def
    univ_less_def univlvl_def
  by (rule guniv_in_guniv)

lemma natelab[elabMR]: "[|
    freshunifvar i  ;  foconstraint (i <: univlvl)  |] ==>
  nat elabto nat : (guniv i)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def univlvl_def
  by (rule nat_in_guniv)

lemma [elabMR]: "[|
    freshunifvar i  ;  foconstraint (i <: univlvl)  |] ==>
  univlvl elabto univlvl : (guniv i)"
  apply (subst univlvl_def, subst univlvl_def) by (rule natelab)


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
    freshunifvar x  ;  freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;  foconstraint (i <: univlvl)  ;  constraint (x <: A) |] ==>
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
  (<t1', t2'> typed (SUM x:A. B(x)))  synthty (SUM x:A. B(x))"
  by (simp add: synthty_const_def typed_pair_def)



lemma [MR]: "
  metaelab (PROP P) (PROP P)"
  by (simp add: metaelab_const_def)

lemma [MR]: "[|
    t elabto t' : A  |] ==>
  metaelab (elabbrack(t)) (truenessbrack(t'))"
  by (simp add: metaelab_const_def)

(* TODO(feature): allow foconstraints over x and discharge them into P'.
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

(* NB: the next 2 rules feature a B(x) non-pattern in non-primary input position.
   They can only be applied usefully by metarec if x is a free variable, esp. a fixed one. *)
 
(* TODO: unchecked for now because variable availability analysis is
     cautious about non-pattern match against input B(x) *)
lemma typ_constraint_ctxt_discharge_MR[MR_unchecked]: "[|
     try (x :> A)  ;  deprestr f A  ;
     f <:: MsPI x : A. B(x)  |] ==>
   f(x) <:: B(x)"
  unfolding try_const_def elabjud_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp

(* TODO: unchecked for now because variable availability analysis is
     cautious about non-pattern match against input B(x) *)
lemma typ_constraint_ctxt_discharge_MR2[MR_unchecked]: "[|
     try (x :> A)  ;  deprestr f A  ;
     f <:: MssPI x : A. B(x) |] ==>
   f(x) <: B(x)"
  unfolding try_const_def elabjud_def
    constraint_typing_def constraint_meta_typ_def mPi_def
    syn_constraint_typing_def
  by simp

lemma typ_constraint_ctxt_discharge_MR3[MR_unchecked]: "[|
     try (x :> A)  ;  deprestr f A  ;
     f <: PROD x:A. B(x) |] ==>
   f ` x <: B(x)"
  unfolding try_const_def elabjud_def
    constraint_typing_def syn_constraint_typing_def
  by simp


(* NB: useful when a constraint F <:: A => B gets instantiated with F:=(%x. ...)
   due to delayed structural unifications *)
lemma [MR]: "[|
    !! x. x :> A ==> f(x) <:: B(x)  |] ==>
  (% x. f(x)) <:: (MsPI x:A. B(x))"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def .
lemma [MR]: "[|
    !! x. x :> A ==> f(x) <: B(x)  |] ==>
  (% x. f(x)) <:: (MssPI x:A. B(x))"
  unfolding mPi_def constraint_meta_typ_def syn_constraint_typing_def constraint_typing_def .
  



lemma [MR]: "
    foconstraint (i <: univlvl) ==>
  nat <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def univlvl_def
  by (rule nat_in_guniv)
lemma [MR]: "
    foconstraint (i <: univlvl) ==>
  univlvl <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def univlvl_def
  by (rule nat_in_guniv)

lemma [MR]: "[|
    foconstraint (i <: univlvl)  ;
    A <: guniv i  ;  !! x. x :> A ==> B(x) <: guniv i  |] ==>
  (PROD x:A. B(x)) <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def syn_constraint_typing_def univlvl_def
  by (rule prod_in_guniv)

(* NB: i,j are always universe level variables, so the constraint (i u< j) cannot really
   be solved right now and can at best be refuted if i = j *)
lemma [MR]: "[|
    foconstraint (i <: univlvl) ;  foconstraint (j <: univlvl)  ;  foconstraint (i u< j) |] ==>
  guniv i <: guniv j"
  unfolding foconstraint_const_def constraint_typing_def univ_less_def univlvl_def
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
        val (th, [elab_t, _]) = MetaRec.metarec_fully_discharged ctxt ElabRuleProcessing.elabjud_n (t, [])
        val (_, [t']) = MetaRec.metarec_fully_discharged ctxt ElabRuleProcessing.printsasjud_n
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

(* FIXME?: contextual discharge of typing constraint for only works if
     the order of arguments is the same as their occurrence in the context,
     and all context elements do occur as arguments.
     This is due to the dependent type formation in contextual discharge rule.
     The contextual discharge should be based on the context elements,
     not the arguments, but this seems hard to achieve.
   Minor issue because contextual discharge of typing constraints is mostly
   interesting for typing constraints of unification variables,
   because for atomic terms that are opaque to type inference
   we have the specialized rule introducing first-order constraints
   (as in examples above). *)
ML {*  elab @{context} @{term "(fun f. fun x. blub(x, f))"}  *}
ML {*  elab @{context} @{term "(fun f. fun x. bla(x))"}  *}



(* NB: no merge of universe constraints for the same type yet,
   because typing constraint merge rule is not active yet *)
ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}

ML {*  elab @{context} @{term "(fun f. fun g. fun x. f # (g # x))"}  *}

(* minor FIXME: stupid __reordfree0 bound variable name. can actually be eta-contracted away here *)
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

lemma [constraint_simp_rule]: "universe_inconsistency(0) ==> i u< i"
  by (simp add: universe_inconsistency_def)+

  (* NB: no try around unify. corresponds to CHR  (i <= j , j <= i) == (i = j) *)
lemma [constraint_simp_rule]: "[| primunify i j  ;  constraint (i <: univlvl)  ;  constraint (j <: univlvl)  |] ==>
  (i u<= j &&& j u<= i)"
  unfolding univ_less_def univ_leq_def univlvl_def
  apply (rule Pure.conjunctionI)
  by (simp add: primunify_const_def constraint_const_def constraint_typing_def)+

 (* actually a specialization of the rule above for j := i *)
lemma [constraint_simp_rule]: "constraint (i <: univlvl) ==> i u<= i"
  unfolding univ_less_def univ_leq_def univlvl_def
  by (simp add: constraint_const_def constraint_typing_def)



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


lemma uless_base: "i <: univlvl ==> i u< succ(i)"
  by (simp add: univ_less_def univlvl_def constraint_typing_def)
  (* NB: univlvl typing premises only necessary for uniformity *)
lemma uless_umax1: "i u< i' ==> i' <: univlvl ==> j <: univlvl ==> i u< i' umax j"
  apply (simp add: univ_max_def univ_less_def max_def)
  apply (rule impI) by (rule Ordinal.lt_trans2)
lemma uless_umax2: "j u< j' ==> i <: univlvl ==> j' <: univlvl ==> j u< i umax j'"
  apply (simp add: univ_max_def univ_less_def max_def univlvl_def constraint_typing_def)
  apply (rule impI) apply (simp add: not_le_iff_lt) by (rule Ordinal.lt_trans)

lemma uleq_base: "i <: univlvl ==> i u<= i"
  by (simp add: univ_leq_def univlvl_def constraint_typing_def)
  (* NB: univlvl typing premises only necessary for uniformity *)
lemma uleq_umax1: "i u<= i' ==> i' <: univlvl ==> j <: univlvl ==> i u<= i' umax j"
  apply (simp add: univ_max_def univ_leq_def max_def)
  apply (rule impI) by (rule Ordinal.le_trans)
lemma uleq_umax2: "j u<= j' ==> i <: univlvl ==> j' <: univlvl ==> j u<= i umax j'"
  apply (simp add: univ_max_def univ_leq_def max_def univlvl_def constraint_typing_def)
  apply (rule impI) apply (simp add: not_le_iff_lt) by (rule leI, rule Ordinal.lt_trans1)

lemma umax_univlvl_ty: "i <: univlvl ==> j <: univlvl ==> (i umax j) <: univlvl"
  by (simp add: univ_max_def max_def)
lemma zero_univlvl_ty: "0 <: univlvl"
  by (simp add: univlvl_def constraint_typing_def)
lemma succ_univlvl_ty: "i <: univlvl ==> succ(i) <: univlvl"
  by (simp add: univlvl_def constraint_typing_def)



ML_file "hidden_univlvl_discharge.ML"


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
             (Cs |> map (rpair (MetaRec.ConstraintTrace [])))))
        |> MetaRec.put_concl_in_lin_ctxt @{prop "True"}
      val ((simpth, uninst_uls, inst_uls), _) =
        HiddenUnivlvlDischarge.calc_hidden_terminal_univlvl_discharge Cs ctxt

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
    constraint_typing_def univlvl_def)
  by (rule zero_in_guniv)

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



(* TODO: constraint simp procs die eine constraint simp rule dynamisch (auf Basis
     aller aktuell vorliegenden Constraints) generieren
     (ggf. unter Modifikation des Kontext, insbes Instantiierungen),
     die dann einmal ausgefuehrt wird
     (und entstehende Constraints werden normal hinzugefuegt) *)




ML {*  elab_with_expected_error "unification of * and * failed" @{context} @{term "x # x"} *}

(* NB: now the guniv constraints for ?A22 have been unified due to the constraint sharing rule *)
ML {*  elab @{context} @{term "f # x"}  *}

(* NB: now the universe constraints get unified due to the constraint sharing rule *)
ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}


(* tests for insane dependent pair type inference *)
ML {*  elab @{context} @{term "<x, f # x>"}  *}
ML {*  elab @{context} @{term "<g # x, f # x>"}  *}
ML {*  elab @{context} @{term "<g # x, f # (g # x)>"}  *}
ML {*  Timing.timeit (*MetaRec.output_local_cumul_timing_for ["hidden_univlvl_discharge_proc"]*)
  (fn () => elab @{context} @{term "<x, <g # x, f # x # (g # x)>>"})  *}
ML {*  elab @{context} @{term "<x, <y, f # x # y>>"}  *}
ML {*  elab @{context} @{term "<x, <y, f # y # x>>"}  *}
ML {*  elab @{context} @{term "<h # f # x, i # g # y>"}  *}

(* FIXME: abstractas does not work as expected ?! *)
ML {*  elab @{context} @{term "<x abstractas y, y, x>"} *}
ML {*  elab @{context} @{term "<(g # x) abstractas y, y, g # x, y>"}  *}




(* tests for terminal hidden universe level discharge *)
  (* i73 hidden and terminal *)
ML {*  elab @{context} @{term "f # (PI x:A. B(x))"}  *}
ML {*  elab @{context} @{term "f # (PI x:A. PI y:B(x). C(x,y))"}  *}
ML {*  elab @{context} @{term "f # (PI x:A. PI y:(B # x). C # x # y)"}  *}
(* minor FIXME: reordfree naming visible *)
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
ML {*  elab @{context} @{term "lam f : guniv i ~> guniv i. f # (guniv j)"} *}

ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv i. f # (guniv i)"} *}
ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv j ~> guniv i. f # (guniv j) # (guniv i)"} *}
ML {*  elab_with_expected_error "universe_inconsistency" @{context}
  @{term "lam f : guniv i ~> guniv j ~> guniv k ~> guniv i. f # (guniv j) # (guniv k) # (guniv i)"} *}





(* test of postprocessing that unlifts of first-order vars (here: universe level vars) *)
(* FIXME: hidden terminal universe level ?i80 not discharged *)
ML {*  elab @{context} @{term "g # univ # (f # univ)"}  *}






ML {*
  fun test_constraint_simp ctxt0 Cs =
    let
      val ctxt0 = ctxt0 |> fold Variable.declare_term Cs
        |> Variable.add_fixes_direct ([] |> fold Term.add_free_names Cs)
      val ctxt = ctxt0
        |> Context.proof_map (MetaRec.set_run_state (MetaRec.init_run_state ctxt0))
        |> Context.proof_map (MetaRec.map_constraints_in_run_state (K (Cs
             |> map (rpair (MetaRec.ConstraintTrace [])))))
        |> MetaRec.put_concl_in_lin_ctxt @{prop "True"}
      val ((Cs', implied_Cs), ctxt2) = MetaRec.constraint_simplification true ctxt
      val cert = cterm_of (Proof_Context.theory_of ctxt0)
    in
      (Cs' |> map (fst #> cert), map (fst #> cert) implied_Cs)
    end
*}

(* minor FIXME: these tests omit the  i <: univlvl  constraints.
    that should only make a difference regarding hidden univlvl discharge *)
ML {*
  val res = test_constraint_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"},
     @{prop "i u< j"}, @{prop "j u< k"}, @{prop "i u< k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"}, @{prop "l <: univlvl"},
     @{prop "i u< j"}, @{prop "j u< k"}, @{prop "k u< l"}, @{prop "i u< l"}, @{prop "j u< l"}]
  val _ = if length (snd res) = 2 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"},
     @{prop "i u< j"}, @{prop "j u< k"}, @{prop "i u<= k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"},
     @{prop "i u<= j"}, @{prop "j u< k"}, @{prop "i u< k"}]
  val _ = if length (snd res) = 1 then () else error "expected constraint simplification"
*}

ML {*
  val res = test_constraint_simp @{context}
    [@{prop "i <: univlvl"}, @{prop "j <: univlvl"}, @{prop "k <: univlvl"}, @{prop "l <: univlvl"},
     @{prop "i u< j"}, @{prop "j u<= k"}, @{prop "k u< l"}, @{prop "i u< l"}]
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
    foconstraint (i <: univlvl)  ;  constraint (A <: guniv i)  ;
    foconstraint (d dictof groups(A)) |] ==>
  gmult elabto (group_mult(d)) : A -> A -> A"
  apply (simp add: elabjud_def constraint_const_def foconstraint_const_def)
  by (rule groups_lawsD)

lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar d  ;
    foconstraint (i <: univlvl)  ;  constraint (A <: guniv i)  ;
    foconstraint (d dictof groups(A)) |] ==>
  gunit elabto (group_neutral(d)) : A"
  apply (simp add: elabjud_def constraint_const_def foconstraint_const_def)
  by (rule groups_lawsD)

lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar d  ;
    foconstraint (i <: univlvl)  ;  constraint (A <: guniv i)  ;
    foconstraint (d dictof groups(A)) |] ==>
  ginv elabto (group_inv(d)) : A -> A"
  apply (simp add: elabjud_def constraint_const_def foconstraint_const_def)
  by (rule groups_lawsD)

lemma [constraint_simp_rule no_re_eval_on_head_reconsideration]: "[|
    freshunifvar dA  ;  freshunifvar dB  ;
    primunify d (prod_group(A,B,dA,dB))  ;
    foconstraint (dA dictof groups(A))  ;
    foconstraint (dB dictof groups(B))  |] ==>
  d dictof groups(A * B)"
  apply (simp add: primunify_const_def constraint_const_def foconstraint_const_def)
  by (rule prod_group_in_groups)

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
  val res = exception_trace (fn () => test_constraint_simp  @{context} pats)
  val _ = if length (snd res) = 2 then () else error "expected constraint simplification"
*}











(* note that this is still slightly improper since we reuse Larry's list operator instead
   of a proper type constructor formulation
     list : (PI i:univlvl. guniv i -> guniv i)  *)

definition
  "list' == (lam i:univlvl. lam A:guniv i. List_ZF.list(A))"

lemma list'_ty: "list' : (PROD i:univlvl. guniv i -> guniv i)"
  unfolding list'_def univlvl_def
  apply typecheck
  by (rule list_in_guniv)

lemma [MR]: "[|
    foconstraint (i <: univlvl)  ;    A <: guniv i  |] ==>
  (list' ` i ` A) <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def  list'_def univlvl_def
  apply simp
  by (rule list_in_guniv)


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



lemma [elabMR]: "[|
    freshunifvar i  ;  foconstraint (i <: univlvl)  |] ==>
  list elabto (list' ` i) : guniv i -> guniv i"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (typecheck add: list'_ty)

lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;
    foconstraint (i <: univlvl)  ;  constraint (A <: guniv i)  |] ==>
  Nil elabto (nil' ` i ` A) : list' ` i ` A"
  unfolding elabjud_def foconstraint_const_def constraint_const_def constraint_typing_def
  by (typecheck add: nil'_ty)

(* TODO: actually we could use a checking judgements  i <= univlvl, A <= guniv i
   here instead of emitting a constraint *)
lemma [elabMR_unchecked]: "[|
    t elabto t' : A  ;
    ts elabto ts' : list' ` i ` A2  ;
    primunify A A2  ;
    foconstraint (i <: univlvl)  ;  constraint (A <: guniv i)   |] ==>
  (Cons(t,ts)) elabto (cons' ` i ` A ` t' ` ts') : (list' ` i ` A)"
  unfolding elabjud_def constraint_const_def foconstraint_const_def
    primunify_const_def constraint_typing_def
  by (typecheck add: cons'_ty)



(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [elabMR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar B  ;
    foconstraint (i <: univlvl)  ;  constraint (A <: guniv i)  ;  constraint (B <: guniv i)  |] ==>
  map elabto (map' ` i ` A ` B) : (A -> B) -> list' ` i ` A -> list' ` i ` B"
  unfolding elabjud_def foconstraint_const_def constraint_const_def constraint_typing_def
  by (simp add: map'_def list'_def)



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
      val _ = tracing ("input of inference: "^commas (ts |> map (Syntax.string_of_term ctxt)))

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
        val _ = tracing ("printing on "^commas (map (Syntax.string_of_term ctxt) ts))

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

setup {*
  Context.theory_map
    (Syntax_Phases.term_check' ~100 "elab_infer" elab_infer
     #> Syntax_Phases.term_uncheck' 100 "elab_printing" elab_printing)
*}


ML {*
  Syntax.check_term @{context} @{prop "f # x === f # y"} |> cterm_of @{theory}
*}



lemma assumes H0: "(x annotyped A) === y" shows "f # x === f # y"
proof -
  thm H0
  ML_prf {* Assumption.all_assms_of @{context} *}

  have "y === x"
    ML_prf {* Assumption.all_assms_of @{context} *}
    sorry
  have "f === f"
    ML_prf {* Assumption.all_assms_of @{context} *}
    sorry

  {
    fix z
    have "y === x &&& x === z"
      ML_prf {* Assumption.all_assms_of @{context} *}
      sorry
  }
  thm this

  have "y === x ==> f === g"
    ML_prf {* Assumption.all_assms_of @{context} *}
    sorry 
  thm this

  have "!!st x. f # x === g # x" sorry

  {
    assume "y === z"
    and "x == x"
      ML_prf {* Assumption.all_assms_of @{context} *}
    have "z === z"
      ML_prf {* Assumption.all_assms_of @{context} *}
      sorry
  }
  thm this


  show "f # x === f # y"
    ML_prf {*  Assumption.all_assms_of @{context} *}
    sorry
qed




locale test =
 fixes y z
 assumes H:"y === z" (* TODO: constraints of H should be assumed too *)
begin
  thm H

  lemma loclem: "z === z2" sorry
end


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






