theory Unify
imports "../HOLMetaRec"
begin



definition
  unify where
  [MRjud 1 1]: "unify tup C \<equiv> ((\<forall> P\<in>C. P) \<longrightarrow> fst tup = snd tup)"

definition
  hasNoOcc where
  [MRjud 2 0]: "hasNoOcc t x \<equiv> True"

definition (* has no clause, so this signifies error *)
  occCheckFailed where
  [MRjud 1 0]: "occCheckFailed x \<equiv> True"

definition
  subst where
  [MRjud 1 1]: "subst t1 t2 \<equiv> (t1 = t2)"

definition
  addToCtxt :: "bool set \<Rightarrow> bool" where
  [MRjud 1 0]: "addToCtxt C \<equiv> (\<forall> P\<in>C. P)"

definition
  var :: "'a \<Rightarrow> bool" where
  [MRjud 1 0]: "var x \<equiv> True"




lemma [impl_frule]: "
  addToCtxt { x = t }
  \<Longrightarrow>  subst x t"    by (simp add: subst_def addToCtxt_def)

lemma [impl_frule]: "
  addToCtxt (C1 Un C2)
  \<Longrightarrow> addToCtxt C1 &&& addToCtxt C2"

    apply (rule Pure.conjunctionI)
    unfolding addToCtxt_def
    by auto



lemma [MR]: "
  hasNoOcc t x"  by (simp add: hasNoOcc_def)

lemma [MR]: "
   \<lbrakk> hasNoOcc t1 x  ;  hasNoOcc t2 x \<rbrakk> \<Longrightarrow>
  hasNoOcc (t1 t2) x "   by (simp add: hasNoOcc_def)

lemma [MR]: "
    occCheckFailed x \<Longrightarrow>
  hasNoOcc x x"  by (simp add: hasNoOcc_def)



lemma [MR]: "
    subst t t "   by (simp add: subst_def)

lemma [MR]: "
      [| subst t1 t1'  ;  subst t2 t2' |] ==>
    subst (t1 t2) (t1' t2')"   by (simp add: subst_def)






lemma [MR]: "
    [| try (var x) ; unify (x, t) C |] ==>
  unify (t, x) C"   by (simp add: unify_def)

lemma [MR]: "
    \<lbrakk>  try (var x)  ;  subst x t'  ;  unify (t', t) C \<rbrakk> \<Longrightarrow>
  unify (x, t) C " by (simp add: unify_def subst_def)

lemma [MR]: "
    \<lbrakk>  try (var x) ;  try (subst x x)  ;  subst t t'  ;  hasNoOcc t' x \<rbrakk> \<Longrightarrow>
  unify (x, t) { x = t' }"    by (simp add: unify_def subst_def)

lemma [MR]: "
   [| unify (t1, t1') C1  ;  addToCtxt C1 ==> unify (t2, t2') C2 |] ==>
 unify (t1 t2, t1' t2') (C1 Un C2)"     by (auto simp add: unify_def addToCtxt_def)

lemma [MR]: "
  unify (t, t) {}"  by (simp add: unify_def)






schematic_lemma
  assumes [MRassm]: "var X"
  shows "unify (c X t, c t X) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *})

(* performance test *)
schematic_lemma
  assumes [MRassm]: "var A" "var B" "var C" "var D" "var E" "var F" "var G"
  shows "unify (c A B C D E F G, c (f1 5 5) (f2 A A) (f3 B B) (f4 C C) (f5 D D) (f6 E E) (f7 F F)) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *})


(* throws occurs check *)
(* schematic_lemma
  assumes [MRassm]: "var X" "var Y"
  shows "unify (c Y X, c (f X) Y) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *}) *)


(* throws occurs check *)
(* schematic_lemma
  assumes [MRassm]: "var X"
  shows "unify (c X, X) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *}) *)


end