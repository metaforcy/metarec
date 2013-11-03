
(* first-order unification with explicit constraint (= instantiation) propagation by forward rules *) 

theory Unify
imports "../HOLMetaRec"
begin



definition
  founify where
  [MRjud 1 1]: "founify tup C \<equiv> ((\<forall> P\<in>C. P) \<longrightarrow> fst tup = snd tup)"

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
  varsubst where
  [MRjud 1 1]: "varsubst t1 t2 \<equiv> (t1 = t2)"

definition
  addToCtxt :: "bool set \<Rightarrow> bool" where
  [MRjud 1 0]: "addToCtxt C \<equiv> (\<forall> P\<in>C. P)"

definition
  var :: "'a \<Rightarrow> bool" where
  [MRjud 1 0]: "var x \<equiv> True"




lemma [impl_frule]: "
  addToCtxt { x = t }
  \<Longrightarrow>  varsubst x t"    by (simp add: varsubst_def addToCtxt_def)

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

(* important because the rhs of varsubst clauses is not normalized on-the-fly
   when new var instantiations are found
   (which is contrary to many formulations of unification) *)
lemma [MR]: "
    \<lbrakk>  try (varsubst x t)  ;  subst t t'  \<rbrakk> \<Longrightarrow>
  subst x t'"
      by (simp add: subst_def try_const_def varsubst_def)

lemma [MR]: "
      [| subst t1 t1'  ;  subst t2 t2' |] ==>
    subst (t1 t2) (t1' t2')"   by (simp add: subst_def)






lemma [MR]: "
    [| try (var x) ; founify (x, t) C |] ==>
  founify (t, x) C"   by (simp add: founify_def)

lemma [MR]: "
    \<lbrakk>  try (var x)  ;  subst x t'  ;  founify (t', t) C \<rbrakk> \<Longrightarrow>
  founify (x, t) C " by (simp add: founify_def subst_def)

lemma [MR]: "
    \<lbrakk>  try (var x) ;  try (subst x x)  ;  subst t t'  ;  hasNoOcc t' x \<rbrakk> \<Longrightarrow>
  founify (x, t) { x = t' }"    by (simp add: founify_def subst_def)

lemma [MR]: "
   [| founify (t1, t1') C1  ;  addToCtxt C1 ==> founify (t2, t2') C2 |] ==>
 founify (t1 t2, t1' t2') (C1 Un C2)"     by (auto simp add: founify_def addToCtxt_def)

lemma [MR]: "
  founify (t, t) {}"  by (simp add: founify_def)




schematic_lemma
  assumes [MRassm]: "var X" "var Y"
  shows "founify (c X, c Y) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *})

schematic_lemma
  assumes [MRassm]: "var X"
  shows "founify (c X t, c t X) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *})

(* performance test *)
schematic_lemma
  assumes [MRassm]: "var A" "var B" "var C" "var D" "var E" "var F" "var G"
  shows "founify (c A B C D, c (f1 5 5) (f2 A A) (f3 B B) (f4 C C)) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *})


(* throws occurs check *)
(* schematic_lemma
  assumes [MRassm]: "var X" "var Y"
  shows "founify (c Y X, c (f X) Y) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *}) *)


(* throws occurs check *)
(* schematic_lemma
  assumes [MRassm]: "var X"
  shows "founify (c X, X) ?C"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *}) *)


end
