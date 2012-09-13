theory MetaTypes
imports Pure
begin





definition
  meta_true :: "prop"
where
  "meta_true == ((% x::prop. x) == (% x. x))"

lemma meta_true: "PROP meta_true"
unfolding meta_true_def
by (rule Pure.reflexive)


(* characterizes well formed judgement argument types *)
definition
  wfjaty_const :: "('a::{} => prop) => prop" ("wfjaty _" [1000] 30)
where
  "wfjaty_const == % P. meta_true"




(* meta synthesis judgement for predicate elementship *)
(* synthesis of soft type hierarchies for this judgement stops
   at wf predicate *)
definition
  minsyn :: "'a::{} => ('a => prop) => prop" (infixl ":j>" 30)
where
  "minsyn x A == PROP (A x)"

(* meta refinement judgement for predicate elementship *)
(* synthesis of soft type hierarchies for this judgement stops
   at wf predicate *)
definition
  minref :: "'a::{} => ('a => prop) => prop" (infixl "<j:" 30)
where
  "minref x A == minsyn x A"



(* for better matching against application rule *)
definition
  meta_apply :: "('a::{} => 'b::{}) => 'a::{} => 'b::{}" (infixl "<>" 90)
where
  "meta_apply f a == f a"

definition
   jlam_const :: "('a::{} => prop) => ('a => 'b::{}) => ('a => 'b)"
where
  "jlam_const ty body == (% x. body x)"

(* only used for judgement inputs *)
definition
  JPi :: "('a::{} => prop) => ('a => 'b::{} => prop) => (('a => 'b) => prop)"
where
  "JPi ty bodyT == (% f. (\<And> x. x :j> ty \<Longrightarrow> f x :j> bodyT x))"


(* only used for judgement outputs *)
definition
  JPiSig1 :: "('a \<Rightarrow> prop) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> prop) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> prop)"
where
  "JPiSig1 ty bodyT \<equiv> (% f.
     (\<And> x. f x :j> bodyT x \<Longrightarrow> x :j> ty))"

definition
  JPiSig2 :: "('a \<Rightarrow> prop) \<Rightarrow> ('b \<Rightarrow> prop) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> prop) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> prop)"
where
  "JPiSig2 ty1 ty2 bodyT \<equiv> (% f.
     (\<And> x1 x2. f x1 x2 :j> bodyT x1 x2 \<Longrightarrow> x1 :j> ty1 &&& x2 :j> ty2))"

definition
  JPiSig3 :: "('a \<Rightarrow> prop) \<Rightarrow> ('b \<Rightarrow> prop) \<Rightarrow> ('c \<Rightarrow> prop) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> prop)
    \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> prop)"
where
  "JPiSig3 ty1 ty2 ty3 bodyT \<equiv> (% f.
     (\<And> x1 x2 x3. f x1 x2 x3 :j> bodyT x1 x2 x3
      \<Longrightarrow> x1 :j> ty1 &&& x2 :j> ty2 &&& x3 :j> ty3))"


definition
  JPiSig4 :: "('a \<Rightarrow> prop) \<Rightarrow> ('b \<Rightarrow> prop) \<Rightarrow> ('c \<Rightarrow> prop) \<Rightarrow> ('d \<Rightarrow> prop) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> prop)
      \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> prop)"
where
  "JPiSig4 ty1 ty2 ty3 ty4 bodyT \<equiv> (% f.
     (\<And> x1 x2 x3 x4. f x1 x2 x3 x4 :j> bodyT x1 x2 x3 x4
      \<Longrightarrow> x1 :j> ty1 &&& x2 :j> ty2 &&& x3 :j> ty3 &&& x4 :j> ty4))"


syntax
   "_jlam" :: "[pttrn, 'a::{} => prop, 'b] => ('a \<Rightarrow> 'b)" ("(3jlam _ _./ _)" 10) 
  "_JPI" :: "[pttrn, 'a \<Rightarrow> prop, 'a \<Rightarrow> ('b \<Rightarrow> prop)] \<Rightarrow>  (('a \<Rightarrow> 'b) \<Rightarrow> prop)" ("(3JPI _ _./ _)" 10) 
  "_JPISIG1" :: "[pttrn, 'a \<Rightarrow> prop, 'a \<Rightarrow> ('b \<Rightarrow> prop)] \<Rightarrow>  (('a \<Rightarrow> 'b) \<Rightarrow> prop)" ("(3JPISIG1 _ _./ _)" 10) 
  "_JPISIG2" :: "[pttrn, 'a \<Rightarrow> prop, pttrn, 'b \<Rightarrow> prop, 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> prop] \<Rightarrow>  (('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> prop)" ("(3JPISIG2 _ _ _ _./ _)" 10) 
  "_JPISIG3" :: "[pttrn, 'a \<Rightarrow> prop, pttrn, 'b \<Rightarrow> prop, pttrn, 'c \<Rightarrow> prop, 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> prop]
        \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> prop)" ("(3JPISIG3 _ _ _ _ _ _./ _)" 10) 
  "_JPISIG4" :: "[pttrn, 'a \<Rightarrow> prop, pttrn, 'b \<Rightarrow> prop, pttrn, 'c \<Rightarrow> prop, pttrn, 'd \<Rightarrow> prop,
                  'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> prop]
        \<Rightarrow>  (('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> prop)" ("(3JPISIG4 _ _ _ _ _ _ _ _./ _)" 10) 
translations
   "jlam x ty. t" == "CONST jlam_const ty (% x. t)"
  "JPI x ty. B" == "CONST JPi ty (% x. B)"
  "JPISIG1 x ty. B" == "CONST JPiSig1 ty (% x. B)"
  "JPISIG2 x1 ty1 x2 ty2. B" == "CONST JPiSig2 ty1 ty2 (% x1 x2. B)"
  "JPISIG3 x1 ty1 x2 ty2 x3 ty3. B" == "CONST JPiSig3 ty1 ty2 ty3 (% x1 x2 x3. B)"
  "JPISIG4 x1 ty1 x2 ty2 x3 ty3 x4 ty4. B" == "CONST JPiSig4 ty1 ty2 ty3 ty4 (% x1 x2 x3 x4. B)"


term "jlam x (% x. meta_true). meta_true"
ML {* @{term "JPISIG4 x1 ty1 x2 ty2 x3 ty3 x4 ty4. True" } *}



lemma jPi_ref_generalized : "wfjaty A \<Longrightarrow> (!! x. x :j> A ==> f x <j: B x) ==> f <j: (JPI x A. B x)"
unfolding JPi_def minref_def minsyn_def by assumption

lemma jlam_syn : 
 "wfjaty A ==> (!! x. x :j> A ==> t x :j> B x)
   ==> (jlam x A. t x) :j> (JPI x A. B(x))"
unfolding jlam_const_def JPi_def minsyn_def .

lemma mapply_syn : "f :j> (JPI x A. B x) ==> a :j> A ==> f a :j> B a"
unfolding JPi_def minsyn_def minref_def
proof -
  assume  h1: "!!x::'a. PROP (A x) ==> PROP B x (f x)"
  assume  h2: "PROP (A a)"
  show "PROP (B a (f a))"
  by (rule h1[OF h2])
qed


(* ganz niedrig-prior damit Konstrukte die Meta-Applikation im Objekt nutzen hochpriorer matchen
   trotzdem ziemlich problematisch fuer Fehlermeldungen, deshalb besser rausnehmen und
   explizites meta_apply nutzen *)
lemma mapply_syn_rule : "f :j> (JPI x A. B(x)) ==> a :j> A ==> f(a) :j> B(a)"
  by (rule mapply_syn)



lemma mapply_beta : "f :j> (JPI x A. B(x)) ==> a :j> A ==> (% x. f(x))(a) == f(a)"
by (rule Pure.reflexive)

lemma mapply_eta : "f :j> (JPI x A. B(x)) ==> (% x. f(x)) == f"
by (rule Pure.reflexive)








lemma pisig1E : "f :j> (JPISIG1 x A. B x) \<Longrightarrow> f x :j> B x \<Longrightarrow> x :j> A"
  unfolding JPiSig1_def minsyn_def
  by assumption


lemma pisig2E : "f :j> (JPISIG2 x1 A1 x2 A2. B x1 x2) \<Longrightarrow> f x1 x2 :j> B x1 x2 \<Longrightarrow> x1 :j> A1 &&& x2 :j> A2"
  unfolding JPiSig2_def minsyn_def
  by assumption

lemma pisig3E : "f :j> (JPISIG3 x1 A1 x2 A2 x3 A3. B x1 x2 x3) \<Longrightarrow> f x1 x2 x3 :j> B x1 x2 x3
     \<Longrightarrow> x1 :j> A1 &&& x2 :j> A2 &&& x3 :j> A3"
  unfolding JPiSig3_def minsyn_def
  by assumption

lemma pisig4E : "f :j> (JPISIG4 x1 A1 x2 A2 x3 A3 x4 A4. B x1 x2 x3 x4) \<Longrightarrow> f x1 x2 x3 x4 :j> B x1 x2 x3 x4
     \<Longrightarrow> x1 :j> A1 &&& x2 :j> A2 &&& x3 :j> A3 &&& x4 :j> A4"
  unfolding JPiSig4_def minsyn_def
  by assumption


definition
  propjud :: "'prop \<Rightarrow> 'prop"
where
  "propjud == (% P. P)"

lemma pisig1I : "wfjaty A \<Longrightarrow> (\<And> x. PROP f x \<Longrightarrow> x :j> A) \<Longrightarrow> f :j> (JPISIG1 x A. propjud)"
  unfolding JPiSig1_def minsyn_def propjud_def
  by assumption

lemma pisig2I : "wfjaty A1 \<Longrightarrow> wfjaty A2
   \<Longrightarrow> (\<And> x1 x2. PROP f x1 x2 \<Longrightarrow> x1 :j> A1 &&& x2 :j> A2) \<Longrightarrow> f :j> (JPISIG2 x1 A1 x2 A2. propjud)"
  unfolding JPiSig2_def minsyn_def propjud_def
  by assumption

lemma pisig3I : "wfjaty A1 \<Longrightarrow> wfjaty A2 \<Longrightarrow> wfjaty A3
    \<Longrightarrow> (\<And> x1 x2 x3. PROP f x1 x2 x3 \<Longrightarrow> x1 :j> A1 &&& x2 :j> A2 &&& x3 :j> A3)
    \<Longrightarrow> f :j> (JPISIG3 x1 A1 x2 A2 x3 A3. propjud)"
  unfolding JPiSig3_def minsyn_def propjud_def
  by assumption


lemma pisig4I : "wfjaty A1 \<Longrightarrow> wfjaty A2 \<Longrightarrow> wfjaty A3 \<Longrightarrow> wfjaty A4
     \<Longrightarrow> (\<And> x1 x2 x3 x4. PROP f x1 x2 x3 x4 \<Longrightarrow> x1 :j> A1 &&& x2 :j> A2 &&& x3 :j> A3 &&& x4 :j> A4)
     \<Longrightarrow> f :j> (JPISIG4 x1 A1 x2 A2 x3 A3 x4 A4. propjud)"
  unfolding JPiSig4_def minsyn_def propjud_def
  by assumption


end