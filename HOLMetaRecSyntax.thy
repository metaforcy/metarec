theory HOLMetaRecSyntax
imports Main
begin



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


(* n1, n2 input   n' output *)
definition
  concat_names_const :: "'a::{} => 'b::{} => 'c::{} => prop" ("concat names _ _ = _" [10, 10, 10] 10)
where
  "concat_names_const n1 n2 n' == Trueprop True"

lemma concat_namesI : "concat names n1 n2 = n'"
  unfolding concat_names_const_def by simp



definition
  try_const :: "prop => prop" ("try (_)"  [5] 10)
where
  "try_const P == P"

lemma tryI: "PROP P ==> try (PROP P)"
  unfolding try_const_def .

definition
  brule_const :: "prop => prop" ("brule _" [5] 10)
where
  "brule_const P == P"

definition
  frule_const :: "prop => prop" ("frule _" [5] 10)
where
  "frule_const P == P"




definition
  define_const :: "'a::{} => 'b::{} => 'b :: {} => prop" ("define (_)/ := (_)/ giving (_)" 10)
where
  "define_const name rhs lhs_output == (lhs_output == rhs)"

lemma defineI: "lhs_output == rhs ==> define name := rhs giving lhs_output"
unfolding define_const_def by simp



definition
  note_const :: "prop => 'a::{} => prop" ("note (_)/ named (_)" [5,5] 10) 
where
  "note_const P name == P"



type_synonym
  proplist = unit

definition
  prop_cons :: "prop => proplist => proplist"
where
  "prop_cons p ps = ()"

definition
  prop_nil :: "proplist"
where
  "prop_nil = ()"


lemma gen_colljudI: "PROP P == Trueprop True ==> PROP P" by simp



definition
  constraint_const :: "prop => prop"
where
  "constraint_const P == P"

abbreviation
  constraint_abbrev :: "prop => prop" ("constraint _" [5] 10) where
  "constraint_abbrev P == PROP constraint_const P"

lemma constraintI: "PROP P ==> constraint (PROP P)"
  by (simp add: constraint_const_def)

definition
  foconstraint_const :: "prop => prop"
where
  "foconstraint_const P == P"

abbreviation
  foconstraint_abbrev :: "prop => prop" ("foconstraint _" [5] 10) where
  "foconstraint_abbrev P == PROP foconstraint_const P"

lemma foconstraintI: "PROP P ==> foconstraint (PROP P)"
  by (simp add: foconstraint_const_def)


definition
  unify_const :: "'a :: {} => 'a => prop"
where
  "unify_const t1 t2 == (t1 == t2)"

abbreviation
  unify_abbrev :: "'a :: {} => 'a => prop" ("unify _ _" 10) where
  "unify_abbrev x y == PROP unify_const x y"

lemma unifyI: "t1 == t2 ==> unify t1 t2"
  by (simp add: unify_const_def)

definition
  fresh_unifvar_const:: "unit => 'a :: {} => prop"
where
  "fresh_unifvar_const u x == (Trueprop True)"

abbreviation
  fresh_unifvar_abbrev :: "'a :: {} => prop" ("freshunifvar _" 10) where
  "fresh_unifvar_abbrev x == PROP fresh_unifvar_const () x"

lemma fresh_unifvarI: "freshunifvar x"
  by (simp add: fresh_unifvar_const_def)

definition
  explapp :: "('a :: {} => 'b :: {}) => 'a => 'b" (infixl "$" 200) where
  "t1 $ t2 == t1 t2"

definition
  matchout_const :: "'a :: {} => 'a => prop" ("matchout _ _") where
  "matchout t1 t2 == (t1 == t2)"

lemma matchoutI: "matchout t t"
  by (simp add: matchout_const_def)
  

definition
  protect_eta_redex_var where
  "protect_eta_redex_var t == t"


ML {*
  val max_polym = singleton (Variable.polymorphic @{context});

  structure MetaRec = MetaRec (
    val True = @{term "True"}
    val conjunctionE = @{thm conjunctionE}

    val try_const_name = @{const_name "try_const"}
    val tryI = @{thm tryI}
    val brule_const_name = @{const_name brule_const}
    val brule_const_def = @{thm brule_const_def}
    val frule_const_name = @{const_name frule_const}
    val frule_const_def = @{thm frule_const_def}

    val constraint_headterm = @{term constraint_const} |> max_polym
    val constraintI = @{thm constraintI}
    val foconstraint_headterm = @{term foconstraint_const} |> max_polym
    val foconstraintI = @{thm foconstraintI}
    val unify_headterm = @{term unify_const} |> max_polym
    val unifyI = @{thm unifyI}
    val fresh_unifvar_headterm = @{term fresh_unifvar_const} |> max_polym
    val fresh_unifvarI = @{thm fresh_unifvarI}

    val note_headterm = @{term note_const} |> max_polym
    val note_const_def = @{thm note_const_def}
    val define_headterm = @{term define_const} |> max_polym
    val defineI = @{thm defineI}
    val concat_names_headterm = @{term concat_names_const} |> max_polym
    val concat_namesI = @{thm concat_namesI}
   
    val mk_Trueprop = HOLogic.mk_Trueprop
    val dest_Trueprop = HOLogic.dest_Trueprop

    val unit_ty = @{typ "unit"}
    val unit_elem = @{term "()"}

    val proplist_ty = @{typ "proplist"}
    fun mk_prop_cons t1 t2 = @{term "prop_cons"} $ t1 $ t2
    val prop_nil = @{term "prop_nil"}

    val gen_colljudI = @{thm gen_colljudI}

    val expl_app_const_name = @{const_name explapp}
    val expl_app_def = @{thm explapp_def}

    val matchout_headterm = @{term matchout_const} |> max_polym
    val matchout_def = @{thm matchout_const_def}
    val matchoutI = @{thm matchoutI}

    val prf_displayT = @{typ "bool"}
    fun app_prf_displayt t1 t2 = t1 $ t2

    fun protect_eta_redex_var_const ty =
      Const(@{const_name protect_eta_redex_var},
        Sign.const_instance @{theory} (@{const_name protect_eta_redex_var}, [ty]))
    val protect_eta_redex_var_def = @{thm protect_eta_redex_var_def}
  );
*}

setup {* MetaRec.setup *}






definition
  proplist_len :: "proplist => nat => bool"
where
  [MRjud 1 1]: "proplist_len L n == True"

lemma [MR]: "proplist_len Ps n ==> proplist_len (prop_cons P Ps) (Suc n)"
  unfolding proplist_len_def by simp
lemma [MR]: "proplist_len prop_nil 0"
  unfolding proplist_len_def by simp




lemma distinct_to_false: "a ~= b ==> (a = b) == False" by simp
lemma imp_simps: "(False --> P) == True" "(True --> P) == P"by simp+
lemma refl_simp: "(a = a) == True"by simp
lemma True_conj_simps: "True & P == P" "P & True == P"by simp+






(* NB: nonemptiness has to be derivable for type-generalized
   sets in typedefs, no assumptions on fixed type variables may be used *)
definition
  nonempty :: "'a set => bool"
where
  [MRjud 1 0]: "nonempty A == (EX x. x : A)"

lemma ex_from_nonempty: "nonempty A ==> (EX x. x : A)"
  unfolding nonempty_def .

definition
  typedef_const :: "'name => 'tyvar list => ('tyvar => 'aa itself => bool) =>
     'a set => 'b itself => ('b => 'a) => ('a => 'b) => bool"
     ("typedef _ _ via _ := _ gives _ _ _" 10)
where
  [MRjud 4 3]: "typedef_const n alphas tyinterpr A kappa Rep Abs == type_definition Rep Abs A"

lemma typedef_easyI: "type_definition (Rep :: 'b => 'a) Abs A
  ==> n==n ==> alphas==alphas ==> tyinterpr==typinterpr
  ==> typedef n alphas via tyinterpr := A gives TYPE('b) Rep Abs"
  unfolding typedef_const_def .







definition
  enum_datatype :: "'name => nat => 'a itself => 'a list => bool"
where
  [MRjud 2 2]: "enum_datatype n m tyco constrs == True"

lemma enum_datatypeI: "enum_datatype n m tyco constrs"
  unfolding enum_datatype_def by simp

(*  (ALL x :: enum. P x) == ( P C1 /\ ... /\ P Cn ) *)
definition
  enum_datatype_quant_unrollrew :: "bool => bool => bool"
where
  [MRjud 1 1]: "enum_datatype_quant_unrollrew t1 t2 == (t1 = t2)"


lemma metaeq_bool_I: "(P ==> Q) ==> (Q ==> P) ==> P == Q"
  apply (rule eq_reflection)
  by auto


(* test of general tactic approach *)
datatype myenum = E1 | E2
lemma "(ALL x :: myenum. P x) == P E1 & P E2 & True"
  by (tactic {*
     rtac @{thm metaeq_bool_I} 1 
   
     THEN REPEAT_FIRST (rtac @{thm conjI} ORELSE' rtac @{thm TrueI})
     THEN REPEAT (etac @{thm allE} 1 THEN atac 1)

     THEN REPEAT_FIRST (etac @{thm conjE})
     THEN rtac @{thm allI} 1
     THEN rtac @{thm myenum.induct} 1
     THEN REPEAT (atac 1) *})


lemma enum_datatype_quant_unrollrewI: "t1 = t2 ==> enum_datatype_quant_unrollrew t1 t2"
  unfolding enum_datatype_quant_unrollrew_def .


(*  (C_i = C_j) == False   for i =/= j
    (C_i = C_i) == True  *)
definition
  enum_datatype_constreq_rew :: "'name => bool => bool => bool"
where
  [MRjud 2 1]: "enum_datatype_constreq_rew n t1 t2 == (t1 = t2)"

lemma enum_datatype_constreq_rewI: "t1 = t2 ==> enum_datatype_constreq_rew n t1 t2"
  unfolding enum_datatype_constreq_rew_def .

lemma neq_to_rew: "x ~= y ==> ((x = y) = False)" by simp
lemma eq_to_rew: "x = y ==> ((x = y) = True)" by simp


(*  UNIV == {constructors} *)
definition
  enum_datatype_univ_rew :: "'a set => 'a set => bool"
where
  [MRjud 1 1]: "enum_datatype_univ_rew S1 S2 == (S1 = S2)"
lemma enum_datatype_univ_rewI: "S1 = S2 ==> enum_datatype_univ_rew S1 S2"
  by (simp add: enum_datatype_univ_rew_def)


lemma mem_insert_rew: "x : insert a A == ( x = a | x : A )" by simp
lemma mem_empty_rew: "x : {} == False" by simp
lemma or_false_rew: "P | False == P" by simp
lemma univeqI: "ALL x. x : A ==> UNIV = A" by auto













definition
  enumfun_const :: "'name => 'a itself => 'b list => ('a => 'b) => bool" ("enumfun _ on _ withvals _ gives _" 10)
where
  [MRjud 3 1]: "enumfun_const n kappa rhss f == True"

lemma enumfun_constI: "enumfun_const n kappa rhss f"
   by (simp add: enumfun_const_def)

definition
  enumfun_rewr :: "'a => 'name => 'a => bool"
where
  [MRjud 1 2]: "enumfun_rewr t1 n t2 == (t1 = t2)"



lemma enumfun_rewrI : "t1 = t2 ==> enumfun_rewr t1 n t2"
  unfolding enumfun_rewr_def .





definition
  tracing :: "string => 'a::{} => bool" where
  [MRjud 2 0]: "tracing str t == True"
lemma tracingI: "tracing str t" by (simp add: tracing_def)

  (* finally a constant with a reasonable semantics ;D *)
definition
  errwith :: "string => nat => 'a => bool" where
  [MRjud 3 0]: "errwith msg errcode t == False"






definition
  onfailerr_const :: "prop => string => nat => 'a => prop" ("onfail _ err _ _ _") where
  [MRjud 4 0]: "onfailerr_const P str errcode t == PROP P"
lemma onfailerrI: "PROP P ==> onfail (PROP P) err str errcode t"
  by (simp add: onfailerr_const_def)



(* invokes the simplifier von t1;  synth  t2  from  t1,   t1 is primary *)
definition
  simpto_const :: "'a::{} => 'a => prop" ("(_) simpto (_)" [10,10] 10)
where
  [MRjud 1 1]: "simpto_const t1 t2 == (t1 == t2)"
definition
  powersimpto_const :: "'a::{} => 'a => prop" ("(_) powersimpto (_)" [10,10] 10)
where
  [MRjud 1 1]: "powersimpto_const t1 t2 == (t1 == t2)"

(* used to register rewrite rules;  synth  t2  from  t1,   t1 is primary *)
definition
  rewto_const :: "'a::{} => 'a => prop" ("(_) rewto (_)" [10,10] 10)
where
  [MRjud 1 1]: "rewto_const t1 t2 == (t1 == t2)"


lemma simptoI: "t1 == t2  ==>  t1 simpto t2"
  by (simp add: simpto_const_def)
lemma powersimptoI: "t1 == t2  ==>  t1 powersimpto t2"
  by (simp add: powersimpto_const_def)

lemma rewtoD: "t1 rewto t2 ==> t1 == t2"
  by (simp add: rewto_const_def)






definition
  scopify_name :: "'a => 'a => bool" where
  [MRjud 1 1]: "scopify_name n n' == True"
lemma scopify_name_I[intro]: "scopify_name n n'" by (simp add: scopify_name_def)
lemma scopify_name_easyI[intro]: "n == n ==> n' == n' ==> scopify_name n n'"
  by (simp add: scopify_name_def)





(* NB: no higher-order mode analysis and only
   hackish higher-order dependency tracking
   for proj_proplist and metamap.
   Use only with concrete judgements with corresponding mode in frules! *)
definition
  proj_proplist :: "(prop => 'a => prop) => proplist => 'a list => bool"
where
  [MRjud 2 1]: "proj_proplist J Ps ys == True"
lemma proj_proplistI[intro]: "proj_proplist J Ps ys" by (simp add: proj_proplist_def)


lemma [MR_unchecked]: "[|  PROP (J P y)  ;  proj_proplist J Ps ys  |]
                      ==> proj_proplist J (prop_cons P Ps) (Cons y ys) " ..
lemma [MR]: "proj_proplist J prop_nil []" ..



inductive
  metamap :: "('a => 'b => bool) => 'a list => 'b list => bool"
where
  metamap_nil: "
    metamap J [] []"
| metamap_cons: "[| J x y  ;  metamap J xs ys |] ==>
    metamap J (Cons x xs) (Cons y ys) "

lemma [MRjud 2 1]: "metamap J xs ys == metamap J xs ys" by simp
declare metamap_nil[MR]
declare metamap_cons[MR_unchecked]





(* hack: use a,b,c,d type constructors instead of type variables in
   judgement patterns in collectHOLfacts judgement *)
typedef a = "UNIV :: bool set"   by simp
typedef b = "UNIV :: bool set"   by simp
typedef c = "UNIV :: bool set"   by simp
typedef d = "UNIV :: bool set"   by simp


definition  (* judgement for the synthesis proc *)
  collectHOLfacts_int :: "prop \<Rightarrow> bool set \<Rightarrow> bool" where
  [MRjud 1 1]: "collectHOLfacts_int pat Js == (\<forall> J\<in>Js. J)"

lemma allholdEmpty: "(\<forall> J\<in>{}. J)" by simp
lemma allholdInsert: "J2 \<Longrightarrow> (\<forall> J\<in> Js. J) \<Longrightarrow> (\<forall> J\<in>(insert J2 Js). J)" by simp

lemma 
  assumes assms: "A" "B" "C"
  shows "(\<forall> J\<in>{A,B,C}. J)"
  by (tactic {* REPEAT_FIRST (resolve_tac ([@{thm allholdEmpty}, @{thm allholdInsert}] @ @{thms assms})) *})

lemma collectHOLfacts_intI: "(\<forall> J\<in>Js. J) \<Longrightarrow> collectHOLfacts_int pat Js"
  by (simp add: collectHOLfacts_int_def)


definition
  collectHOLfacts where
  [MRjud 1 1]: "collectHOLfacts pat Js \<equiv> collectHOLfacts_int pat Js"

lemma [MR]: "
    collectHOLfacts_int pat Js \<Longrightarrow>
  collectHOLfacts pat Js"  by (simp add: collectHOLfacts_def)




definition
  gen_fresh :: "unit \<Rightarrow> 'a \<Rightarrow> bool" where
  [MRjud 1 1 allowinconsis]: "gen_fresh u x \<equiv> True"
lemma gen_freshI: "gen_fresh () x"  by (simp add: gen_fresh_def)






method_setup sorry2 =
  {* Scan.succeed (Method.cheating true) *}
  {* "sorry oracle" *}




end
