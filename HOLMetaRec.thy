theory HOLMetaRec
imports Main
uses
  "../metarec/item_net2.ML"
  "../metarec/impconv.ML"
  "../metarec/decomp_pattern.ML"
  "../metarec/metarec.ML"
begin





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








(* testing *)

locale test =
  fixes dummy :: "'a"
    and dummy2 :: "'a"
    and natdummy :: "nat"
begin


ML {*
  val myref = Unsynchronized.ref (NONE : (term * (thm list * cterm) * string * thm) option)
*}

local_setup {* fn lthy =>
  let
    val bnd = Binding.name "foooo"
    val ((lhs, (n, def_th)), lthy2) = lthy
     |> Local_Theory.define ((bnd, NoSyn), ((Thm.def_binding bnd, []),
           @{term "UNIV :: 'a set"}))
    val _ = tracing ("assumptions: "^cat_lines (map (Syntax.string_of_term lthy2 o term_of)
       (Assumption.all_assms_of lthy2)))
    val lhs_exp = Local_Defs.export_cterm lthy2 lthy
      (cterm_of (ProofContext.theory_of lthy2) lhs)
    val _ = myref := SOME (lhs, lhs_exp, n, def_th)
  in
    lthy2
  end
*}

ML {*
  val SOME (lhs, lhs_exp, n, def_th) = !myref;
  prop_of def_th;
*}

local_setup {* fn lthy =>
  let val _ = tracing ("assumptions: "^cat_lines (map (Syntax.string_of_term lthy o term_of)
    (Assumption.all_assms_of @{context})))
  in lthy end
*}

ML {*
  Local_Defs.export_cterm @{context} (ProofContext.init_global @{theory})
    (cterm_of @{theory} (Logic.mk_equals (lhs, lhs)))
  |> snd |> term_of
*}


ML {*
  val tyco = "myenum"
  val tycobnd = Binding.name tyco
  val tyargs = []
*}

(* rudimentary localization suffices because no other types involved,
   but we don't register attribute in resulting context in the example,
   so pattern-completeness of functions on tyco only works on trivial functions *)
local_setup {* fn lthy =>
  let val ([tyco_name], lthy2) = lthy
    |> Local_Theory.raw_theory_result (Datatype.add_datatype Datatype_Aux.default_config
         [tyco] [(tyargs, tycobnd, NoSyn, map (fn n => (Binding.name n, [], NoSyn)) ["E1", "E2"])])
    val _ = Output.writeln ("tyco got name "^quote tyco_name)
  in lthy2 end
*}
ML {*
  @{term "E1"};
  val thy = ProofContext.theory_of @{context} ;
  val SOME info = Datatype_Data.get_info thy (Sign.full_name @{theory} tycobnd) ;
  val {split, nchotomy, induct, distinct, ...} = info ; 
  val case_const  = case prop_of split |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst of
    _ $ t => head_of t
*}

lemma "(case E1 of E1 => a | E2 => b) = (a :: 'a)"
ML_prf {*
  fun eq_refl th = @{thm eq_reflection} OF [th]
  val inst_split = split
    |> Drule.instantiate' [SOME @{ctyp "'a"}] [SOME @{cterm "% x::'a. x = a"}]
    |> eq_refl
  val distinct' = map (fn th => @{thm distinct_to_false} OF [th]) distinct
  val ss = (empty_ss |> Simplifier.context @{context})
    addsimps ([inst_split, @{thm refl_simp}] @ @{thms imp_simps} @ @{thms True_conj_simps} @ distinct')
*}
by (tactic {* Simplifier.simp_tac ss 1 THEN rtac @{thm TrueI} 1 *})





ML {*
  val bnd = Binding.name "myfun"
  val triv_bnd = Binding.name ""
*}
ML {*
@{prop "myfun E1 = natdummy"}
*}

(*fun
  myfun
where
  "myfun E1 = dummy"
| "myfun E2 = dummy2" *)

local_setup {*
  Function_Fun.add_fun [(bnd, NONE, NoSyn)]
    [((triv_bnd, []), @{prop "myfun E1 = dummy"}),
     ((triv_bnd, []), @{prop "myfun E2 = dummy"})]   
    Function_Common.default_config
*}

ML {*
    (* wird indiziert nach fundierungstechnische Konstante auf relevante Parameter,
       nicht nach lokaler Free! *)
  @{term "myfun"};
  Function_Common.get_function @{context} |> Item_Net.content |> hd;
  Function.get_info @{context} @{term "myfun"} |> #simps
*}










lemma univ_nonempty: "EX x. x : UNIV" by auto

ML {*
 val kappa = @{binding "kappa"}
*}

ML {*
  Variable.constraints_of @{context} |> fst |> Vartab.dest;
  ProofContext.inferred_fixes @{context}
*}


ML {* print_depth 20 *}
ML {*
  fun decomp_typedef typedef =
    let
      val typedef_prop = prop_of typedef
      val (rep, abs, A) = case typedef_prop of _ $ (_ $ rep $ abs $ A) => (rep, abs, A)
    in (rep, abs, A) end
*}

(* locally fixed 'a has to be renamed *)
local_setup {* fn lthy =>
  let val ((tyco_name, info), lthy2) =
    lthy |> Typedef.add_typedef false NONE (kappa, [("'b", HOLogic.typeS)], NoSyn)
      @{term "UNIV :: 'b set"} NONE (rtac @{thm univ_nonempty} 1)
   val _ = Output.writeln ("tyco_name became: "^quote tyco_name)
   val _ = Output.writeln ("info: "^PolyML.makestring (info |> snd |> #type_definition |> decomp_typedef))
   val infos = Typedef.get_info (Local_Theory.target_of lthy2) (Local_Theory.full_name lthy2 kappa)
   val _ = Output.writeln ("infos: "^PolyML.makestring infos)
  in lthy2 end
*}


local_setup {* fn lthy =>
  let
    val infos = Typedef.get_info lthy (Local_Theory.full_name lthy kappa)
   val _ = Output.writeln ("infos: "^PolyML.makestring infos)
  in lthy end
*}

ML {*
  val infos = Typedef.get_info @{context} (Local_Theory.full_name @{context} kappa)

  val decomposed_typedefs = infos |> map (snd #> #type_definition #> decomp_typedef)

*}

term "''bla''"

ML {*
  @{term "''bla''"};
  val str2 = HOLogic.mk_string "bla";
  HOLogic.dest_string str2;
*}



end




ML {*
  fun metaize_nat (Const(@{const_name Suc}, _) $ x) = metaize_nat x + 1
    | metaize_nat (Const(@{const_name "zero_class.zero"}, _)) = 0;

  fun metaize_list (Const (@{const_name "Cons"}, _) $ x $ xs) = x :: metaize_list xs
    | metaize_list (Const (@{const_name "Nil"}, _)) = []
    | metaize_list t = error ("metaize_list: not a concrete list: "^PolyML.makestring t);

  fun metaize_proplist (Const (@{const_name "prop_cons"}, _) $ x $ xs) = x :: metaize_proplist xs
    | metaize_proplist (Const (@{const_name "prop_nil"}, _)) = []
    | metaize_proplist _ = error ("metaize_proplist: not a concrete proplist");
 
  fun holize_nat 0 = @{term "0::nat"}
    | holize_nat n = @{term Suc} $ holize_nat (n-1)

  fun holize_list thy T (x :: xs) =
     Const (@{const_name "Cons"}, Sign.const_instance thy (@{const_name "Cons"}, [T]))
       $ x $ holize_list thy T xs
    | holize_list thy T [] = Const (@{const_name "Nil"}, Sign.const_instance thy (@{const_name "Nil"}, [T]))

  fun setize_list thy T (x :: xs) =
     Const (@{const_name "insert"}, Sign.const_instance thy (@{const_name "insert"}, [T]))
       $ x $ setize_list thy T xs
    | setize_list thy T [] =
        Const (@{const_name "bot"}, Sign.const_instance thy (@{const_name "bot"}, [T --> @{typ "bool"}]))
*}







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


(* pseudo-local typedef expanding local definitions and temporarily renaming TFrees *)
ML {*
  fun typedef_lthytransf (name_ct, [tyvars_ct, tyvarinter_jud_ct, set_ct]) lthy =
    let
      val (name_t, set_t) = pairself Thm.term_of (name_ct, set_ct)
      val _ =
        if null (Term.add_tvars set_t []) andalso null (Term.add_vars set_t []) then ()
        else error "typedef_lthytransf: set contains variables or type variables"

      fun constr_nonempty_t set =
        HOLogic.mk_Trueprop (Const(@{const_name "nonempty"}, fastype_of set --> @{typ "bool"}) $ set)
      val nonempty_t = constr_nonempty_t set_t

      fun err_nonempty () =
        error ("typedef_lthytransf: nonemptiness fact not there; we need\n "
         ^Syntax.string_of_term lthy nonempty_t)
      val nonempty_fact =
        case MetaRec.lookup_facts (Context.Proof lthy) (constr_nonempty_t set_t) of
          [] => err_nonempty ()
        | ne_facts => 
            (case filter (fn th => prop_of th  aconv  nonempty_t) ne_facts of
              [th] => th
            | [] => err_nonempty ()
            | _ => error ("typedef_lthytransf: nonemptiness fact "^
                Syntax.string_of_term lthy nonempty_t^" is there multiple times??!"))

      val tyvar_ts = metaize_list (Thm.term_of tyvars_ct)
      (* TODO(HACK): nutzt aus wie das MRjud Attribut die Judgement-Namen vergibt *)
      val tyvarinter_jud = MetaRec.name_from_const_or_free (Thm.term_of tyvarinter_jud_ct)
        |> suffix "_jud"
      val tfrees = tyvar_ts |> map (fn tyvar_t =>
        MetaRec.metarec lthy tyvarinter_jud (tyvar_t, [])
        |> snd |> the_single |> Logic.dest_type |> Term.dest_TFree)
      val tfrees_setord = Term.add_tfrees set_t [] |> rev
      val bad_tfrees = tfrees_setord |> subtract (op =) tfrees
      val _ =
        if null bad_tfrees then ()
        else
          error ("typedef_lthytransf: the TFrees  "
            ^Library.commas (map (Syntax.string_of_typ lthy o TFree) bad_tfrees)
            ^"  of the representing set  "^Syntax.string_of_term lthy set_t
            ^" have not been listed via the pseudo type variables  "
            ^Library.commas (map (Syntax.string_of_term lthy) tyvar_ts))
      (* FIXME: warum geht das wenn die umbenannten tfrees auch fixes sind ?! 
         besser ueber variant_free oder names_of gehen? *)
      val (ren_tfrees, lthy2) = lthy
        |> Variable.variant_fixes (map fst tfrees)
      val tfree_renaming = tfrees ~~ ren_tfrees

      val thy2 = ProofContext.theory_of lthy2
      val global_ctxt2 = ProofContext.init_global thy2
      (* globalisieren damit Typvar-Umbennenung funktioniert *)
      val set_exp =
        Local_Defs.export_cterm lthy2 global_ctxt2
          (cterm_of thy2 set_t) |> snd |> Thm.term_of
      val set_exp_ren = set_exp |> (map_types o map_type_tfree)
        (fn (n, S) => TFree (AList.lookup (op =) tfree_renaming (n, S) |> the, S))
      val (exp_rews, nonempty_fact_exp_ren) = nonempty_fact
        |> Local_Defs.export lthy2 global_ctxt2
        ||> Thm.generalize (map fst tfrees, []) 0
        ||> Thm.instantiate (map (fn ((n, S), n') =>
                (TVar((n,0), S), TFree(n',S)) |> pairself (ctyp_of thy2))
              tfree_renaming, [])
      (* val _ = tracing ("typedef_lthytransf:   set is  "^PolyML.makestring set_t
        ^"\n  exported set is  "^PolyML.makestring set_exp
        ^"\n  renamed exported set is  "^PolyML.makestring set_exp_ren
        ^"\n  tfree_renaming is "^PolyML.makestring tfree_renaming
        ^"\n  nonempty_fact is  "^PolyML.makestring (prop_of nonempty_fact)
        ^"\n  nonempty_fact_exp_ren is  "^PolyML.makestring (prop_of nonempty_fact_exp_ren)) *)

      val ne_tac = rtac (@{thm ex_from_nonempty} OF [nonempty_fact_exp_ren]) 1
      val kappa = MetaRec.name_from_const_or_free_unsuffix name_t
        |> Long_Name.base_name |> Binding.name
      val ((tyco_name, _), lthy3) = lthy2
        |> Typedef.add_typedef false NONE
             (kappa, ren_tfrees |> map (fn n => (n, HOLogic.typeS)), NoSyn)
             set_exp_ren NONE ne_tac

      val full_name = (Local_Theory.full_name lthy3 kappa)
       (* TODO(hack): nur noetig weil alte declaration Semantik den aux context vernachlaessigt *)
      val target = Local_Theory.target_of lthy3
      val infos = Typedef.get_info target full_name
      val thy3 = ProofContext.theory_of lthy3
      val type_definition_exp =
        case infos of
          (info :: _) => info |> snd |> #type_definition
        | _ => error ("typedef_lthy_transform: no infos for "^quote full_name)
      (* val _ = tracing ("typedef_lthytransf:  type_definition_exp is  "
        ^Display.string_of_thm lthy3 type_definition_exp) *)
        
      val cert = cterm_of thy3
      val certty = ctyp_of thy3
      val cert_tyof = fastype_of #> certty
      (* FIXME: eher von Hand das richtige type_definition_reinst aufsetzen,
          weil Definition folding unperfekt *)
      val type_definition_reinst = (type_definition_exp
          |> Drule.instantiate' (map (SOME o certty o TFree) tfrees) []
          |> Local_Defs.fold lthy3 exp_rews)
     (* val _ = tracing ("typedef_lthytransf:  type_definition_reinst is  "
        ^Display.string_of_thm lthy3 type_definition_reinst) *)
      val (rep, abs) = case prop_of type_definition_reinst of
        _ $ (_ $ rep $ abs $ _) => (rep, abs)
      val abs_type = case fastype_of rep of
        Type ("fun", [T1, T2]) => T1
      val th = @{thm typedef_easyI} OF
        (type_definition_reinst :: map Thm.reflexive [name_ct, tyvars_ct, tyvarinter_jud_ct])
      val msg = "typedef "^Syntax.string_of_typ lthy3 abs_type^" := "
        ^Syntax.string_of_term lthy3 set_t
        ^"\n   type_definition_reinst is "^Display.string_of_thm lthy3 type_definition_reinst
      val lthy4 = lthy3 |> MetaRec.map_lthy_transforms_log (cons msg)
      val cert = cterm_of (ProofContext.theory_of lthy4)
      (* val _ = tracing msg *)
    in ((th, [Logic.mk_type abs_type, rep, abs] |> map cert), lthy4) end
*}


setup {*
  Context.theory_map
    (MetaRec.add_lthy_transform "HOLMetaRec.typedef_const_jud" "typedef_lthytransf" typedef_lthytransf)
*}



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











ML {*
  fun enum_datatype_lthytransf (name_ct, [num_constrs_ct]) lthy =
    let
      val (name_t, num_constrs_t) = pairself Thm.term_of (name_ct, num_constrs_ct)
      val tyco_name = MetaRec.name_from_const_or_free_unsuffix name_t
        |> Long_Name.base_name
      val tyco_bnd = Binding.name tyco_name
      val tyargs = []
      val num_constrs = metaize_nat num_constrs_t
      val _ =
        if num_constrs < 1 then error "enum_datatype_lthytransf: needs at least one constructor"
        else ()
      val constr_names = map_range (fn i => tyco_name^"_Constr"^string_of_int i) num_constrs
      val ([tyco_name], lthy2) = lthy
        |> Local_Theory.raw_theory_result (Datatype.add_datatype Datatype_Aux.default_config
             [tyco_name] [(tyargs, tyco_bnd, NoSyn, constr_names |> (map (fn C => (Binding.name C, [], NoSyn))))])
         handle ERROR str =>
           MetaRec.err_with_trace_and_facts lthy
             ("enum_datatype_lthytransf: error in datatype package:\n"^str)
      val T = Type(tyco_name, [])

      val thy2 = ProofContext.theory_of lthy2
      val cert = cterm_of thy2
      val certT = ctyp_of thy2
      val ctyp_from = fastype_of #> ctyp_of thy2
      val SOME {descr, induct, distinct,
        inducts, nchotomy, case_rewrites, rec_rewrites, inject, weak_case_cong,
        split, split_asm, ...} =
          Datatype_Data.get_info thy2 (Sign.full_name thy2 tyco_bnd)
      val constrs = descr |> hd |> snd |> #3 |> map (fn (n, _) => Const(n, T)) 
      val constrs_t = holize_list thy2 T constrs
      val th = @{thm enum_datatypeI}
        |> Drule.instantiate' [SOME (ctyp_from name_t), SOME (certT T)]
              (map (SOME o cert) [name_t, num_constrs_t, Logic.mk_type T, constrs_t])

      val free_P = Free("P", T --> HOLogic.boolT)
      val quant_unroll_t = HOLogic.mk_eq (HOLogic.all_const T $ Abs("x", T, free_P $ Bound 0),
          fold (fn constr => fn rest => HOLogic.mk_conj (free_P $ constr, rest)) constrs HOLogic.true_const)
        |> HOLogic.mk_Trueprop
      val quant_unroll_th = Goal.prove lthy2 ["P"] [] quant_unroll_t (fn _ =>
          rtac @{thm iffI} 1 
          (**)
          THEN REPEAT_FIRST (rtac @{thm conjI} ORELSE' rtac @{thm TrueI})
          THEN REPEAT (etac @{thm allE} 1 THEN atac 1)
          (**)
          THEN REPEAT_FIRST (etac @{thm conjE})
          THEN rtac @{thm allI} 1
          THEN rtac induct 1
          THEN REPEAT (atac 1))
        COMP @{thm enum_datatype_quant_unrollrewI}
      val constreq_rews =
        (distinct |> map (fn th => (th COMP @{thm neq_to_rew} COMP @{thm enum_datatype_constreq_rewI})
          |> Drule.instantiate' [SOME (ctyp_from name_t)] [SOME (cert name_t)]))
        @ (constrs |> map (fn constr =>
            ((@{thm refl} |> Drule.instantiate' [SOME (ctyp_from constr)] [SOME (cert constr)])
            COMP @{thm eq_to_rew} COMP @{thm enum_datatype_constreq_rewI})
            |> Drule.instantiate' [SOME (ctyp_from name_t)] [SOME (cert name_t)]))

      val univ_t = Const(@{const_name "top"}, Sign.const_instance thy2 (@{const_name "top"}, [T --> @{typ "bool"}]))
      val univ_rewr_t = HOLogic.mk_eq (univ_t, setize_list thy2 T constrs)  |> HOLogic.mk_Trueprop
      val univ_rewr = Goal.prove lthy2 [] [] univ_rewr_t (fn _ =>
        rtac @{thm univeqI} 1 THEN
        Raw_Simplifier.rewrite_goals_tac [@{thm mem_insert_rew}, @{thm mem_empty_rew}, @{thm or_false_rew}] THEN
        rtac nchotomy 1)
        COMP @{thm enum_datatype_univ_rewI}


      val msg = "enumdatatype "^Syntax.string_of_typ lthy2 T
        ^" ::= "^(space_implode " | " (constrs |> map (Syntax.string_of_term lthy2)))
      (* val _ = tracing msg *)

      val prfx = Binding.qualify true tyco_name;
      val lthy3 = lthy2
        |> MetaRec.add_non_pervasive_declaration (fn morph =>
             MetaRec.add_rule 0 (Morphism.thm morph quant_unroll_th))
        |> MetaRec.add_facts_decl (univ_rewr :: constreq_rews)
        |> MetaRec.map_lthy_transforms_log (cons msg)
          (* rudimentary localization, Induct.induct_simp_add, Code.add_default_eqn_attribute nicht gemacht *)
        |> MetaRec.add_non_pervasive_declaration (fn _ =>
             Simplifier.map_ss (fn ss =>
               ss addsimps (case_rewrites @ distinct @ rec_rewrites)
               addcongs [weak_case_cong])
             #> fold (fn th => fn gctxt => Classical.safe_elim NONE (gctxt, th RS notE) |> fst)
                  distinct
             #> fold (fn th => fn gctxt => Clasimp.iff_add' (gctxt, th) |> fst) inject)
      val cert = cterm_of (ProofContext.theory_of lthy3)
    in
      ((th, [Logic.mk_type T, constrs_t] |> map cert), lthy3)
    end
*}


setup {*
  Context.theory_map
    (MetaRec.add_lthy_transform "HOLMetaRec.enum_datatype_jud" "enum_datatype_lthytransf" enum_datatype_lthytransf)
*}






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


ML {*

fun enum_fun_lthytransf (name_ct, [tyco_ct, vals_ct]) lthy =
  let
    val [name_t, tyco_t, vals_t] = map Thm.term_of [name_ct, tyco_ct, vals_ct]
    val ([fun_name], lthy2) = (* lthy |> Variable.variant_fixes *)
      ([MetaRec.name_from_const_or_free_unsuffix name_t |> Long_Name.base_name], lthy)
    val fun_bnd = Binding.name fun_name
    val triv_bnd = Binding.name ""

    val thy2 = ProofContext.theory_of lthy2
    val ty = Logic.dest_type tyco_t
    val tyco = case ty of
        Type(tyco, _) => tyco
      | _ => error ("enum_fun_lthytransf: "^Syntax.string_of_typ lthy2 ty
          ^" is not an enum datatype")
    val tyco_info =
      case Datatype_Data.get_info thy2 tyco of
        SOME tyco_info => tyco_info
      | _ => error ("enum_fun_lthytransf: "^tyco^" is not a datatype")
    val {descr, split, distinct, ...} = tyco_info
    val constrs = case descr of
        [(0, (_, [], constr_names_wargs))] =>
          map (fn (n, _) => Const(n, ty)) constr_names_wargs
      | _ => error ("enum_fun_lthytransf: "^quote tyco
          ^" is not an enum datatype")
    val case_const_n =
      case prop_of split |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst of
        _ $ t => (case head_of t of Const(n, _) => n)


    val vals = metaize_list vals_t
    val _ =
     if length vals = length constrs then ()
     else error ("enum_fun_lthytransf: "^string_of_int (length constrs)^" values needed;"
       ^" name is   "^fun_name^"   vals_t is:\n"
       ^Syntax.string_of_term lthy2 vals_t)
    val fstval = case vals of
        [] => error ("enum_fun_lthytransf: no values")
      | vals => hd vals
    val valty = fastype_of fstval
    val _ =
      if forall (fn val' => fastype_of val' = valty) vals then ()
      else error ("enum_fun_lthytransf: values have different types")

    val funty = ty --> valty
    val funfree = Free(fun_name, funty)
    val case_expr =
      list_comb (Const(case_const_n, Sign.const_instance thy2 (case_const_n, [valty])), vals)
    fun constreq constr v = HOLogic.mk_eq (funfree $ constr, v)
      |> HOLogic.mk_Trueprop

    val ((fun_term, (_, def_th)), lthy3) = lthy2
      |> Local_Theory.define ((fun_bnd, NoSyn), ((Thm.def_binding fun_bnd, []), case_expr))


    val thy3 = ProofContext.theory_of lthy3
    val cert = cterm_of thy3
    val certT = ctyp_of thy3
    val name_t_cty = fastype_of name_t |> certT
    val name_t_cert = cert name_t
    val valty_cert = certT valty
    val fun_cterm = cert fun_term

    val ([xname], _) = Variable.variant_fixes ["x"] lthy3
    fun eq_val_lam v = HOLogic.mk_eq (Free(xname, valty), v)
      |> absfree (xname, valty)
    val distinct' = map (fn th => @{thm distinct_to_false} OF [th]) distinct
    fun simpset inst_split = Simplifier.context lthy3 empty_ss
      addsimps ([def_th, inst_split, @{thm refl_simp}] @ @{thms imp_simps} @ @{thms True_conj_simps} @ distinct')
    val rewr_rules = constrs ~~ vals
      |> map (fn (constr, v) =>
           let
             val inst_split = @{thm eq_reflection} OF [
               Drule.instantiate' [SOME valty_cert] [SOME (cert (eq_val_lam v))] split ]
             val eqth = 
               Goal.init (cterm_of thy3 (constreq constr v))
               |> (Simplifier.simp_tac (simpset inst_split) 1  THEN  rtac @{thm TrueI} 1)
               |> (fn st => case Seq.pull st of 
                    SOME (th, _) => th
                  | NONE =>
                      error ("enumfun: proof of the following rewriting rule failed "
                        ^Syntax.string_of_term lthy3 (constreq constr v)))
               |> Goal.conclude
           in
             (@{thm enumfun_rewrI} OF [eqth])
             |> Drule.instantiate' [SOME name_t_cty] [SOME name_t_cert]
           end)

    val th = @{thm enumfun_constI}
      |> Drule.instantiate' [SOME name_t_cty, SOME (ctyp_of thy3 ty), SOME (ctyp_of thy3 valty)]
           [SOME name_t_cert, SOME (cterm_of thy3 tyco_t), SOME (cterm_of thy3 vals_t),
            SOME fun_cterm]
    val msg = "enumfun   " ^ space_implode "    "
      (map2 (fn constr => fn v => Syntax.string_of_term lthy3 (constreq constr v)) constrs vals)
    (* val _ = tracing msg *)

    val lthy4 = lthy3
      |> MetaRec.add_facts_decl rewr_rules
      |> MetaRec.map_lthy_transforms_log (cons msg)
  in ((th, [fun_cterm]), lthy4) end
*}

setup {*
  Context.theory_map
    (MetaRec.add_lthy_transform "HOLMetaRec.enumfun_const_jud" "enum_fun_lthytransf" enum_fun_lthytransf)
*}





definition
  tracing :: "string => 'a::{} => bool" where
  [MRjud 2 0]: "tracing str t == True"
lemma tracingI: "tracing str t" by (simp add: tracing_def)


ML {*
  fun tracing_proc ctxt (str_ct, [ct], _) =
    let
      val thy = ProofContext.theory_of ctxt
      val str = HOLogic.dest_string (Thm.term_of str_ct)
      val _ = tracing (str^"\n  "^Syntax.string_of_term ctxt (Thm.term_of ct))
      val th = @{thm tracingI} |> Drule.instantiate' [SOME (Thm.ctyp_of_term ct)]
        (map SOME [str_ct, ct]) 
    in
      (th, [])
    end
*}

setup {*
  Context.theory_map
    (MetaRec.add_syn_proc "HOLMetaRec.tracing_jud" "tracing" tracing_proc)
*}


ML {*
  (* error-code, bad term, context of the error, errormessage *)
  exception distinguished_metarec_error of int * cterm * Proof.context * string
*}


  (* finally a constant with a reasonable semantics ;D *)
definition
  errwith :: "string => nat => 'a => bool" where
  [MRjud 3 0]: "errwith msg errcode t == False"

ML {*
  fun errwith_proc ctxt (msg_ct, [errcode_ct, bad_ct], _) =
    let
      val msg = HOLogic.dest_string (Thm.term_of msg_ct)
      val errcode = metaize_nat (Thm.term_of errcode_ct)
      val msg2 = MetaRec.compose_err_from_trace ctxt msg
    in
      raise distinguished_metarec_error (errcode, bad_ct, ctxt, msg2)
    end
*}

setup {*
  Context.theory_map
    (MetaRec.add_syn_proc "HOLMetaRec.errwith_jud" "errwith_proc" errwith_proc)
*}





definition
  onfailerr_const :: "prop => string => nat => 'a => prop" ("onfail _ err _ _ _") where
  [MRjud 4 0]: "onfailerr_const P str errcode t == PROP P"
lemma onfailerrI: "PROP P ==> onfail (PROP P) err str errcode t"
  by (simp add: onfailerr_const_def)

ML {*
  (* error-code, message, bad term, context of the error *)
  exception distinguished_metarec_error of int * cterm * Proof.context * string

  fun onfailerr_proc ctxt (P_ct, [msg_ct, errcode_ct, bad_ct], _) =
    let
      val thy = ProofContext.theory_of ctxt

      val msg = HOLogic.dest_string (Thm.term_of msg_ct)
      val errcode = metaize_nat (Thm.term_of errcode_ct)
      fun failcont ctxt2 msg2 =
        let
          val msg3 = 
            MetaRec.compose_err_from_trace ctxt2
              (msg ^ "\n\n\nlow-level error message is:\n"^msg2)
        in
          raise distinguished_metarec_error (errcode, bad_ct, ctxt2, msg3)
        end

      val (jud, pobj, iobjs) =
        case MetaRec.decompose_judgement_cterm (Context.Proof ctxt) P_ct of
          NONE => error ("onfailerr_proc: term of unknown judgement\n"
            ^Syntax.string_of_term ctxt (Thm.term_of P_ct))
        | SOME (jud, (pobj, iobjs, _)) => (jud, pobj, iobjs)
      val (res, _) = MetaRec.metarec_worker true ctxt (SOME failcont) jud (pobj, iobjs)
      val th = (@{thm onfailerrI} OF [res])
        |> Drule.instantiate' [SOME (Thm.ctyp_of_term bad_ct)]
             (map SOME [msg_ct, errcode_ct, bad_ct])
    in
      (th, [])
    end
*}

setup {*
  Context.theory_map
    (MetaRec.add_syn_proc "HOLMetaRec.onfailerr_const_jud" "onfailerr_proc" onfailerr_proc)
*}



(* invokes the simplifier von t1;  synth  t2  from  t1,   t1 is primary *)
definition
  simpto_const :: "'a::{} => 'a => prop" ("(_) simpto (_)" [10,10] 10)
where
  [MRjud 1 1]: "simpto_const t1 t2 == (t1 == t2)"
(* synth  t2  from  t1,   t1 is primary *)
definition
  irewto_const :: "'a::{} => 'a => prop" ("(_) irewto (_)" [10,10] 10)
where
  [MRjud 1 1]: "irewto_const t1 t2 == (t1 == t2)"
(* used to register rewrite rules;  synth  t2  from  t1,   t1 is primary *)
definition
  rewto_const :: "'a::{} => 'a => prop" ("(_) rewto (_)" [10,10] 10)
where
  [MRjud 1 1]: "rewto_const t1 t2 == (t1 == t2)"


lemma simptoI: "t1 == t2  ==>  t1 simpto t2"
  by (simp add: simpto_const_def)

lemma rewtoD: "t1 rewto t2 ==> t1 == t2"
  by (simp add: rewto_const_def)

(* TODO(feature): treat conditional simp rules properly with
     rewto in premises transformed to == *)
(* TODO(semantics): besser rewrite Regeln als Fakten der Form
     decl_rewr_rule P mit P voll-quantifiziert registieren??
     aber was ist mit TVars?? *)
(* TODO(opt):  nicht jedesmal neues simpset konstruieren,
     sondern nur beim adden von neuen rewto Regeln *)
ML {*
  fun simpto_proc ctxt (ct, [], _) =
    let
      val {rules, ...} = MetaRec.get_current_ruledata (Context.Proof ctxt)
      val simprules =
        case Symtab.lookup rules "HOLMetaRec.rewto_const_jud" of
          SOME inet => Item_Net2.content inet
            |> map (fn (th, _) => @{thm rewtoD} OF [th])
        | NONE => []
      val thy = ProofContext.theory_of ctxt
      val ss = empty_ss addsimps simprules
        |> Raw_Simplifier.context ctxt

      fun prover ss = SINGLE (ALLGOALS (K all_tac)) (* Simplifier.full_simp_tac ss)) *)
      val th0 = Raw_Simplifier.rewrite_cterm (true, true, false) prover ss ct

      val th = @{thm simptoI} OF [th0]
    in (th, [Thm.rhs_of th0]) end
*}

setup {*
 Context.theory_map (
   MetaRec.add_syn_proc "HOLMetaRec.simpto_const_jud" "simpto_proc" simpto_proc)
*}





definition
  scopify_name :: "'a => 'a => bool" where
  [MRjud 1 1]: "scopify_name n n' == True"
lemma scopify_name_I[intro]: "scopify_name n n'" by (simp add: scopify_name_def)
lemma scopify_name_easyI[intro]: "n == n ==> n' == n' ==> scopify_name n n'"
  by (simp add: scopify_name_def)

ML {*
  fun scopify_name_proc ctxt (ct, [], _) =
    let
      val (scope, _, _) = MetaRec.RuleData.get (Context.Proof ctxt)
      val cert = cterm_of (ProofContext.theory_of ctxt)
      val n' = MetaRec.name_from_const_or_free_perhaps_unsuffix (Thm.term_of ct)
        |> Long_Name.base_name
        |> suffix (string_of_int scope)
        |> suffix MetaRec.name_suffix
      val ct' = Free(n', Thm.ctyp_of_term ct |> Thm.typ_of) |> cert
      val th = @{thm scopify_name_easyI} OF (map Thm.reflexive [ct, ct'])
    in (th, [ct']) end
*}

setup {*
 Context.theory_map (
   MetaRec.add_syn_proc "HOLMetaRec.scopify_name_jud" "scopify_name_proc" scopify_name_proc)
*}





definition
  blub :: "'a itself => bool"
where
  [MRjud 1 0]: "blub x == True"
definition
  datatyco :: "'a itself => bool"
where
  [MRjud 1 0]: "datatyco T == True"

definition
  test_decl_tyvar :: "nat => 'a itself => bool" where
  [MRjud 1 1]: "test_decl_tyvar a tau == True"


datatype dummyT = Dummy

locale results =
  fixes dummy1 :: "'a"
    and dummy2 :: "'b"
begin

  definition
    alpha :: nat where
    "alpha = 0"
  definition
    beta :: nat where
    "beta = 0"

  lemma [ffact]: "test_decl_tyvar alpha TYPE('a)" by (simp add: test_decl_tyvar_def)
  lemma [ffact]: "test_decl_tyvar beta TYPE('b)" by (simp add: test_decl_tyvar_def)

  lemma [ffact]: "blub TYPE('a)"
  unfolding blub_def by simp

  definition my_tyco_name :: "nat"
  where "my_tyco_name = 0"
  definition my_enum_name :: "nat"
  where "my_enum_name = 0"
  definition my_fun_name :: "nat"
  where "my_fun_name = 0"

  definition
     "myset == (UNIV  :: ('a * 'b) set)"

  lemma [ffact]: "nonempty myset" unfolding myset_def nonempty_def by auto

  lemma [expl_frule]: "[|
    blub x  ;
      typedef my_tyco_name [beta, alpha] via (test_decl_tyvar :: nat => dummyT itself => bool)
        := myset gives tyco Rep Abs  |]
    ==> True"
   unfolding blub_def by simp
  lemma [expl_frule]: "[| blub x ; enum_datatype my_enum_name (Suc (Suc (Suc 0))) T Cs |] ==> datatyco T"
   unfolding datatyco_def by simp
  lemma [expl_frule]: "[| datatyco T ; enumfun my_fun_name on T  withvals [dummy2, dummy2, dummy2] gives f |] ==> True"
   unfolding blub_def by simp


  local_setup {*
    MetaRec.run_expl_frules
  *}

  schematic_lemma "enum_datatype_quant_unrollrew (ALL x :: my_enum. P x) ?Q"
    by (tactic {* MetaRec.metarec_tac @{context} 1 *})

  schematic_lemma "enum_datatype_constreq_rew my_enum_name (my_enum_Constr0 = my_enum_Constr1) ?Q"
    by (tactic {* MetaRec.metarec_tac @{context} 1 *})

  schematic_lemma "enumfun_rewr (my_fun my_enum_Constr0) (?n :: ?'a) ?t"
    by (tactic {* MetaRec.metarec_tac @{context} 1 *})
end



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



definition
  testjud :: "nat => nat => bool"
where
  [MRjud 1 1]: "testjud x y == (y = Suc x)"
lemma [MR]: "testjud x (Suc x)" by (simp add: testjud_def)

schematic_lemma "metamap testjud [0::nat,1,2] (?ys :: nat list)"
 by (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})



definition
  testjud2 :: "nat list => bool"
where
  [MRjud 1 0]: "testjud2 xs == True"

(* test for rudimentary higher order judgement dependency analysis *)
lemma [MR]: "metamap testjud [0::nat,1,2] (ys :: nat list) ==> testjud2 ys"
  by (simp add: testjud2_def)




method_setup sorry2 =
{* Scan.succeed (Method.cheating true) *}
{* "sorry oracle" *}




end
