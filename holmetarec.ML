


structure HOLMetaRec = struct

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



  (* pseudo-local typedef expanding local definitions and temporarily renaming TFrees *)
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

      val thy2 = Proof_Context.theory_of lthy2
      val global_ctxt2 = Proof_Context.init_global thy2
      (* globalisieren damit Typvar-Umbennenung funktioniert *)
      val set_exp =
        Local_Defs.export_cterm lthy2 global_ctxt2
          (cterm_of thy2 set_t) |> snd |> Thm.term_of
      val set_exp_ren = set_exp |> (map_types o map_type_tfree)
        (fn (n, S) => TFree (AList.lookup (op =) tfree_renaming (n, S) |> the, S))
      val (exp_rews, nonempty_fact_exp_ren) = nonempty_fact
        |> Local_Defs.export lthy2 global_ctxt2
        |>> fst
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
        |> Typedef.add_typedef
             (kappa, ren_tfrees |> map (fn n => (n, HOLogic.typeS)), NoSyn)
             set_exp_ren NONE ne_tac

      val full_name = (Local_Theory.full_name lthy3 kappa)
       (* TODO(hack): nur noetig weil alte declaration Semantik den aux context vernachlaessigt *)
      val target = Local_Theory.target_of lthy3
      val infos = Typedef.get_info target full_name
      val thy3 = Proof_Context.theory_of lthy3
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
      val cert = cterm_of (Proof_Context.theory_of lthy4)
      (* val _ = tracing msg *)
    in ((th, [Logic.mk_type abs_type, rep, abs] |> map cert), lthy4) end







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
             [((tyco_bnd, tyargs, NoSyn), constr_names |> (map (fn C => (Binding.name C, [], NoSyn))))])
         handle ERROR str =>
           MetaRec.err_with_trace_and_facts lthy
             ("enum_datatype_lthytransf: error in datatype package:\n"^str)
      val T = Type(tyco_name, [])

      val thy2 = Proof_Context.theory_of lthy2
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
          fold (fn constr => fn rest => HOLogic.mk_conj (free_P $ constr, rest)) constrs @{term "True"})
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
               |> Raw_Simplifier.add_cong weak_case_cong)
             #> fold (fn th => fn gctxt => Classical.safe_elim NONE (gctxt, th RS notE) |> fst |> the)
                  distinct
             #> fold (fn th => fn gctxt => Clasimp.iff_add' (gctxt, th) |> fst |> the) inject)
      val cert = cterm_of (Proof_Context.theory_of lthy3)
    in
      ((th, [Logic.mk_type T, constrs_t] |> map cert), lthy3)
    end




  fun enum_fun_lthytransf (name_ct, [tyco_ct, vals_ct]) lthy =
    let
      val [name_t, tyco_t, vals_t] = map Thm.term_of [name_ct, tyco_ct, vals_ct]
      val ([fun_name], lthy2) = (* lthy |> Variable.variant_fixes *)
        ([MetaRec.name_from_const_or_free_unsuffix name_t |> Long_Name.base_name], lthy)
      val fun_bnd = Binding.name fun_name
      val triv_bnd = Binding.name ""

      val thy2 = Proof_Context.theory_of lthy2
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


      val thy3 = Proof_Context.theory_of lthy3
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




  fun tracing_proc ctxt (str_ct, [ct], _) =
    let
      val thy = Proof_Context.theory_of ctxt
      val str = HOLogic.dest_string (Thm.term_of str_ct)
      val _ = tracing (str^"\n  "^Syntax.string_of_term ctxt (Thm.term_of ct))
      val th = @{thm tracingI} |> Drule.instantiate' [SOME (Thm.ctyp_of_term ct)]
        (map SOME [str_ct, ct]) 
    in
      (th, [])
    end



  (* error-code, bad term, context of the error, errormessage *)
  exception distinguished_metarec_error of int * cterm * Proof.context * string

  fun errwith_proc ctxt (msg_ct, [errcode_ct, bad_ct], _) =
    let
      val msg = HOLogic.dest_string (Thm.term_of msg_ct)
      val errcode = metaize_nat (Thm.term_of errcode_ct)
      val msg2 = MetaRec.compose_err_from_trace ctxt msg
    in
      raise distinguished_metarec_error (errcode, bad_ct, ctxt, msg2)
    end

  fun onfailerr_proc ctxt (P_ct, [msg_ct, errcode_ct, bad_ct], _) =
    let
      val thy = Proof_Context.theory_of ctxt

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




(* TODO(feature): treat conditional simp rules properly with
     rewto in premises transformed to == *)
(* TODO(semantics): besser rewrite Regeln als Fakten der Form
     decl_rewr_rule P mit P voll-quantifiziert registieren??
     aber was ist mit TVars?? *)
(* TODO(opt):  nicht jedesmal neues simpset konstruieren,
     sondern nur beim adden von neuen rewto Regeln *)
  fun simpto_proc power ctxt (ct, [], _) =
    let
      val {rules, ...} = MetaRec.get_current_ruledata (Context.Proof ctxt)
      val simprules =
        case Symtab.lookup rules "HOLMetaRecSyntax.rewto_const_jud" of
          SOME inet => Item_Net2.content inet
            |> map (fn (th, _) => @{thm rewtoD} OF [th])
        | NONE => []
      val ss = empty_ss addsimps simprules |> Raw_Simplifier.context ctxt

      val prover =
        if power then MetaRec.metarec_simp_prover
        else (fn ss => SINGLE (ALLGOALS (K all_tac)))
      val th0 = Raw_Simplifier.rewrite_cterm (true, true, false) prover ss ct

      val th = (if power then @{thm powersimptoI} else @{thm simptoI}) OF [th0]
    in (th, [Thm.rhs_of th0]) end


  fun scopify_name_proc ctxt (ct, [], _) =
    let
      val (scope, _, _) = MetaRec.RuleData.get (Context.Proof ctxt)
      val cert = cterm_of (Proof_Context.theory_of ctxt)
      val n' = MetaRec.name_from_const_or_free_perhaps_unsuffix (Thm.term_of ct)
        |> Long_Name.base_name
        |> suffix (string_of_int scope)
        |> suffix MetaRec.name_suffix
      val ct' = Free(n', Thm.ctyp_of_term ct |> Thm.typ_of) |> cert
      val th = @{thm scopify_name_easyI} OF (map Thm.reflexive [ct, ct'])
    in (th, [ct']) end



(* gen_fresh is only possible because Isabelle/Pure has no typing contexts
   (this is consistent because types are always non-empty),
   so we can just introduce a fresh Free variable with a given type.
   Very useful for variables whose constraints are discovered only later
   (esp. unification variables) *)
local
  val freshcounter = Unsynchronized.ref 0
in
  (* NB: uses output pattern for its type, so this synproc cannot be
     hidden in an internal judgement. *)
  fun gen_fresh_proc ctxt (_, [], [coutpat]) =
    let
      val ([n], _) = ctxt |>
        Variable.variant_fixes ["genfresh" ^ string_of_int (!freshcounter)]
      val T = Thm.ctyp_of_term coutpat |> Thm.typ_of
      val free = Free(n, T)
      val cfree = free |> cterm_of (Proof_Context.theory_of ctxt)
      val th = @{thm gen_freshI}
        |> Drule.instantiate' [SOME (Thm.ctyp_of_term cfree)] [SOME cfree]
      val _ = Unsynchronized.inc freshcounter
    in (th, [cfree]) end
end



  fun collectHOLfacts_proc ctxt (pat0_ct, [], _) =
    let
      val thy = Proof_Context.theory_of ctxt
      val pat0 = pat0_ct |> Thm.term_of |> Envir.beta_norm
      val vars0 = Term.strip_all_vars pat0

      val vars = ((Variable.variant_fixes (map fst vars0) ctxt |> fst) ~~ (map snd vars0))
        |> map (fn (n, T) => Var((n, 0), T))

      val hackTvar = [(@{typ "a"}, @{typ "'a"}), (@{typ "b"}, @{typ "'b"}),
        (@{typ "c"}, @{typ "'c"}), (@{typ "d"}, @{typ "'d"})]
        |> map (apsnd Logic.varifyT_global)
      fun replaceTHack (T as Type(k, Ts)) =
          (case AList.lookup (op =) hackTvar T of
            SOME tvar => tvar
          | NONE => Type(k, map replaceTHack Ts))
        | replaceTHack T = T
        
      val pat = Term.subst_bounds (rev vars, Term.strip_all_body pat0)
        |> map_types replaceTHack

      val _ = tracing ("pat is "^Syntax.string_of_term ctxt pat)

      val (jid, pobj_pat, iobjs_pat, oobjs_pat) =  case MetaRec.decompose_judgement (Context.Proof ctxt) pat of
          SOME (jid, (pobj, iobjs, oobjs)) => (jid, pobj, iobjs, oobjs)
        | NONE => MetaRec.err_with_trace ctxt ("collectHOLfacts proc: judgement not recognized in "
            ^Syntax.string_of_term ctxt pat)
      
      (* TODO(refactor?): minor code duplication with MetaRec.metarec_worker *)
      val {facts, judgements, ...} = MetaRec.get_current_ruledata (Context.Proof ctxt)
      val jud_matcher = case MetaRec.lookup_judgement_analyzer judgements jid of
          SOME (jud_matcher, _, _) => jud_matcher
        | NONE => error ("internal error: judgement "^quote jid^" now not recognized?!")        
      val pot_facts = Net.unify_term facts pat

      val _ = tracing ("pot facts are \n"^cat_lines (pot_facts |> (map (fn fact => Syntax.string_of_term ctxt (prop_of fact)))))

      val matching_facts = pot_facts
        |> filter (fn fact =>
              let
                 val factconcl = fact |> Thm.concl_of
                 (* TODO(refactor?): minor code duplication with MetaRec.add_assm *)
                 val (pobj2, iobjs2, oobjs2) = factconcl |> jud_matcher |> the
                 val _ = tracing ("pobj_pat, ibojs_pat, oobjs_pat: "^commas ((pobj_pat :: iobjs_pat @ oobjs_pat) |> map (Syntax.string_of_term ctxt)))
                 val _ = tracing ("pobj2, ibojs2, oobjs2: "^commas ((pobj2 :: iobjs2 @ oobjs2) |> map (Syntax.string_of_term ctxt)))
                 val is_fact =
                    Thm.nprems_of fact = 0
                    andalso null (Term.add_vars factconcl [])
                    andalso null (Term.add_tvars factconcl [])
                 val _ =
                   if not is_fact then
                     MetaRec.err_with_trace ctxt ("collectHOLfacts proc: internal error: not a fact in fact table")
                   else ()
              in
                case MetaRec.decompose_pattern_match_opt thy (pat, factconcl) of
                  SOME inst =>
                    (iobjs_pat @ oobjs_pat, iobjs2 @ oobjs2)
                    |> pairself (map (Term_Subst.instantiate inst #> Envir.beta_norm))
                    |> MetaRec.pattern_matches_opt thy |> is_some
                | NONE => false
              end)
      
      val Js_ct = setize_list thy @{typ "bool"} (matching_facts |> map (Thm.prop_of #> HOLogic.dest_Trueprop))
        |> cterm_of thy
      val res0 = @{thm collectHOLfacts_intI}
        |> Drule.instantiate' [] [SOME Js_ct, SOME pat0_ct]
      val assm = Goal.init (Thm.cprem_of res0 1)
        |> REPEAT_FIRST (resolve_tac ([@{thm allholdEmpty}, @{thm allholdInsert}] @ matching_facts))
        |> Seq.hd |> Goal.conclude
      val res = res0 OF [assm]
    in
      (res0 OF [assm], [Js_ct])
    end





  val setup = 
    Context.theory_map (
      MetaRec.add_lthy_transform "HOLMetaRecSyntax.typedef_const_jud" "typedef_lthytransf" typedef_lthytransf
      #> MetaRec.add_lthy_transform "HOLMetaRecSyntax.enum_datatype_jud" "enum_datatype_lthytransf" enum_datatype_lthytransf
      #> MetaRec.add_lthy_transform "HOLMetaRecSyntax.enumfun_const_jud" "enum_fun_lthytransf" enum_fun_lthytransf
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.tracing_jud" "tracing" tracing_proc
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.errwith_jud" "errwith_proc" errwith_proc
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.onfailerr_const_jud" "onfailerr_proc" onfailerr_proc
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.simpto_const_jud" "simpto_proc" (simpto_proc false)
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.powersimpto_const_jud" "powersimpto_proc" (simpto_proc true)
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.collectHOLfacts_int_jud" "collectHOLfacts_internal_proc" collectHOLfacts_proc
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.scopify_name_jud" "scopify_name_proc" scopify_name_proc
      #> MetaRec.add_syn_proc "HOLMetaRecSyntax.gen_fresh_jud" "gen_fresh_proc" gen_fresh_proc)

end
