
structure ZFUnifyData =
struct
  fun meta_unify ctxt (t1, t2) env =
    case MetaRec.try_pat_unify ctxt (t1, t2) env of
      SOME env2 => env2
    | NONE => error ("ZF.meta_unify: non-pattern problem "
        ^Syntax.string_of_term ctxt (Logic.mk_equals (t1, t2)))

  fun onorm ctxt env t0 =
    let
      exception NormFail of string
      fun fail_cont ctxt_ msg = raise NormFail msg
      val t = Envir.norm_term env t0
    in
      let
        val ((_, [t']), _) = MetaRec.metarec_with_failcont fail_cont ctxt
          "UniverseLevelInference.zfnorm_const_jud" (t, [])
      in t' end (* FIXME? t' fully normed? *)
      handle NormFail msg => 
        error ("onorm failed on "^Syntax.string_of_term ctxt t^"\n"^msg)
    end

  (* NB: assumes otypable term *)
  fun unsafe_onorm ctxt env t0 =
    let
      val t = Envir.norm_term env t0
      val rew = @{cpat "(lam x:?A. ?t(x)) ` ?a == ?t(?a)"}
        |> Thm.term_of |> Logic.dest_equals
    in
      Pattern.rewrite_term (Proof_Context.theory_of ctxt) [rew] [] t
    end

  fun synth_otyp ctxt env t =
    let
      val _ = tracing ("synth_otyp on "^Syntax.string_of_term ctxt (Envir.norm_term env t))
      val jud = 
        if fastype_of t = @{typ "i"}
        then "UniverseLevelInference.synthty_const_jud"
        else "UniverseLevelInference.metasynthty_const_jud"
      exception SynthFail
      fun fail_cont _ _ = raise SynthFail
    in
      case (MetaRec.metarec_with_failcont fail_cont ctxt jud (t, []) |> SOME
          handle SynthFail => NONE)
      of
        SOME ((_, [oT]), (delayed_unifs, constraints)) =>
          (* FIXME: what about delayed_unifs and constraints ?
             change architecture to runstate-Propagation instead
             of just env-Propagation? *)
          SOME oT 
      | NONE => NONE
     end

  fun refines_into_otyp ctxt env oT1 oT2 =
    let
      exception RefineFail
      fun fail_cont _ _ = raise RefineFail
      fun env_abeconv t1 t2 =
        Pattern.aeconv (onorm ctxt env t1, onorm ctxt env t2)
    in
      if fastype_of oT1 <> fastype_of oT2 then
        false
      else
        env_abeconv oT1 oT2
      (* FIXME? refining via subunify. can generate new constraints! *)
      (* else if fastype_of oT1 <> @{typ "i"} then *)
        (* case (MetaRec.metarec_with_failcont fail_cont "UniverseLevelInference.subunify"
          (oT1, [oT2]) |> SOME
          handle RefineFail => NONE)
        of
           (* FIXME: what about delayed_unifs and constraints ? *)
           SOME ((_, [oT]), (delayed_unifs, constraints)) => true
         | NONE => false *)
     end
          

  fun is_top_otyp ctxt env t0 =
    case onorm ctxt env t0 of
      Const(@{const_name guniv}, _) => true
    | _ => false


  fun mk_typ_assm x typ = 
    case fastype_of typ of
      @{typ "i"} => @{term synthty_const} $ x $ typ
    | Type("fun", [aT, _]) =>
        Const(@{const_name metasynthty_const},
          Sign.const_instance @{theory} (@{const_name metasynthty_const}, [aT]))
        $ x $ typ

  fun mk_oapp t1 t2 = @{term "op `"} $ t1 $ t2
  fun mk_olam (x, oT) body = @{term "Lambda"} $ oT $ Term.lambda x body
  fun mk_mlam (x, oT_opt) body = case oT_opt of
      SOME oT => @{term "annot_metalam"} $ oT $ Term.lambda x body
    | NONE => Term.lambda x body

  fun mk_opi (x, A) body = @{term "ZF.Pi"} $ A $ Term.lambda x body
  fun mk_mpi (x, Aopt) body =
    let
      val aT = fastype_of x
      val bT = case fastype_of body of
          Type("fun", [bT, _]) => bT
        | _ => error "mk_mpi: internal error: expected function type for body"
      val mPi_const =
        Const(@{const_name mPi}, 
          Sign.const_instance @{theory} (@{const_name mPi}, [aT, bT]))
      val body_abs = Term.lambda x body
    in
      case Aopt of
        SOME A => mPi_const $ A $ body_abs
      | NONE => mPi_const $ (Term.lambda x @{term "Trueprop(True)"}) $ body_abs
    end

  fun dest_oapp (Const(@{const_name "ZF.apply"}, _) $ t1 $ t2) =
        SOME (t1, t2)
    | dest_oapp _ = NONE

  fun dest_opi (Const(@{const_name "ZF.Pi"}, _) $ A $ body) =
        SOME (A, body)
    | dest_opi _ = NONE

  fun dest_mpi (Const(@{const_name "UniverseLevelInference.mPi"}, _) $ P $ body) =
      let
        val argty_opt = case P of
            Abs(_, _, Const(@{const_name "Trueprop"}, _) $ Const(@{const_name "True"}, _)) =>
              NONE
          | _ => SOME P
       in
          SOME (argty_opt, body)
       end
    | dest_mpi _ = NONE



  (* fun binder_descent ctxt env t0 =
    let val t = onorm ctxt env t0
    in
      (* TODO: (cached):
             * find synthty rule matching input t
               (perhaps let user declare binder synthty rules)
             * search for "the binder premise", which has a synthty assumption
               (if there is none t is not a binder, if there
                are serveral the rule seems wrong)
             * assume all the synthty assumptions of the binder premise
               in ctxt as local metarec rules (reuse that part of MetaRec.solve_prems?) *)
    end *)

  (* fun extract_relevant_fix_otyping_for_otyps ctxt ts =
    let
      val xs = [] |> fold Term.add_free ts
      val vs = [] |> fold Term.add_vars ts
    in
      (* TODO: search synthty/metasynthty rule for xs, vs (fixed?) in MetaRec.rule_net of ctxt *)
    end *)
    

end



structure ZF_Unify = ObjLangUnify(ZFUnifyData);


