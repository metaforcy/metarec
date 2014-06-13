
structure ZFUnifyData =
struct

  exception UnificationFailed of string

  fun meta_unify ctxt (t1, t2) env =
    (case MetaRec.try_pat_unify ctxt (t1, t2) env of
      SOME env2 => env2
    | NONE => error ("ZF.meta_unify: non-pattern problem "
        ^Syntax.string_of_term ctxt (Logic.mk_equals (t1, t2))))
    handle MetaRec.TryPatUnify (ctxt_, (t1_, t2_), msg) =>
      error ("ZF.meta_unify: "^msg)
      (*raise UnificationFailed msg*)

  fun onorm ctxt env t0 =
    let
      exception NormFail of string
      fun fail_cont ctxt_ msg = raise NormFail msg
      val t = Envir.norm_term env t0
    in
      let
        val ((_, [t']), _) = MetaRec.metarec_no_constraintsimp fail_cont ctxt
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
      case (MetaRec.metarec_no_constraintsimp fail_cont ctxt jud (t, []) |> SOME
          handle SynthFail => NONE)
      of
        SOME ((_, [oT]), ctxt2) =>
          (* FIXME: what about delayed_unifs and constraints in runstate of ctxt2?
             change architecture to runstate-Propagation instead
             of just env-Propagation? *)
          SOME oT 
      | NONE => NONE
     end

  (* FIXME: this assumes consistent variable generation, so at least we need
       to run constraint simplification, esp. typing constraint merge rule,
       on the constraints generated from previous synth_otyp calls *)
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
        (* case (MetaRec.metarec_no_constraintsimp fail_cont ctxt "UniverseLevelInference.subunify"
          (oT1, [oT2]) |> SOME
          handle RefineFail => NONE)
        of
           (* FIXME: what about delayed_unifs and constraints ? *)
           SOME ((_, [oT]), (delayed_unifs, constraints)) => true
         | NONE => false *)
     end
          

  fun is_top_otyp ctxt env t0 =
    case onorm ctxt env t0 of
      Const(@{const_name guniv}, _) $ _ => true
    | t => (case fastype_of t of
        Type("fun", [aT, _]) =>
          t aconv (Term.lambda (Free("x", aT)) @{term Trueprop(True)})
      | _ => false)
        


  fun mk_typ_assm x typ = 
    case fastype_of typ of
      @{typ "i"} => @{term synthty_const} $ x $ typ |> FOLogic.mk_Trueprop
    | Type("fun", [aT, _]) =>
        Const(@{const_name metasynthty_const},
          Sign.const_instance @{theory} (@{const_name metasynthty_const}, [aT]))
        $ x $ typ

  fun mk_oapp t1 t2 = @{term "op `"} $ t1 $ t2
  fun mk_olam (x, oT) body = @{term "Lambda"} $ oT $ Term.lambda x body
  (* FIXME?: case of meta type oT_opt missing? *)
  fun mk_mlam (x, oT_opt) body = case oT_opt of
      SOME oT => @{term "annot_metalam"} $ oT $ Term.lambda x body
    | NONE => Term.lambda x body

  fun mk_opi (x, A) body =
    @{term "ZF.Pi"} $ A $ Term.lambda x body

  fun mk_mpi (x, Aopt) body =
    let
      fun mem_pred A = @{term "op :"} $ x $ A
        |> FOLogic.mk_Trueprop |> Term.lambda x

      val aT = fastype_of x
      val (bT, body') = case fastype_of body of
          Type("fun", [bT, _]) => (bT, body)
        | @{typ "i"} => (@{typ "i"}, mem_pred body)
        | _ => error ("mk_mpi: internal error: expected function type for body "
           ^Syntax.string_of_term @{context} body
           ^" (x is "^Syntax.string_of_term @{context} x
              ^(Aopt |> Option.map (Syntax.string_of_term @{context} #> prefix " :: ")
                |> the_default "")^")")

      val Aopt' = Aopt |> Option.map (fn A => case fastype_of A of
          @{typ "i"} => mem_pred A
        | _ => A)

      val mPi_const =
        Const(@{const_name mPi}, 
          Sign.const_instance @{theory} (@{const_name mPi}, [aT, bT]))
      val body_abs = Term.lambda x body'
    in
      case Aopt' of
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



  (* not necessary with current architecture *)
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


