

(* summary: take arbitrary unification modulo beta as parameter
     and transform it to a unification modulo beta, object-lang-beta:
      * normalize wrt. beta,object-lang-beta
      * map object-lang-variable-applications to meta-lang-variable-applications
        via transformational variable instantiation with a corresponding
        object-lang-abstraction
      * run unification modulo beta
      * typecheck variable instantiation and undo transformational
        variable instantiation
      * simplify constraints of instantiated obj-lang-var to
        calculate constraints of newly generated vars *)
     
(* TODO(feature):
     unification modulo object-lang-eta is harder to achieve modularly
     (but also less important):
       * preprocess to object-lang-eta-long-normal form  ?
       * or provide employ on-the-fly object-lang-eta-expansion to the
         (instantiated generic) unification  ?  *)


signature ObjLangUnifyData =
sig

  type otyp_ann
  type mtyp_ann
  val otyp_to_mtyp_ann : otyp_ann -> mtyp_ann
  (* val otyp_ann_term : otyp_ann -> term
  val mtyp_ann_term : otyp_ann -> term *)

  exception UnificationFailed of string
  exception SynthFail of Proof.context * string

  val env_from_ctxt: Proof.context -> EnvDiff.env
  val map_env_in_ctxt: (EnvDiff.env -> EnvDiff.env) -> Proof.context -> Proof.context

  (* NB: we assume that meta_unify also unifies the meta types of the terms *)
  val meta_unify : Proof.context -> term * term -> EnvDiff.env -> EnvDiff.env
  val onorm : Proof.context -> term -> term
  (* NB: we assume unsafe_onorm is only called on otypable terms and does not
     need otyping computations, so no otyping assumptions in the context
     are necessary. This means the obeta computation has to be expressible
     as a purely syntactic rewrite on otypeable terms. *)
  val unsafe_onorm : Proof.context -> term -> term
  (* NB: unification vars (and not just frees) may have assigned otyps in context *)
  val synth_otyp : Proof.context ->  term -> term  (* raises SynthFail *)
  val refine_into_otyp : term -> term -> Proof.context -> Proof.context option
  val is_top_otyp : Proof.context -> term -> bool

  (* NB: has to be able to create judgements that assign unification variables
     oPis or mPis as types *)
  val mk_typ_assm : term -> term -> term
  val mk_oapp : term -> term -> term
  val mk_olam : term * otyp_ann -> term -> term
  (* meta abstraction, potentially annotated with otype for bound *)
  val mk_mlam : term * mtyp_ann option -> term -> term 
  val mk_opi : term * otyp_ann -> term -> term
  (* NB: mk_mpi is expected to convert an object-level type (for body or binder)
     to a meta-level type as needed *)
  val mk_mpi : term * mtyp_ann option -> term -> term

  val dest_oapp : term -> (term * term) option
  (* val dest_olam : term -> (term * term) option
  val dest_mlam : term -> (term option * term) option *)
  val dest_opi : term -> (otyp_ann * term) option
  val dest_mpi : term -> (mtyp_ann option * term) option



  (* the following functions would allow stepwise enrichment of the context
     with otyping assumptions when descending under binders and the extraction 
     of these assumptions. Not needed ATM, because we can use unsafe_onorm
     in metafy_oapps, which does not need otyping computations. *)

  (* NB: we assume that this Variable.variant_fixes bound variables that we descend into,
    returns to the fixed "body term" and registers metarec assumptions declaring the type
    synthesis of the bound variables *)
  (* val binder_descent : Proof.context -> EnvDiff.env -> term -> (term, Proof.context) option *)

  (* in telescopic left-to-right order *)
  (* val extract_relevant_fix_otypings_for_otyps : Proof.context -> term list
       -> (term * term option) list *)
end


functor ObjLangUnify(Data : ObjLangUnifyData) =
struct


fun strip_oapps t =
  case Data.dest_oapp t of
    SOME (t1, t2) =>
      strip_oapps t1 |> apsnd (fn ts => ts @ [t2])
  | NONE => (t, [])


local 

fun gen_strip_pis dest oT ctxt =
  case dest oT of
    SOME (arg_oT, Abs(x, T, body)) =>
      let
        val ([x'], ctxt2) = Variable.variant_fixes [x] ctxt
        val free = Free (x', T)
        val body' = Term.subst_bound (free, body)
      in
        gen_strip_pis dest body' ctxt2
        |> (apfst o apfst) (cons (free, arg_oT))
      end
  | _ => (([], oT), ctxt)

in

val strip_mpis = gen_strip_pis Data.dest_mpi
val strip_opis = gen_strip_pis Data.dest_opi

fun strip_mpis_opis ctxt oT = 
  let
    val ((mpi_telescope, oT_mpis_stripped), ctxt2) = ctxt |> strip_mpis oT
    val ((pi_telescope, oT_stripped), _) = ctxt2 |> strip_opis oT_mpis_stripped
  in ((mpi_telescope, pi_telescope), oT_stripped) end


end


(* TODO(refactor): shared with struct_unify.ML (and private in term.ML) *)
fun term_name (Const (x, _)) = Long_Name.base_name x
  | term_name (Free (x, _)) = x
  | term_name (Var ((x, _), _)) = x
  | term_name _ = Name.uu;



fun synth_otyp_wrapped msgprefix ctxt t =
  Data.synth_otyp ctxt t
  handle Data.SynthFail (ctxt2, msg) =>
    MetaRec.err_with_trace ctxt2 (msgprefix^": "^Syntax.string_of_term ctxt2 t
      ^" has no object-level type but is used in an object-level application because\n"
      ^msg)

(* NB: assumes Variable.declared, onormed, otypable term
     and otyping assumptions in ctxt about oapplied unification variables *)
fun metafy_oapps ctxt0 term (metafy_tab, env) =
  let val ctxt = ctxt0 |> Data.map_env_in_ctxt (K env)
  in
  case (term |> Data.unsafe_onorm ctxt |> strip_oapps |> apfst strip_comb) of
    ((Var _, _), []) => (metafy_tab, env)
  | ((Var (v as (ixn as (vn, _), vT)), args), oargs) =>
      (* v := (mlam xs1 : oTs1. olam xs2 : oTs2. v' $ xs1 $ xs2)
         where v : (MPI xs1 : oTs1. PI xs2 : oTs2. B) *)
      let
        val v_oT = synth_otyp_wrapped "metafy_oapps" ctxt (Var v)
        val ((mpi_telescope, pi_telescope), v_oT_stripped) = strip_mpis_opis ctxt v_oT

        val _ =
          if length args <> length mpi_telescope then
            error ("metafy_oapps: internal error: size of meta product telescope"
              ^" not equal to number of meta applications")
          else ()
        val _ =
          if length oargs > length pi_telescope then
            error ("metafy_oapps: internal error: object product telescope"
              ^" smaller than number of object applications")
          else ()

        val rel_pi_telescope = pi_telescope |> take (length oargs)
        fun telescope_Ts telescope = map (fst #> fastype_of) telescope

        val v'_T = telescope_Ts mpi_telescope ---> telescope_Ts rel_pi_telescope
          ---> body_type vT
        val v'_oT = v_oT_stripped
          |> fold_rev Data.mk_mpi (mpi_telescope
               @ map (apsnd (SOME o Data.otyp_to_mtyp_ann)) pi_telescope)
        val (v' as Var(ixn', _), env2) = EnvDiff.genvar vn v'_T env
        val inst = list_comb (v', map fst mpi_telescope @ map fst rel_pi_telescope)
          |> fold_rev Data.mk_olam rel_pi_telescope
          |> fold_rev Data.mk_mlam mpi_telescope

        val env3 = EnvDiff.update ((ixn, vT), inst) env2
        val metafy_tab2 = metafy_tab |> Vartab.update (ixn', ((v'_T, v'_oT), (v, v_oT)))
      in
        (metafy_tab2, env3)
        |> fold (metafy_oapps ctxt) (args @ oargs)
      end
  | ((Abs (x, T, body), []), []) =>
      let 
        val ([x'], ctxt2) = ctxt |> Variable.variant_fixes [x]
        val body' = Term.subst_bound (Free(x', T), body)
      in metafy_oapps ctxt2 body' (metafy_tab, env) end
  | ((Abs _, _), _) => error "metafy_oapps: internal error: term not beta normal"
  | ((a, args), oargs) =>
      (metafy_tab, env) |> fold (metafy_oapps ctxt) (args @ oargs)
  end




(* NB: assumes Variable.declared t1_0, t2_0
     and potential otyping constraints in ctxt for the unification variables in t1_0, t2_0 *)
(* NB: assumes metarec run state in ctxt *)
(* TODO(correctness): propagate exceptions from synth_otyp, onorm, meta_unify ?? *)
fun obj_unify (t1_0, t2_0) ctxt =
  let
    val _ = tracing ("obj_unify on "^commas ([t1_0, t2_0] |> map (MetaRec.str_of_normed_term ctxt)))
    (* TODO(feature): treat case of t1_0, t2_0 inhabiting a non-object meta type *)
    val (oT1, oT2) = (t1_0, t2_0) |> pairself (synth_otyp_wrapped "obj_unify" ctxt)
    (* TODO(opt!): if t1_0 = t2_0 then we are done and do not need to unify their types *)
    val ctxt2 = 
      (* TODO(feature): handle unification errors here and reraise them, stating that
        this refers to unification of types of (t1_0, t2_0) *)
      if Data.is_top_otyp ctxt oT1 andalso Data.is_top_otyp ctxt oT2 then
        ctxt |> Data.map_env_in_ctxt (Data.meta_unify ctxt (oT1, oT2))
      else
        obj_unify (oT1, oT2) ctxt

    (* TODO(opt): onorm-ing seems essential here, in particular to ensure otypability 
         of t1_0, t2_0 under env2. But can env2 invalidate the otypability
         of t1_0, t2_0 under env, even if it resulted from an obj_unify of oT1, oT2 ? *)
    val (t1, t2) = (t1_0, t2_0) |> pairself (Data.onorm ctxt2)

    val env2 = Data.env_from_ctxt ctxt2
    val (metafy_tab, env3) = (Vartab.empty, env2)
      |> fold (metafy_oapps ctxt2) [t1, t2]
    val ctxt3 = ctxt2 |> Data.map_env_in_ctxt (K env3)

    val ctxt3_metafied = ctxt3 |> MetaRec.add_assm_terms_internal  
      (Vartab.dest metafy_tab |> map (fn (ixn', ((v'_T, v'_oT), _)) =>
        Data.mk_typ_assm (Var(ixn', v'_T)) v'_oT |> MetaRec.mk_exact_rule))
    val (t1', t2') = (t1, t2) |> pairself (Data.onorm ctxt3_metafied)

    val ((envdiff_ixns, _), env4) = env3 |> EnvDiff.with_diff_slot "meta_unify_diffslot"
      (Data.meta_unify ctxt3 (t1', t2'))
    val ctxt4 = ctxt3 |> Data.map_env_in_ctxt (K env4)


    val used_uninst_metafy_vars = []
      |> fold (fn ixn' =>
             case EnvDiff.lookup_wotype env4 ixn' of
               SOME (T, _) =>
                 let val t2 = EnvDiff.norm_term env4 (Var (ixn', T))
                 in Term.add_vars t2 end
             | NONE => I)
           envdiff_ixns
      |> filter (fn (ixn', _) => Vartab.defined metafy_tab ixn')

    (* NB: we go for a fully normalizing transform of metafy-unifvar bindings.
         The alternative to non-normalizingly transform unifvar bindings to be un-metafied
         is more complex and would only result in slightly smaller env which should
         not matter in practice.
       TODO(opt?): test performance effects of a non-normalizing transform of
         unifvar bindings to be un-metafied *)
    (* NB: unifvars newly generated during unification, which are
       not constrained a priori and potentially get inferred constraints if their
       are used in an instantiation of a constrained unifvar. *)
    val ctxt' = ctxt4
      |> fold (fn v' as (ixn', _) => fn ctxt_ =>
             (* non-instantiated metafy unifvars occuring in instantiation are unmetafied first *)
             case Vartab.lookup metafy_tab ixn' of
               SOME (_, (v, v_oT)) =>
                 let
                   (*  v' := (mlam (xs1:oTs1) (xs2:oTs2). (v xs1) ` xs2)
                       where v : (MPI xs1 : oTs1. PI xs2 : oTs2. B)  *)
                   val ((mpi_telescope, pi_telescope), _) = strip_mpis_opis ctxt_ v_oT
                   val env_ = Data.env_from_ctxt ctxt_
                   val reabs_v = list_comb (Var v, map fst mpi_telescope)
                     |> fold (fn (x, _) => fn t_ => Data.mk_oapp t_ x) pi_telescope
                     |> fold_rev Data.mk_mlam (mpi_telescope
                          @ map (apsnd (SOME o Data.otyp_to_mtyp_ann)) pi_telescope)
                     |> EnvDiff.norm_term env_
                 in
                   ctxt_ |> Data.map_env_in_ctxt (EnvDiff.update (v', reabs_v))
                 end
             | NONE => error ("objlang_unify: internal error: used_uninst_metafy_vars incorrectly calculated"))
           used_uninst_metafy_vars
      |> fold (fn ixn' => fn ctxt_ =>
             case Vartab.lookup metafy_tab ixn' of
               NONE => ctxt_
             | SOME ((v'_T0, v'_oT), (v as (ixn, v_T0), v_oT)) => 
                 (* v' := t  ~~>  v := t'
                    where v : (MPI xs1 : oTs1. PI xs2 : oTs2. B)
                      and t' := (mlam xs1 : oTs1. olam xs2 : oTs2. t $ xs1 $ xs2) *)
                 let
                   val ((mpi_telescope, pi_telescope), _) = strip_mpis_opis ctxt_ v_oT
                   val env_ = Data.env_from_ctxt ctxt_
                   val v' = (ixn', v'_T0)
                   val t = EnvDiff.norm_term env_ (Var v')

                   (* TODO(opt): unsafe_onorm safe here modulo instantiation? *)
                   val t' = list_comb (t, map fst mpi_telescope @ map fst pi_telescope)
                     |> fold_rev Data.mk_olam pi_telescope
                     |> fold_rev Data.mk_mlam mpi_telescope
                     |> Data.onorm ctxt_ 

                   val t'_oT = synth_otyp_wrapped "obj_unify" ctxt_ t'
                 in
                   case Data.refine_into_otyp t'_oT v_oT ctxt_ of
                     SOME ctxt_2 =>
                       (* NB: v' binding remains in env_ to avoid interference with
                          normalization of unifvar bindings to terms containing it *)
                       ctxt_2 |> Data.map_env_in_ctxt (EnvDiff.update (v, t'))
                   | NONE =>
                       error ("obj_unify: instantiation "
                         ^Syntax.string_of_term ctxt_ (Var (ixn', v'_T0))^" := "^Syntax.string_of_term ctxt_ t
                         ^" found by the meta unification is not object-type correct:"
                         ^" expected variable object-type "^Syntax.string_of_term ctxt_ v_oT
                         ^" but instantiation derived term with object-type "
                         ^Syntax.string_of_term ctxt_ (synth_otyp_wrapped "obj_unify" ctxt_ t)
                         ^", which after transformation results in object-type "
                         ^Syntax.string_of_term ctxt_ t'_oT)
                 end)
           envdiff_ixns

    (* FIXME: do constraint simplification of ctxt' here to discover non-otypability
       of instantiation found by meta_unify.
       Can constraint simplification convert otyping constraints for non-metafied unifvars
       that have been imitated and proj-restricted in (pattern unification) meta_unify?
         ?f := (lam xs : As. ?B(xs')) <: PROD xs : As. B(xs')
           ~>  ?B <: MPROD xs':As'. B(xs')
         ?f := (lam xs : As. t[vec{?H_i(xs)}]) <: PROD xs : As. B(xs)
           ~>  vec{ ?H_i <: MPROD xs:As. B_i(xs) }
           only implemented for t=lam, missing for t containing app or const with otyping
       Works even for structural instantiations?
          ?X := (% t. PROD x:?A'(t). ?B'(t, x)) <: C -> guniv(i)
            ~>  ?A' <: C m-> guniv(i),  ?B' <: MPROD t:C. ?A'(t) m-> guniv(i)
     *)

    val ctxt'' = ctxt' |> Data.map_env_in_ctxt (EnvDiff.unsafe_map_tenv
      (fold (fn ixn' => (Vartab.defined metafy_tab ixn') ? Vartab.delete ixn') envdiff_ixns))
  in
    ctxt''
  end





end
