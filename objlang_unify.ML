

(* summary: take arbitrary unification modulo beta as parameter
     and transform it to a unification modulo beta, object-lang-beta:
      * normalize wrt. beta,object-lang-beta
      * map object-lang-variable-applications to meta-lang-variable-applications
        via transformational variable instantiation with a corresponding
        object-lang-abstraction
      * run unification modulo beta
      * typecheck variable instantiation and undo transformational
        variable instantiation *)
     
(* TODO(feature):
     unification modulo object-lang-eta is harder to achieve modularly
     (but also less important):
       * preprocess to object-lang-eta-long-normal form  ?
       * or provide employ on-the-fly object-lang-eta-expansion to the
         (instantiated generic) unification  ?  *)


(* FIXME: we have to be able to represent universe level annotations on olam, opi binders.
  Make information on olam, opi binders polymorphic instead of term-valued and allow
  coercion of this information to mlam, mpi binder information. *)
signature ObjLangUnifyData =
sig

  exception UnificationFailed of string

  (* NB: we assume that meta_unify also unifies the meta types of the terms *)
  val meta_unify : Proof.context -> term * term -> Envir.env -> Envir.env
  val onorm : Proof.context -> Envir.env -> term -> term
  (* NB: we assume unsafe_onorm is only called on otypable terms and does not
     need otyping computations, so no otyping assumptions in the context
     are necessary. This means the obeta computation has to be expressible
     as a purely syntactic rewrite on otypeable terms. *)
  val unsafe_onorm : Proof.context -> Envir.env -> term -> term
  (* NB: unification vars may also need otyps as well as frees *)
  val synth_otyp : Proof.context -> Envir.env -> term -> term option * Proof.context
  val refines_into_otyp : Proof.context -> Envir.env -> term -> term -> bool * Proof.context
  val is_top_otyp : Proof.context -> Envir.env -> term -> bool

  (* NB: has to be able to create judgements for typing unification variables into oPis *and* mPis *)
  val mk_typ_assm : term -> term -> term
  val mk_oapp : term -> term -> term
  val mk_olam : term * term -> term -> term
  (* meta abstraction, potentially annotated with otype for bound *)
  val mk_mlam : term * term option -> term -> term 
  val mk_opi : term * term -> term -> term
  (* NB: mk_mpi is expected to convert an object-level type (for body or binder)
     to a meta-level type as needed *)
  val mk_mpi : term * term option -> term -> term

  val dest_oapp : term -> (term * term) option
  (* val dest_olam : term -> (term * term) option
  val dest_mlam : term -> (term option * term) option *)
  val dest_opi : term -> (term * term) option
  val dest_mpi : term -> (term option * term) option



  (* the following functions would allow stepwise enrichment of the context
     with otyping assumptions when descending under binders and the extraction 
     of these assumptions. Not needed ATM, because we can use unsafe_onorm
     in metafy_oapps, which does not need otyping computations. *)

  (* NB: we assume that this Variable.variant_fixes bound variables that we descend into,
    returns to the fixed "body term" and registers metarec assumptions declaring the type
    synthesis of the bound variables *)
  (* val binder_descent : Proof.context -> Envir.env -> term -> (term, Proof.context) option *)

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

fun gen_strip_pis_hlp dest rev_telescope oT ctxt =
  case dest oT of
    SOME (arg_oT, Abs(x, T, body)) =>
      let
        val ([x'], ctxt2) = Variable.variant_fixes [x] ctxt
        val free = Free (x', T)
        val body' = Term.subst_bound (free, body)
      in gen_strip_pis_hlp dest ((free, arg_oT) :: rev_telescope) body' ctxt2 end
  | _ => ((rev_telescope, oT), ctxt)

fun gen_strip_pis dest oT ctxt = gen_strip_pis_hlp dest [] oT ctxt
  |> apfst (apfst rev)

in

val strip_mpis = gen_strip_pis Data.dest_mpi
val strip_opis = gen_strip_pis Data.dest_opi

end


(* TODO(refactor): shared with struct_unify.ML (and private in term.ML) *)
fun term_name (Const (x, _)) = Long_Name.base_name x
  | term_name (Free (x, _)) = x
  | term_name (Var ((x, _), _)) = x
  | term_name _ = Name.uu;



fun the_otyp ctxt msgprefix t (SOME otyp) = otyp
  | the_otyp ctxt msgprefix t NONE = error (msgprefix^": "^Syntax.string_of_term ctxt t
      ^" has no object-level type but is used in an object-level application")

(* NB: assumes Variable.declared, onormed, otypable term
     and otyping assumptions in ctxt about oapplied unification variables *)
fun metafy_oapps ctxt term (metafy_tab, env) =
  case (term |> Data.unsafe_onorm ctxt env |> strip_oapps |> apfst strip_comb) of
    ((Var _, _), []) => (metafy_tab, env)
  | ((Var (v as (ixn as (vn, _), vT)), args), oargs) =>
      (* v := (mlam xs1 : oTs1. olam xs2 : oTs2. v' $ xs1 $ xs2)
         where v : (MPI xs1 : oTs1. PI xs2 : oTs2. B) *)
      let
        val v_oT = Data.synth_otyp ctxt env (Var v) |> the_otyp ctxt "metafy_oapps" (Var v)
        val ((mpi_telescope, v_oT_mpis_stripped), ctxt2_) = ctxt |> strip_mpis v_oT
        val ((pi_telescope, v_oT_stripped), _) = ctxt2_ |> strip_opis v_oT_mpis_stripped

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

        val v'T = telescope_Ts mpi_telescope ---> telescope_Ts rel_pi_telescope
          ---> body_type vT
        val v'_oT = v_oT_stripped
          |> fold_rev Data.mk_mpi (mpi_telescope @ map (apsnd SOME) pi_telescope)
        val (env2, v' as Var(ixn', _)) = Envir.genvar vn (env, v'T)
        val inst = list_comb (v', map fst mpi_telescope @ map fst rel_pi_telescope)
          |> fold_rev Data.mk_olam rel_pi_telescope
          |> fold_rev Data.mk_mlam mpi_telescope

        val env3 = Envir.update (((ixn, vT), inst), env2)
        val metafy_tab2 = metafy_tab |> Vartab.update (ixn', ((v'T, v'_oT), (v, v_oT)))
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




(* NB: assumes Variable.declared t1_0, t2_0
     and VarTypings in ctxt for the unification variables in t1_0, t2_0 *)
(* NB: assumes metarec run state in ctxt *)
(* TODO(correctness): propagate exceptions from synth_otyp, onorm, meta_unify ?? *)
fun obj_unify ctxt (t1_0, t2_0) env =
  let
    val _ = tracing ("obj_unify on "^commas ([t1_0, t2_0] |> map (MetaRec.str_of_normed_term ctxt)))
    (* TODO(feature): treat case of t1_0, t2_0 inhabiting a non-object meta type *)
    val (oT1, oT2) = (t1_0, t2_0)
      |> pairself (fn t_ => Data.synth_otyp ctxt env t_ |> the_otyp ctxt "obj_unify" t_)
    (* TODO(opt!): if t1_0 = t2_0 then we are done and do not need to unify their types *)
    val env2 = 
      (* TODO(feature): handle unification errors here and reraise them, stating that
        this refers to unification of types of (t1_0, t2_0) *)
      if Data.is_top_otyp ctxt env oT1 andalso Data.is_top_otyp ctxt env oT2 then
        Data.meta_unify ctxt (oT1, oT2) env
      else
        obj_unify ctxt (oT1, oT2) env

    (* TODO(opt): onorm-ing seems essential here, in particular to ensure otypability 
         of t1_0, t2_0 under env2. But can env2 invalidate the otypablitily
         of t1_0, t2_0 under env, even if it resulted from an obj_unify of oT1, oT2 ? *)
    val (t1, t2) = (t1_0, t2_0) |> pairself (Data.onorm ctxt env2)

    val (metafy_tab, env3) = (Vartab.empty, env2)
      |> fold (metafy_oapps ctxt) [t1, t2]
    val ctxt_metafied = ctxt |> MetaRec.add_assm_terms_internal  
       (Vartab.dest metafy_tab |> map (fn (ixn', ((v'T, v'_oT), _)) =>
           Data.mk_typ_assm (Var(ixn', v'T)) v'_oT |> MetaRec.mk_exact_rule))
    val (t1', t2') = (t1, t2) |> pairself (Data.onorm ctxt_metafied env3)

    val env4 = Data.meta_unify ctxt_metafied (t1', t2') env3 

    (* TODO(refactor): envdiff shared with metarec.ML *)
    val envdiff = env4 |> Envir.term_env
      |> fold Vartab.delete (Vartab.keys (Envir.term_env env3))

    val envdiff_graph = Var_Graph.empty
      |> Vartab.fold (fn (ixn', _) => Var_Graph.new_node (ixn', ())) envdiff
      |> Vartab.fold (fn (ixn', (T, t)) =>
             fold (fn (ixn2, _) => (Vartab.defined envdiff ixn2) ?  Var_Graph.add_edge (ixn', ixn2))
               (Term.add_vars t []))
           envdiff
    val envdiff_reord = Var_Graph.strong_conn envdiff_graph |> rev |> map (fn comp =>
      case comp of
        [ixn] => (case Vartab.lookup envdiff ixn of
            SOME (T, t) => (ixn, (T, t))
          | NONE => error ("obj_unify: internal error: variable environment graph contains unknown variable"))
     | _ => error ("obj_unify: internal error: variable environment after meta unification is cyclic"))

    val env' = env4 |> fold (fn (ixn', (v'T0, t0)) => fn env_ =>
        case Vartab.lookup metafy_tab ixn' of
          SOME (_, (v as (ixn, vT0), v_oT)) => 
            (* v' := t  ~~>  v := t'
               where v : (MPI xs1 : oTs1. PI xs2 : oTs2. B)
                 and t' := (mlam xs1 : oTs1. olam xs2 : oTs2. t $ xs1 $ xs2) *)
            let
              (* NB: metafied vars from t0 are gone in t due to construction of env_ *)
              val t = Envir.norm_term env_ t0
              val vT = Envir.norm_type (Envir.type_env env_) vT0

              val ((mpi_telescope, v_oT_mpis_stripped), ctxt2_) = ctxt |> strip_mpis v_oT
              val ((pi_telescope, _), _) = ctxt2_ |> strip_opis v_oT_mpis_stripped

              val t' = list_comb (t, map fst mpi_telescope @ map fst pi_telescope)
                |> fold_rev Data.mk_olam pi_telescope
                |> fold_rev Data.mk_mlam mpi_telescope

              val t'_oT = Data.synth_otyp ctxt env_ t' |> the_otyp ctxt "obj_unify" t'
            in
              if Data.refines_into_otyp ctxt env_ t'_oT v_oT then
                (* NB: v' binding remains in env_ to avoid interference with
                     non-metafy-related parts of env4 *)
                env_ |> curry Envir.update ((ixn, vT0), t')
              else
                error ("obj_unify: instantiation "
                  ^Syntax.string_of_term ctxt (Var (ixn', v'T0))^" := "^Syntax.string_of_term ctxt t
                  ^" found by the meta unification is not object-type correct:"
                  ^" expected variable object-type "^Syntax.string_of_term ctxt v_oT
                  ^" but instantiation derived term with object-type "
                  ^Syntax.string_of_term ctxt
                    (Data.synth_otyp ctxt env_ t |> the_otyp ctxt "obj_unify" t)
                  ^", which after transformation results in object-type "
                  ^Syntax.string_of_term ctxt t'_oT)
            end
        | NONE => env_)
      envdiff_reord
  in
    env'
  end





end
