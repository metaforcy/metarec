

signature STRUCT_UNIFY =
sig
  type flexflex
  val term_name: term -> string
    (* bool = false for fallback to pattern unification *)
  val unify: bool -> theory -> term * term -> EnvDiff.env * flexflex list -> EnvDiff.env * flexflex list
  val solve_delayed_flexflexs: theory -> flexflex list -> EnvDiff.env -> EnvDiff.env
  val term_eq_of_flexflex: flexflex -> term

  val pattern_unify_envdiff : theory -> term * term -> EnvDiff.env -> EnvDiff.env

  exception Unif
  exception NotBetaNormal
  exception Pattern
end;

structure StructUnify: STRUCT_UNIFY =
struct

exception Unif;
exception Pattern;
exception NotBetaNormal;

val trace_unify_fail = Unsynchronized.ref false;

fun string_of_term thy env binders t =
  Syntax.string_of_term_global thy
    (EnvDiff.norm_term env (subst_bounds (map Free binders, t)));

fun bname binders i = fst (nth binders i);
fun bnames binders is = space_implode " " (map (bname binders) is);

fun typ_clash thy env (T,U) =
  if !trace_unify_fail
  then let val t = Syntax.string_of_typ_global thy (EnvDiff.norm_type env T)
           and u = Syntax.string_of_typ_global thy (EnvDiff.norm_type env U)
       in tracing("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ()

fun clash a b =
  if !trace_unify_fail then tracing("Clash: " ^ a ^ " =/= " ^ b) else ()

fun boundVar binders i =
  "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")";

fun clashBB binders i j =
  if !trace_unify_fail then clash (boundVar binders i) (boundVar binders j)
  else ()

fun clashB binders i s =
  if !trace_unify_fail then clash (boundVar binders i) s
  else ()

fun proj_fail thy binders (F,_,is,t) (env, delayed_flexflexs) =
  if !trace_unify_fail
  then let val f = Term.string_of_vname F
           val xs = bnames binders is
           val u = string_of_term thy env binders t
           val ys = bnames binders (subtract (op =) is (loose_bnos t))
       in tracing("Cannot unify variable " ^ f ^
               " (depending on bound variables " ^ xs ^ ")\nwith term " ^ u ^
               "\nTerm contains additional bound variable(s) " ^ ys)
       end
  else ()

fun ocheck_fail thy (F,t,binders,env) =
  if !trace_unify_fail
  then let val f = Term.string_of_vname F
           val u = string_of_term thy env binders t
       in tracing("Variable " ^ f ^ " occurs in term\n" ^ u ^
                  "\nCannot unify!\n")
       end
  else ()

fun occurs env F t =
    let fun occ(Var (G, T))   = (case EnvDiff.lookup env (G, T) of
                                 SOME(t) => occ t
                               | NONE    => F=G)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ t end;



fun env_abeconv env (t1,t2) = 
  Pattern.aeconv ((t1, t2) |> pairself (EnvDiff.norm_term env))


(*Abstraction of the term "body" over its occurrences of v,
    which may contain loose bound variables.
  The resulting term is ready to become the body of an Abs.*)
fun abstract_over_open (v, body) =
  let
    fun abs v2 lev tm =
      if v2 aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (Term.incr_boundvars 1 v2) (lev + 1) t)
        | t $ u =>
            (abs v2 lev t $ (abs v2 lev u handle Same.SAME => u)
              handle Same.SAME => t $ abs v2 lev u)
        | _ => raise Same.SAME);
  in abs v 0 body handle Same.SAME => body end;


(* from Pure/term.ML *)
fun term_name (Const (x, _)) = Long_Name.base_name x
  | term_name (Free (x, _)) = x
  | term_name (Var ((x, _), _)) = x
  | term_name _ = Name.uu;


fun lambda_name_open binderTs (x, v) t =
  Abs (if x = "" then term_name v else x,
    Term.fastype_of1 (binderTs, v),
    abstract_over_open (v, t));

fun lambda_open binderTs v t = lambda_name_open binderTs ("", v) t;


fun dest_Bound (Bound i) = i
  | dest_Bound _ = error "dest_Bound"

fun reord_name_from_term binders s = case s of
    Free(n, _) => n
  | Var((n, _), _) => n
  | Const(n,_) => n
  | Bound i => nth binders i |> fst
  | _ => "__reordfree0"


fun reorder_open_abss binders ss ss_reord body =
  let
    val binderTs = map snd binders
    val ctxt = Name.context |> fold Term.declare_term_names
      (body :: ss @ map Logic.mk_type binderTs)
    val (bnd_ns, ctxt2) = ctxt |> fold_map (Name.variant o fst) binders
    val (ss_ns, _) = ctxt2 |> fold_map (Name.variant o reord_name_from_term binders) ss

    val bnd_frees = bnd_ns ~~ binderTs |> map Free
    val subst = curry subst_bounds bnd_frees

    val ss_Ts = ss |> map (curry Term.fastype_of1 binderTs)
    val ss_frees_map = ss ~~ (ss_ns ~~ ss_Ts) |> map (fn (s, (n, T)) => (s, Free(n, T)))
    val ss_frees = map snd ss_frees_map
    val ss_frees_reord = ss_reord |> map (fn s =>
      case AList.lookup (op aconv) ss_frees_map s of
        SOME sfree => sfree
      | NONE => error ("struct_unify: internal error: no reordering Free found for a var argument"))
  in
    body |> subst
    |> fold_rev (Term.lambda o subst) ss_reord
    |> (fn abs_body => list_comb (abs_body, ss_frees_reord))
    |> fold_rev Term.lambda ss_frees
    |> Envir.beta_norm
  end



fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun idx [] j     = raise Unif
  | idx(i::is) j = if (i:int) =j then length is else idx is j;

fun mkabs (binders,is,t)  =
    let fun mk(i::is) = let val (x,T) = nth binders i
                        in Abs(x,T,mk is) end
          | mk []     = t
    in mk is end;

val incr = mapbnd (fn i => i+1);

fun ints_of []             = []
  | ints_of (Bound i ::bs) =
      let val is = ints_of bs
      in if member (op =) is i then raise Pattern else i::is end
  | ints_of _              = raise Pattern;

fun ints_of' env ts = ints_of (map (EnvDiff.head_norm env) ts);


fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (nth jn) t,is);


(* split_type ([T1,....,Tn]---> T,n,[]) = ([Tn,...,T1],T) *)
fun split_type (T,0,Ts)                    = (Ts,T)
  | split_type (Type ("fun",[T1,T2]),n,Ts) = split_type (T2,n-1,T1::Ts)
  | split_type _                           = error("split_type");

fun type_of_G env (T, n, is) =
  let
    val (Ts, U) = split_type (EnvDiff.norm_type env T, n, []);
  in map (nth Ts) is ---> U end;

fun mkhnf (binders,is,G,js) = mkabs (binders, is, app(G,js));

fun mknewhnf(env,binders,is,F as (a,_),T,js) =
  let val (G, env2) = EnvDiff.genvar a (type_of_G env (T,length is,js)) env
  in EnvDiff.update ((F, T), mkhnf (binders, is, G, js)) env2 end;


(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;

(*mk_proj_list(is) = [ |is| - k | 1 <= k <= |is| and is[k] >= 0 ]*)
fun mk_proj_list is =
    let fun mk(i::is,j) = if is_some i then j :: mk(is,j-1) else mk(is,j-1)
          | mk([],_)    = []
    in mk(is,length is - 1) end;

fun proj(s,env,binders,is) =
    let fun trans d i = if i<d then i else (idx is (i-d))+d;
        fun pr(s,env,d,binders) = (case EnvDiff.head_norm env s of
              Abs(a,T,t) => let val (t',env') = pr(t,env,d+1,((a,T)::binders))
                            in (Abs(a,T,t'),env') end
            | t => (case strip_comb t of
                (c as Const _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(c,ts'),env') end
                 | (f as Free _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(f,ts'),env') end
                 | (Bound(i),ts) =>
                         let val j = trans d i
                             val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(Bound j,ts'),env') end
                 | (Var(F as (a,_),Fty),ts) =>
                      let val js = ints_of' env ts;
                          val js' = map (try (trans d)) js;
                          val ks = mk_proj_list js';
                          val ls = map_filter I js'
                          val Hty = type_of_G env (Fty,length js,ks)
                          val (H,env') = EnvDiff.genvar a Hty env
                          val env'' =
                            EnvDiff.update ((F, Fty), mkhnf (binders, js, H, ks)) env'
                      in (app(H,ls),env'') end
                 | _  => raise NotBetaNormal))
        and prs(s::ss,env,d,binders) =
              let val (s',env1) = pr(s,env,d,binders)
                  val (ss',env2) = prs(ss,env1,d,binders)
              in (s'::ss',env2) end
          | prs([],env,_,_) = ([],env)
   in if downto0(is,length binders - 1) then (s,env)
      else pr(s,env,0,binders)
   end;


(* mk_ff_list(is,js) = [ length(is) - k | 1 <= k <= |is| and is[k] = js[k] ] *)
fun mk_ff_list(is,js) =
    let fun mk([],[],_)        = []
          | mk(i::is,j::js, k) = if (i:int) = j then k :: mk(is,js,k-1)
                                        else mk(is,js,k-1)
          | mk _               = error"mk_ff_list"
    in mk(is,js,length is-1) end;

fun flexflex1(env,binders,F,Fty,is,js) =
  if is=js then env
  else let val ks = mk_ff_list(is,js)
       in mknewhnf(env,binders,is,F,Fty,ks) end;

fun flexflex2(env,binders,F,Fty,is,G,Gty,js) =
  let fun ff(F,Fty,is,G as (a,_),Gty,js) =
            if subset (op =) (js, is)
            then let val t= mkabs(binders,is,app(Var(G,Gty),map (idx is) js))
                 in EnvDiff.update ((F, Fty), t) env end
            else let val ks = inter (op =) js is
                     val Hty = type_of_G env (Fty,length is,map (idx is) ks)
                     val (H,env') = EnvDiff.genvar a Hty env
                     fun lam(is) = mkabs(binders,is,app(H,map (idx is) ks));
                 in
                   env'
                   |> EnvDiff.update ((F, Fty), lam is)
                   |> EnvDiff.update ((G, Gty), lam js)
                 end;
  in if Term_Ord.indexname_ord (G,F) = LESS then ff(F,Fty,is,G,Gty,js) else ff(G,Gty,js,F,Fty,is) end

(* assumes normed Fty, Gty *)
fun smash_flexflex ((F, Fty), argsF) ((G, Gty), argsG) env =
  let
    fun smashing_abss varT num_appargs smashvar = 
      let val smashed_binderTs = take num_appargs (Term.binder_types varT)
      in smashvar |> fold_rev (fn T => fn t => Abs("", T, t)) smashed_binderTs end

    val smashed_binderTs = take (length argsF) (Term.binder_types Fty)
    val (smashvar, env2) = EnvDiff.genvar (fst F)
      (drop (length argsF) (Term.binder_types Fty) ---> Term.body_type Fty) env
    val F_smashing_abss = smashing_abss Fty (length argsF) smashvar
    val G_smashing_abss = smashing_abss Gty (length argsG) smashvar

    val env3 = EnvDiff.update ((F, Fty), F_smashing_abss) env2
  in
    if F = G then env3 (* the other update would be identical *)
    else
      EnvDiff.update ((G, Gty), G_smashing_abss) env3
  end

type flexflex = (string * typ) list * (((indexname * typ) * term list) * ((indexname * typ) * term list))

fun unify_types thy (T, U) (env, delayed_flexflexs) =
  if T = U then (env, delayed_flexflexs)
  else
    (EnvDiff.typ_unify thy (U, T) env, delayed_flexflexs)
    handle Type.TUNIFY => (typ_clash thy env (T, U); raise Unif);

fun unif struct_unif thy binders (s,t) (env, delayed_flexflexs) =
    case (EnvDiff.head_norm env s, EnvDiff.head_norm env t) of
      (Abs(ns,Ts,ts),Abs(nt,Tt,tt)) =>
         let val name = if ns = "" then nt else ns
         in unif struct_unif thy ((name,Ts)::binders) (ts,tt) (env, delayed_flexflexs) end
    | (Abs(ns,Ts,ts),t) =>
        unif struct_unif thy ((ns,Ts)::binders) (ts,(incr t)$Bound(0)) (env, delayed_flexflexs)
    | (t,Abs(nt,Tt,tt)) =>
        unif struct_unif thy ((nt,Tt)::binders) ((incr t)$Bound(0),tt) (env, delayed_flexflexs)
    | p => cases struct_unif thy binders p (env, delayed_flexflexs)

and cases struct_unif thy binders (s,t) (env, delayed_flexflexs) =
      case (strip_comb s,strip_comb t) of
       ((Var(F,Fty),ss),(Var(G,Gty),ts)) =>
          if F = G then 
            ((flexflex1(env,binders,F,Fty,ints_of' env ss,ints_of' env ts),
              delayed_flexflexs)
             handle Pattern =>
               if not struct_unif then raise Pattern
               else if env_abeconv env (s, t) then (env, delayed_flexflexs)
               else
                 (* NB: structural instantiation would lead to cyclic instantiation in this case *)
                 (* we employ opportunistic smash unification because this situation occurs
                    prominently in type inference for e.g.  f # x === f # y,  as this results
                    in constraints  ?B(x) == ?B(y),  f : (PROD x:?A. ?B(x)),  x : ?A,  y : ?A,
                    which we smash-unify via ?B := (% _. ?B2) *)
                 let
                   val Fty' = Fty |> EnvDiff.norm_type env
                 in
                   (* TODO(feature): more general dependency-restriction-solution useful here? *)
                   (smash_flexflex ((F, Fty'), ss) ((F, Fty'), ts) env, delayed_flexflexs)
                 end)
          else
            ((flexflex2(env,binders,F,Fty,ints_of' env ss,G,Gty,ints_of' env ts),
              delayed_flexflexs)
             handle Pattern =>
               if not struct_unif then raise Pattern
               else
                 (env, delayed_flexflexs @ [ (binders, (((F,Fty), ss), ((G,Gty), ts))) ]))
                 (* NB: the following also works, but results in overly general types
                    for  f # x == g # y (due to constraint ?B(x) == ?C(y)) *)
                 (* if Term_Ord.indexname_ord (G,F) = LESS then
                   struct_inst thy binders ((F,Fty), ss) t env
                 else
                   struct_inst thy binders ((G,Gty), ts) s env) *)
      | ((Var(F,Fty),ss),_) =>
          (flexrigid thy binders (F,Fty,ints_of' env ss,t) (env, delayed_flexflexs)
           handle Pattern =>
             if not struct_unif then raise Pattern
             else
               (struct_inst thy binders ((F,Fty), ss) t env, delayed_flexflexs))
      | (_,(Var(F,Fty),ts)) =>
          (flexrigid thy binders (F,Fty,ints_of' env ts,s) (env, delayed_flexflexs)
           handle Pattern =>
             if not struct_unif then raise Pattern
             else
               (struct_inst thy binders ((F,Fty), ts) s env, delayed_flexflexs))
      | ((Const c,ss),(Const d,ts))   =>
          rigidrigid struct_unif thy binders (c,d,ss,ts) (env, delayed_flexflexs)
      | ((Free(f),ss),(Free(g),ts))   =>
          rigidrigid struct_unif thy binders (f,g,ss,ts) (env, delayed_flexflexs)
      | ((Bound(i),ss),(Bound(j),ts)) =>
          rigidrigidB struct_unif thy binders (i,j,ss,ts) (env, delayed_flexflexs)
      | ((Abs(_),_),_)                => raise NotBetaNormal
      | (_,(Abs(_),_))                => raise NotBetaNormal
      | ((Const(c,_),_),(Free(f,_),_)) => (clash c f; raise Unif)
      | ((Const(c,_),_),(Bound i,_))   => (clashB binders i c; raise Unif)
      | ((Free(f,_),_),(Const(c,_),_)) => (clash f c; raise Unif)
      | ((Free(f,_),_),(Bound i,_))    => (clashB binders i f; raise Unif)
      | ((Bound i,_),(Const(c,_),_))   => (clashB binders i c; raise Unif)
      | ((Bound i,_),(Free(f,_),_))    => (clashB binders i f; raise Unif)

(* NB: this is slightly conservative in that we don't recognize acceptable Bound-dependencies via (?X i) in ss
     in accordance with the Unif exception raised in proj *)
and liftvars_over thy binders lev (ss_Ts0, ss_bnds0) term env =
  case strip_comb (EnvDiff.head_norm env term) of
    (Var (ixn, T), ts0) =>
      let
        val ss_Ts = map (apfst (Term.incr_boundvars lev)) ss_Ts0
        val ss_bnds = map (fn i => i + lev) ss_bnds0
        val ts = map (EnvDiff.norm_term env) ts0

        val bnds =
          (0 upto lev-1) @ inter (op =) ss_bnds (map_filter (try dest_Bound) ts)
        fun bounds_avail t_ = subset (op =) (Term.loose_bnos t_, bnds)
        val ss_Ts_new = ss_Ts |> filter (fn (s, _) =>
          if Term.is_Bound s then
            dest_Bound s >= lev andalso bounds_avail s
          else
            bounds_avail s andalso not (member (env_abeconv env) ts s))
        val ts' = ts |> map_filter (fn t =>
          if Term.is_Bound t andalso dest_Bound t >= lev then NONE
          else SOME t)


        val typeof = curry fastype_of1 (map snd binders)
        val Ts' = ts' |> map typeof
        val Hty = map snd ss_Ts_new ---> Ts' ---> drop (length ts) (binder_types T)
            ---> body_type T
          |> EnvDiff.norm_type env
        val (H, env2) = EnvDiff.genvar (fst ixn) Hty env
        val Happ = list_comb (H, map fst ss_Ts_new @ ts')

        val ts_reord = filter Term.is_Bound ts @ filter_out Term.is_Bound ts
        val absHapp = Happ
          |> reorder_open_abss binders ts ts_reord

        (* val _ = tracing ("liftvars_over "^Syntax.string_of_term_global thy (Var(ixn, T))^" with "
          ^"\n  ts="^commas (map (Syntax.string_of_term_global thy) ts)
          ^"\n  ts'="^commas (map ( Syntax.string_of_term_global thy) ts')
          ^"\n  bnds="^commas (map string_of_int bnds)
          ^"\n  ss_bnds="^commas (map string_of_int ss_bnds)
          ^"\n  ss="^commas (map (fn (s, _) => Syntax.string_of_term_global thy s)
            ss_Ts)
          ^"\n  ss_new="^commas (map (fn (s, _) => Syntax.string_of_term_global thy s) ss_Ts_new)
          ^"\n  Happ="^Syntax.string_of_term_global thy Happ
          ^"\n  Habs="^Syntax.string_of_term_global thy absHapp) *)

        val env3 = EnvDiff.update ((ixn, T), absHapp) env2
      in
        env3
      end
  | (Abs (x, T, t), []) =>
      liftvars_over thy ((x, T) :: binders) (lev+1) (ss_Ts0, ss_bnds0) t env
  | (Abs _, _) => raise NotBetaNormal
  | (a, ts) =>
      let val _ =
        case a of
          Bound i =>
            if i <= lev orelse member (op =) ss_bnds0 (i - lev) then ()
            else raise Unif
        | _ => ()
      in
        fold (liftvars_over thy binders lev (ss_Ts0, ss_bnds0)) ts env
      end

(* TODO(opt): only lift over those ss_reord that are "small", because sharing of
    "large" terms is unlikely to correspond to type dependency *)
(* TODO(correctness?): should we order ss_nonbnds according to the occurence in each other? *)
(* TODO(feature): would it be possible and useful to delay struct_insts in order
   to execute them in order of dependencies of lhs vars wrt. to lhs var arguments?
   This only changes the structure of the resulting instantiation, does not
   influence its existence, but would make it independent of occurrence-based order
   of struct_insts.  *)
(* canonical example: the structural instantiation solution for  ?X(t) == (PROD x:?A. ?B(x))  is
      ?X := (% t. PROD x:?A'(t). ?B'(t, x))
      ?A := ?A'(t)   "propagating the dependency on t"
      ?B := ?B'(t)
      ?A', ?B' fresh  *)
and struct_inst thy binders ((F, Fty), ss0) term env =
  if occurs env F term then (ocheck_fail thy (F,term,binders,env); raise Unif)
  else
    let
      val ss = map (EnvDiff.norm_term env) ss0
      fun typeof s = fastype_of1 (map snd binders, s)
        |> EnvDiff.norm_type env

      val ss_bnds = ss |> map_filter (try dest_Bound) |> distinct (op =)
      val ss_nonbnds = ss |> filter_out Term.is_Bound
        |> filter (fn s => subset (op =) (Term.loose_bnos s, ss_bnds))
        (* TODO(feature): useful? *)
        (* |> distinct (env_aeconv env) *)
      val ss_reord = map Bound ss_bnds @ ss_nonbnds
      val ss_reord_Ts = ss_reord ~~ map typeof ss_reord

      val env2 = liftvars_over thy binders 0 (ss_reord_Ts, ss_bnds) term env
      val norm2 = EnvDiff.norm_term env2
      val term'_abs = norm2 term
        |> reorder_open_abss binders (map norm2 ss) (map norm2 ss_reord)
      (* NB: Fty does not have to be normed since var-clash check in EnvDiff.lookup
         is modulo type normalization *)
      val env3 = EnvDiff.update ((F, Fty), term'_abs) env2
      val _ = tracing ("struct_inst: "
        ^Syntax.string_of_term_global thy (Var (F,Fty))
        ^" := "^Syntax.string_of_term_global thy term'_abs)
    in env3 end
  


and rigidrigid struct_unif thy binders ((a,Ta),(b,Tb),ss,ts) (env, delayed_flexflexs) =
      if a<>b then (clash a b; raise Unif)
      else
        (env, delayed_flexflexs)
        |> unify_types thy (Ta,Tb)
        |> fold (unif struct_unif thy binders) (ss~~ts)

and rigidrigidB struct_unif thy binders (i,j,ss,ts) (env, delayed_flexflexs) =
     if i <> j then (clashBB binders i j; raise Unif)
     else
       (env, delayed_flexflexs) |> fold (unif struct_unif thy binders) (ss~~ts)

and flexrigid thy binders (F,Fty,is,t) (env, delayed_flexflexs) =
      if occurs env F t then
        (ocheck_fail thy (F,t,binders,env); raise Unif)
      else
        (let val (u,env') = proj(t,env,binders,is)
         in
           (EnvDiff.update ((F, Fty), mkabs (binders, is, u)) env',
            delayed_flexflexs)
         end
         handle Unif =>
          (proj_fail thy binders (F,Fty,is,t) (env, delayed_flexflexs); 
           raise Unif));

fun solve_flexflex thy (binders, (((F,Fty), ss), ((G,Gty), ts))) env = 
  let
    val (ss', ts') = pairself (map (EnvDiff.norm_term env)) (ss, ts)
    val (Fty', Gty') = (Fty, Gty) |> pairself (EnvDiff.norm_type env)

    (* NB: we intersect dependencies (i.e. generalizing
       the treatment in pattern unification), so that e.g.
       f # x == g # x results in f, g : (PROD x:A. B(x))
         (due to constraint ?B(x) == ?C(x)) 
       and f # x == g # y results in f : ?X -> ?D, g : ?Y -> ?D
         (due to constraint ?B(x) == ?C(y)) *)
    fun dep_restr_sol (v1, args1) (v2, args2) env =
      let
        val ctxt = Name.context |> fold Term.declare_term_names
          ([Var v1, Var v2] @ args1 @ args2 @ map (snd #> Logic.mk_type) binders)
        val (bnd_ns, _) = ctxt |> fold_map (Name.variant o fst) binders
        val bnd_frees = bnd_ns ~~ (map snd binders) |> map Free
        val subst = curry subst_bounds bnd_frees

        val (args1', args2') = pairself (map subst) (args1, args2)
        val common_args = inter (op aconv) args1' args2'
        val (v1_binderTs, v1_bodyT) = Term.strip_type (snd v1)
        val (newvar, env2) = EnvDiff.genvar (fst (fst v1))
          (map fastype_of common_args ---> drop (length args1') v1_binderTs ---> v1_bodyT)
          env

        val common_body = list_comb(newvar, common_args)
        val t1 = common_body |> fold_rev Term.lambda args1'
        val t2 = common_body |> fold_rev Term.lambda args2'

        val env3 = EnvDiff.update (v1, t1) env2
        val env4 = EnvDiff.update (v2, t2) env3
        val _ = tracing ("flexflex2 dependency restriction solution for "
          ^Syntax.string_of_term_global thy
            (Logic.mk_equals (list_comb ((Var v1), args1'), list_comb ((Var v2), args2')))
          ^":   "
          ^Syntax.string_of_term_global thy (Var v1)^" := " ^Syntax.string_of_term_global thy t1
          ^Syntax.string_of_term_global thy (Var v2)^" := " ^Syntax.string_of_term_global thy t2)
      in
        env4
      end

    (* this seems to be the most general solution, but it is so general that it needs postprocessing:
       in constraints changed by this unification solution perform dependency restriction, i.e.
         deprestr t A ==> t <: A
       which happens in constraint regeneration case for metarec constraint simp. *)
    (* f # x == g # x  results in f, g : (PROD x:A. B(x))
          due to constraints ?B0(x) == ?C0(x)
       f # x == g # y  results in f : A -> C',  g : B -> C'
          due to constraint ?C0(x) == ?C1(y) that leads to solution
            ?C0 := (% x. ?C(x,y)), ?C1 := (% y. ?C(x,y))
          which is deprestr to ?C := (% x y. C') during subsequent simplification of
          constraints f : PROD x:A. ?C(x,y), g : PROD y:B. ?C(x,y) *)
    fun dep_accum_sol (v1, args1) (v2, args2) env =
      let
        val ctxt = Name.context |> fold Term.declare_term_names
          ([Var v1, Var v2] @ args1 @ args2 @ map (snd #> Logic.mk_type) binders)
        val (bnd_ns, _) = ctxt |> fold_map (Name.variant o fst) binders
        val bnd_frees = bnd_ns ~~ (map snd binders) |> map Free
        val subst = curry subst_bounds bnd_frees

        val (args1', args2') = pairself (map subst) (args1, args2)
        val common_args = inter (op aconv) args1' args2'
        val common_bnds = inter (op =) common_args bnd_frees
        fun avail t = subset (op =) (
          inter (op =) (Term.add_frees t [] |> map Free) bnd_frees,
          common_bnds)
        val accum_args = union (op aconv) (filter avail args1') (filter avail args2')

        val (v1_binderTs, v1_bodyT) = Term.strip_type (snd v1)
        val (newvar, env2) = EnvDiff.genvar (fst (fst v1))
          (map fastype_of accum_args ---> drop (length args1') v1_binderTs ---> v1_bodyT)
          env

        val unified_body = list_comb(newvar, accum_args)
        val t1 = unified_body |> fold_rev Term.lambda args1'
        val t2 = unified_body |> fold_rev Term.lambda args2'

        val env3 = EnvDiff.update (v1, t1) env2
        val env4 = EnvDiff.update (v2, t2) env3
        val _ = tracing ("flexflex2 dependency accumulation solution for "
          ^Syntax.string_of_term_global thy
            (Logic.mk_equals (list_comb ((Var v1), args1'), list_comb ((Var v2), args2')))
          ^":\n  "^Syntax.string_of_term_global thy (Var v1)^" := " ^Syntax.string_of_term_global thy t1
          ^"\n  "^Syntax.string_of_term_global thy (Var v2)^" := " ^Syntax.string_of_term_global thy t2)
      in
        env4
      end
  in
    dep_restr_sol ((F,Fty'), ss') ((G,Gty'), ts') env
  end

fun flexflex_eq_to_term_eq (((F,Fty), ss), ((G,Gty), ts)) =
  (list_comb (Var(F,Fty), ss), list_comb (Var(G,Gty), ts))

fun term_eq_of_flexflex (binders, flexflex_eq) = 
  flexflex_eq_to_term_eq flexflex_eq
  |> Logic.mk_equals
  |> curry Logic.list_all binders

val flexflex_eq = pairself term_eq_of_flexflex #> op aconv

fun unify_flexflex thy (binders, flexflex_eq) =
  unif true thy binders (flexflex_eq_to_term_eq flexflex_eq)

fun solve_delayed_flexflexs thy delayed_flexflexs env = 
  case delayed_flexflexs of
    [] => env
  | flexflex :: delayed_flexflexs' =>
      let
        val (env_, delayed_flexflex_) = unify_flexflex thy flexflex (env, [])
        fun flexflex_gone_case () = solve_delayed_flexflexs thy
          (delayed_flexflexs' @ delayed_flexflex_) env_
      in
        case delayed_flexflex_ of 
          [flexflex'] =>
            if flexflex_eq (flexflex, flexflex') then
              let
                val env2 = solve_flexflex thy flexflex env
                val (env3, delayed_flexflexs2) = (env2, [])
                  |> fold (unify_flexflex thy) delayed_flexflexs'
              in
                solve_delayed_flexflexs thy delayed_flexflexs2 env3
              end
            else
              flexflex_gone_case ()
        | _ => flexflex_gone_case ()
      end

fun unify struct_unif thy = unif struct_unif thy []


(* put a term into eta long beta normal form *)
fun eta_long Ts (Abs (s, T, t)) = Abs (s, T, eta_long (T :: Ts) t)
  | eta_long Ts t =
      (case strip_comb t of
        (Abs _, _) => eta_long Ts (Envir.beta_norm t)
      | (u, ts) =>
          let
            val Us = binder_types (fastype_of1 (Ts, t));
            val i = length Us;
          in
            fold_rev (Term.abs o pair "x") Us
              (list_comb (incr_boundvars i u, map (eta_long (rev Us @ Ts))
                (map (incr_boundvars i) ts @ map Bound (i - 1 downto 0))))
          end);



fun pattern_unify_envdiff thy (t1, t2) env =
  case unify false thy (t1, t2) (env, []) of
    (env2, []) => env2
  | _ => error ("pattern_unify_envdiff: internal error: delayed flexflex pairs")


end
