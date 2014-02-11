

signature STRUCT_UNIFY =
sig
  val unify: theory -> term * term -> Envir.env -> Envir.env
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
    (Envir.norm_term env (subst_bounds (map Free binders, t)));

fun bname binders i = fst (nth binders i);
fun bnames binders is = space_implode " " (map (bname binders) is);

fun typ_clash thy (tye,T,U) =
  if !trace_unify_fail
  then let val t = Syntax.string_of_typ_global thy (Envir.norm_type tye T)
           and u = Syntax.string_of_typ_global thy (Envir.norm_type tye U)
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

fun proj_fail thy (env,binders,F,_,is,t) =
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

fun occurs(F,t,env) =
    let fun occ(Var (G, T))   = (case Envir.lookup (env, (G, T)) of
                                 SOME(t) => occ t
                               | NONE    => F=G)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ t end;



fun env_abeconv env (t1,t2) = 
  Pattern.aeconv ((t1, t2) |> pairself (Envir.norm_term env))


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


(* TODO(feature): try to annotate generated abstractions with nice names from bounds and frees in ss *)
(* ss_absord has to be in the correct abstraction order:
     if an element occurs as a subterm of another element, it has to occur previously in ss_absord *)
fun reorder_open_abss binderTs ss ss_absord body =
  let
    val ctxt = Name.context |> fold Term.declare_term_names
      (body :: ss @ map Logic.mk_type binderTs)
    val bnd_ns = Name.invent ctxt "__boundfree0" (length binderTs)
    val ss_ns = Name.invent ctxt "__reordfree0" (length ss)

    val bnd_frees = bnd_ns ~~ binderTs |> map Free
    val subst = curry subst_bounds bnd_frees

    val ss_Ts = ss |> map (curry Term.fastype_of1 binderTs)
    val ss_frees_map = ss ~~ (ss_ns ~~ ss_Ts) |> map (fn (s, (n, T)) => (s, Free(n, T)))
    val ss_frees = map snd ss_frees_map
    val ss_frees_absord = ss_absord |> map (fn s =>
      case AList.lookup (op aconv) ss_frees_map s of
        SOME sfree => sfree
      | NONE => error ("struct_unify: internal error: no reordering Free found"))
  in
    body |> subst
    |> fold_rev (Term.lambda o subst) ss_absord
    |> (fn abs_body => list_comb (abs_body, ss_frees_absord))
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

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts);


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
    val tyenv = Envir.type_env env;
    val (Ts, U) = split_type (Envir.norm_type tyenv T, n, []);
  in map (nth Ts) is ---> U end;

fun mkhnf (binders,is,G,js) = mkabs (binders, is, app(G,js));

fun mknewhnf(env,binders,is,F as (a,_),T,js) =
  let val (env',G) = Envir.genvar a (env,type_of_G env (T,length is,js))
  in Envir.update (((F, T), mkhnf (binders, is, G, js)), env') end;


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
        fun pr(s,env,d,binders) = (case Envir.head_norm env s of
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
                          val (env',H) = Envir.genvar a (env,Hty)
                          val env'' =
                            Envir.update (((F, Fty), mkhnf (binders, js, H, ks)), env')
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
                 in Envir.update (((F, Fty), t), env) end
            else let val ks = inter (op =) js is
                     val Hty = type_of_G env (Fty,length is,map (idx is) ks)
                     val (env',H) = Envir.genvar a (env,Hty)
                     fun lam(is) = mkabs(binders,is,app(H,map (idx is) ks));
                 in Envir.update (((G, Gty), lam js), Envir.update (((F, Fty), lam is), env'))
                 end;
  in if Term_Ord.indexname_ord (G,F) = LESS then ff(F,Fty,is,G,Gty,js) else ff(G,Gty,js,F,Fty,is) end

fun unify_types thy (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  if T = U then env
  else
    let val (tyenv', maxidx') = Sign.typ_unify thy (U, T) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end
    handle Type.TUNIFY => (typ_clash thy (tyenv, T, U); raise Unif);

fun unif thy binders (s,t) env = case (Envir.head_norm env s, Envir.head_norm env t) of
      (Abs(ns,Ts,ts),Abs(nt,Tt,tt)) =>
         let val name = if ns = "" then nt else ns
         in unif thy ((name,Ts)::binders) (ts,tt) env end
    | (Abs(ns,Ts,ts),t) => unif thy ((ns,Ts)::binders) (ts,(incr t)$Bound(0)) env
    | (t,Abs(nt,Tt,tt)) => unif thy ((nt,Tt)::binders) ((incr t)$Bound(0),tt) env
    | p => cases thy (binders,env,p)

and cases thy (binders,env,(s,t)) = case (strip_comb s,strip_comb t) of
       ((Var(F,Fty),ss),(Var(G,Gty),ts)) =>
          if F = G then 
            flexflex1(env,binders,F,Fty,ints_of' env ss,ints_of' env ts)
            (* NB: structural instantiation would lead to cyclic instantiation here *)
          else
            (flexflex2(env,binders,F,Fty,ints_of' env ss,G,Gty,ints_of' env ts)
             handle Pattern => 
               if Term_Ord.indexname_ord (G,F) = LESS then
                 struct_inst thy binders ((F,Fty), ss) t env
               else
                 struct_inst thy binders ((G,Gty), ts) s env)
      | ((Var(F,Fty),ss),_) =>
          (flexrigid thy (env,binders,F,Fty,ints_of' env ss,t)
           handle Pattern => struct_inst thy binders ((F,Fty), ss) t env)
      | (_,(Var(F,Fty),ts)) =>
          (flexrigid thy (env,binders,F,Fty,ints_of' env ts,s)
           handle Pattern => struct_inst thy binders ((F,Fty), ts) s env)
      | ((Const c,ss),(Const d,ts))   => rigidrigid thy (env,binders,c,d,ss,ts)
      | ((Free(f),ss),(Free(g),ts))   => rigidrigid thy (env,binders,f,g,ss,ts)
      | ((Bound(i),ss),(Bound(j),ts)) => rigidrigidB thy (env,binders,i,j,ss,ts)
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
and liftvars_over thy (ss_Ts0, ss_bnds0) ss_invsubstmap0 binders lev term env =
  case strip_comb (Envir.head_norm env term) of
    (Var (ixn, T), ts0) =>
      let
        val ss_Ts = map (apfst (Term.incr_boundvars lev)) ss_Ts0
        val ss_bnds = map (fn i => i + lev) ss_bnds0
        val ss_invsubstmap = map (pairself (Term.incr_boundvars lev)) ss_invsubstmap0
        val ts = map (Envir.norm_term env) ts0

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
          |> Envir.norm_type (Envir.type_env env)
        val (env2, H) = Envir.genvar (fst ixn) (env, Hty)
        val Happ = list_comb (H, map fst ss_Ts_new @ ts')

        val ts_reord = filter Term.is_Bound ts @ filter_out Term.is_Bound ts
        val invsubst = Term.subst_free ss_invsubstmap
        val absHapp' = Happ |> invsubst
          |> reorder_open_abss (map snd binders) (map invsubst ts) (map invsubst ts_reord)

        (* val _ = tracing ("liftvars_over "^Syntax.string_of_term_global thy (Var(ixn, T))^" with "
          ^"\n  ts="^commas (map (Syntax.string_of_term_global thy) ts)
          ^"\n  ts'="^commas (map ( Syntax.string_of_term_global thy) ts')
          ^"\n  bnds="^commas (map string_of_int bnds)
          ^"\n  ss_bnds="^commas (map string_of_int ss_bnds)
          ^"\n  ss="^commas (map (fn (s, _) => Syntax.string_of_term_global thy s)
            ss_Ts)
          ^"\n  ss_new="^commas (map (fn (s, _) => Syntax.string_of_term_global thy s) ss_Ts_new)
          ^"\n  Happ="^Syntax.string_of_term_global thy Happ
          ^"\n  absHapp'="^Syntax.string_of_term_global thy absHapp') *)

        val env3 = Envir.update (((ixn, T), absHapp'), env2)
      in
        (Happ, env3)
      end
  | (Abs (x, T, t), []) =>
      let val (t', env2) =
        liftvars_over thy (ss_Ts0, ss_bnds0) ss_invsubstmap0 ((x, T) :: binders) (lev+1) t env
      in (Abs (x, T, t'), env2) end
  | (Abs _, _) => raise NotBetaNormal
  | (a, ts) =>
      let
        val _ =
          case a of
            Bound i =>
              if i <= lev orelse member (op =) ss_bnds0 (i - lev) then ()
              else raise Unif
          | _ => ()
        val (ts', env2) = env
          |> fold_map (liftvars_over thy (ss_Ts0, ss_bnds0) ss_invsubstmap0 binders lev) ts
      in
        (list_comb (a, ts'), env2)
      end

and struct_inst thy binders ((F, Fty), ss0) term0 env =
  if occurs (F, term0, env) then (ocheck_fail thy (F,term0,binders,env); raise Unif)
  else
    let
      val ss = map (Envir.norm_term env) ss0
      val term = Envir.norm_term env term0

      val ctxt = Name.context |> fold Term.declare_term_names
        ([Var(F,Fty), term] @ ss @ map (Logic.mk_type o snd) binders)

      (* val bnd_ns = Name.invent ctxt "_boundfree0" (length binders)
      val bnd_frees = bnd_ns ~~ binders |> map (fn (n, (x, T)) => Free(x^n, T))
      val subst_bnds = curry subst_bounds bnd_frees
      val abs_bnds = fold (curry Term.abstract_over) bnd_frees *)

      fun typeof s = fastype_of1 (map snd binders, s)
        |> Envir.norm_type (Envir.type_env env)

      val ss_bnds = ss |> map_filter (try dest_Bound) |> distinct (op =)
      val ss_nonbnds = ss |> filter_out Term.is_Bound
        |> filter (fn s => subset (op =) (Term.loose_bnos s, ss_bnds))

      (* NB: we introduce locally fresh fix variables for the different non-bound
         argument positions in  F $ ss  in order to lift over all argument positions
         of F even in the case of duplicates in ss. E.g.
           ?B x x == PROD y:?C. ?D y
         will be solved by
           ?B := (% z1 z2. (PROD y : ?C' z1 z2. ?D' z1 z2 y))
           ?C := ?C' x x
           ?D := ?D' x x  *)
      val ss_nbnds_ns = Name.invent ctxt "_varargfree0" (length ss_nonbnds)
      val ss_nbnds_substmap = ss_nonbnds ~~ ss_nbnds_ns |> map (fn (ss_nbnd, n') =>
        let
          val bnos = Term.loose_bnos ss_nbnd
          val free = Free(n', map (nth binders #> snd) bnos ---> typeof ss_nbnd)
        in
          (ss_nbnd, list_comb (free, map Bound bnos))
        end)
      val ss_nbnds_invsubstmap = map swap ss_nbnds_substmap
      val subst_ss = Term.subst_free ss_nbnds_substmap

      val (ss', _) = ss_nbnds_substmap |> map snd
        |> fold_map (fn s => fn rem_ss_nbnd_substs =>
            if can dest_Bound s then (s, rem_ss_nbnd_substs)
            else
              case rem_ss_nbnd_substs of
                (x :: rem_ss_nbnd_substs2) => (x, rem_ss_nbnd_substs2)
              | _ => error ("struct_unify: internal error: no substitution free found "
                ^"for non-bound variable argument position"))
          ss
      val ss'_reord = map Bound ss_bnds @ map snd ss_nbnds_substmap
      val ss'_reord_Ts = ss'_reord ~~ map typeof ss'_reord
      val term' = subst_ss term

      val (term'2, env2) =
        liftvars_over thy (ss'_reord_Ts, ss_bnds) ss_nbnds_invsubstmap binders 0 term' env
      val norm2 = Envir.norm_term env2
      val term'2_abs = norm2 term'2
        |> reorder_open_abss (map snd binders) (map norm2 ss') (map norm2 ss'_reord)
      (* NB: Fty does not have to be normed since var-clash check in Envir.lookup
         is modulo type normalization *)
      val env3 = Envir.update (((F, Fty), term'2_abs), env2)
    in env3 end
  


and rigidrigid thy (env,binders,(a,Ta),(b,Tb),ss,ts) =
      if a<>b then (clash a b; raise Unif)
      else env |> unify_types thy (Ta,Tb) |> fold (unif thy binders) (ss~~ts)

and rigidrigidB thy (env,binders,i,j,ss,ts) =
     if i <> j then (clashBB binders i j; raise Unif)
     else fold (unif thy binders) (ss~~ts) env

and flexrigid thy (params as (env,binders,F,Fty,is,t)) =
      if occurs(F,t,env) then (ocheck_fail thy (F,t,binders,env); raise Unif)
      else (let val (u,env') = proj(t,env,binders,is)
            in Envir.update (((F, Fty), mkabs (binders, is, u)), env') end
            handle Unif => (proj_fail thy params; raise Unif));

fun unify thy = unif thy [];


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



end
