
signature DECOMP_PATTERN =
sig
  val decompose_match_w_shared_vars: theory -> term * term -> EnvDiff.env -> EnvDiff.env
  val match_w_shared_vars: theory -> term * term -> EnvDiff.env -> EnvDiff.env

  exception NotBetaNormal
  exception NonDistinctVars of term * term
end;

structure DecompPattern: DECOMP_PATTERN =
struct


exception NotBetaNormal
exception NonDistinctVars of term * term

fun string_of_term thy env binders t =
  Syntax.string_of_term_global thy
    (EnvDiff.norm_term env (subst_bounds (map Free binders, t)));

val trace_match_fail = Unsynchronized.ref false;


fun ocheck_fail_matching thy (F,t,binders,env) =
  if !trace_match_fail
  then let val f = Term.string_of_vname F
           val u = string_of_term thy env binders t
       in tracing("Variable " ^ f ^ " occurs in term\n" ^ u ^
                  "\nCannot match!\n")
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




fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun idx [] j     = raise Pattern.MATCH
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
      in if member (op =) is i then raise Pattern.Pattern else i::is end
  | ints_of _              = raise Pattern.Pattern;

(* TODO(opt): head norming arguments of unifvars in patterns is
   unnecessary because we do not normalize pattern at all here.
   But since we check that they are bounds, deep variable bindings
   cannot happen and this does not constitute a bug. *)
fun ints_of' env ts = ints_of (map (EnvDiff.head_norm env) ts);


fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (nth jn) t,is);




(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;


(*** Matching ***)

fun typ_match thy TU env = EnvDiff.typ_match thy TU env
  handle Type.TYPE_MATCH => raise Pattern.MATCH;



(* Matching of higher-order patterns *)

fun match_bind binders (ixn,T) is t env =
  let val js = loose_bnos t
  in
    if null is then
      if null js then EnvDiff.update ((ixn, T), t) env
      else raise Pattern.MATCH
    else
      if subset (op =) (js, is) then
        let val t' =
          if downto0(is,length binders - 1) then t
          else mapbnd (idx is) t
        in EnvDiff.update ((ixn, T), mkabs (binders, is, t')) env end
      else raise Pattern.MATCH
  end;





(* unused *)
fun first_order_match_w_shared_vars thy =
  let
    fun mtch k env (pat, obj0) =
      let val obj = obj0 |> EnvDiff.head_norm env
      in mtch_aux k env (pat, obj) end
    and mtch_aux k env = fn
        (Var(ixn,T), t)  =>
          if k > 0 andalso Term.is_open t then raise Pattern.MATCH
          else
           (case EnvDiff.lookup' env (ixn, T) of
             NONE =>
               env |> typ_match thy (T, fastype_of t)
               |> EnvDiff.update ((ixn, T), t)
           | SOME u => if Pattern.aeconv (t, u) then env else raise Pattern.MATCH)
      | (Free (a,T), Free (b,U)) =>
          if a=b then env |> typ_match thy (T,U) else raise Pattern.MATCH
      | (Const (a,T), Const (b,U))  =>
          if a=b then env |> typ_match thy (T,U) else raise Pattern.MATCH
      | (Bound i, Bound j)  =>  if  i=j  then  env  else raise Pattern.MATCH
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch (k + 1) (typ_match thy (T,U) env) (t,u)
      | (f$t, g$u) => mtch k (mtch k env (f,g)) (t, u)
      | (t, Abs(_,U,u))  =>  mtch (k + 1) env ((incr t)$(Bound 0), u)
      | _ => raise Pattern.MATCH
  in fn tu => fn env => mtch 0 env tu end;




(* matching were variables with same identity in pat and obj are regarded as shared
  NB: no deep variable bindings, as this would correspond to unification, so we only norm the object *)
fun gen_match_w_shared_vars is_decompose_match thy (po as (pat,obj)) env0 =
  let
    (* Pre: pat and obj have same type *)
    fun mtch binders (pat, obj0) env =
      let 
        (* NB: we normalize in order to regard common variables in object and pattern as shared.
           Only object is normalized to avoid deep matching, which would correspond to unification. *)
        val obj = obj0 |> EnvDiff.head_norm env
      in
        case pat of
          Abs(ns,Ts,ts) =>
            (case obj of
               Abs(nt,Tt,tt) => mtch ((nt,Tt)::binders) (ts, tt) env
            | _ =>
              if is_decompose_match then raise Pattern.MATCH
              else
                let val Tt = EnvDiff.subst_type env Ts
                in mtch ((ns,Tt)::binders) (ts, incr obj $ Bound 0) env end)
        | _ => (case obj of
                  Abs(nt,Tt,tt) =>
                    mtch ((nt,Tt)::binders) (incr pat $ Bound 0, tt) env
               | _ => cases binders env pat obj)
      end

    and cases binders env pat obj =
      let
        val (ph,pargs) = strip_comb pat
        val (oh,oargs) = strip_comb obj
        fun rigrig1 env_ = fold (mtch binders) (pargs~~oargs) env_
          handle ListPair.UnequalLengths => raise Pattern.MATCH
        fun rigrig2 ((a,Ta), (b,Tb)) =
          if a <> b then raise Pattern.MATCH
          else env |> typ_match thy (Ta, Tb) |> rigrig1
      in
        case ph of
          Var(ixn,T) =>
            let
              fun varmatch () = 
                let
                  val _ =
                    if occurs env ixn obj then
                      (ocheck_fail_matching thy (ixn,obj,binders,env);
                      raise Pattern.MATCH)
                    else ()
                in 
                  case (SOME (ints_of pargs)
                    handle Pattern.Pattern => NONE)
                  of
                    SOME is => (case EnvDiff.lookup' env (ixn, T) of
                        NONE => env |> match_bind binders (ixn,T) is obj
                      | SOME u =>
                          (* Need for normalization here should hardly arise in practice
                             but it avoids failure (?A := g(?B) =/= g(b)) of
                                f(?A) :match f(g(?B))
                                ?A :match g(b) 
                                with previous instantiation is ?B := b *)
                          if Pattern.aeconv ((obj, red u is []) |> pairself (EnvDiff.norm_term env))
                          then env
                          else raise Pattern.MATCH)
                  | NONE => (case pat of
                        (* pat is non-pattern, so we degrade to local first-order matching *)
                        pat1 $ pat2 => (case obj of
                          obj1 $ obj2 =>
                            let val typ_of = curry fastype_of1 (map snd binders)
                            in
                              env
                              |> typ_match thy (typ_of pat1, typ_of obj1)
                              |> fold (mtch binders) ([pat1, pat2] ~~ [obj1, obj2])
                            end
                        | _ => raise Pattern.MATCH)
                      | _ => error ("gen_match_w_shared_vars: internal error: pattern arguments are "
                        ^"non-bounds but no pattern application found"))
                 end
            in
              case oh of
                Var(ixn2,_) =>
                  if ixn = ixn2 then rigrig1 env (*raise NonDistinctVars (pat, obj)*)
                  else varmatch ()
              | _ => varmatch ()
            end
        | _ => (case (ph,oh) of
            (Const c,Const d) => rigrig2 (c,d)
          | (Free f,Free g)   => rigrig2 (f,g)
          | (Bound i,Bound j) =>
              if i<>j then raise Pattern.MATCH
              else rigrig1 env
          (* NB: if the term were beta-normal here, i.e. just an abstraction without arguments,
             we would have already descended into the abstraction in mtch *)
          | (Abs _, _)        => raise NotBetaNormal
          | (_, Abs _)        => raise NotBetaNormal
          | _                 => raise Pattern.MATCH)
      end;

  in
    env0
    |> typ_match thy (fastype_of pat, fastype_of obj)
    |> mtch [] po
  end;


val match_w_shared_vars = gen_match_w_shared_vars false


(* same as match_w_shared_var, except: no eta expansion of object.
   But pattern is on-the-fly eta-expanded, which corresponds
   to eta-contraction of the object. So decompose_match corresponds to
   higher-order pattern matching modulo beta, while eta-contracting
   the object on the fly.
   first_order_match also only eta-expands the pattern, so we can fallback on it
   for non-patterns
   
   Why the name? We want to regard lambda as a syntactic construct which is
   to be decomposed structurally instead of being introduced on-the-fly via
   eta-expansion!
     E.g.    f does not match (% x. ?t(x))
             but (% x. f(x)) does via ?t:=f
*)
val decompose_match_w_shared_vars = gen_match_w_shared_vars true




end
