
signature DECOMP_PATTERN =
sig
  val decompose_match_w_shared_vars: theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
  val match_w_shared_vars: theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
end;

structure DecompPattern: DECOMP_PATTERN =
struct


exception NotBetaNormal

fun string_of_term thy env binders t =
  Syntax.string_of_term_global thy
    (Envir.norm_term env (subst_bounds (map Free binders, t)));

val trace_match_fail = Unsynchronized.ref false;


fun ocheck_fail_matching thy (F,t,binders,env) =
  if !trace_match_fail
  then let val f = Term.string_of_vname F
           val u = string_of_term thy env binders t
       in tracing("Variable " ^ f ^ " occurs in term\n" ^ u ^
                  "\nCannot match!\n")
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

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts);


fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (nth jn) t,is);




(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;


(*** Matching ***)

fun typ_match thy TU tyenv = Sign.typ_match thy TU tyenv
  handle Type.TYPE_MATCH => raise Pattern.MATCH;



(* Matching of higher-order patterns *)

fun match_bind(itms,binders,ixn,T,is,t) =
  let val js = loose_bnos t
  in
    if null is then
      if null js then Vartab.update_new (ixn, (T, t)) itms
      else raise Pattern.MATCH
    else
      if subset (op =) (js, is) then
        let val t' =
          if downto0(is,length binders - 1) then t
          else mapbnd (idx is) t
        in Vartab.update_new (ixn, (T, mkabs (binders, is, t'))) itms end
      else raise Pattern.MATCH
  end;






fun first_order_match_w_shared_vars thy =
  let
    fun mtch k instsp (pat, obj0) =
      let val obj = obj0
        |> Envir.head_norm (Envir.Envir{maxidx=0, tenv=snd instsp, tyenv=fst instsp})
      in mtch_aux k instsp (pat, obj) end
    and mtch_aux k (instsp as (tyinsts,insts)) = fn
        (Var(ixn,T), t)  =>
          if k > 0 andalso Term.is_open t then raise Pattern.MATCH
          else
           (case Envir.lookup' (insts, (ixn, T)) of
             NONE => (typ_match thy (T, fastype_of t) tyinsts,
                      Vartab.update_new (ixn, (T, t)) insts)
           | SOME u => if Pattern.aeconv (t, u) then instsp else raise Pattern.MATCH)
      | (Free (a,T), Free (b,U)) =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else raise Pattern.MATCH
      | (Const (a,T), Const (b,U))  =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else raise Pattern.MATCH
      | (Bound i, Bound j)  =>  if  i=j  then  instsp  else raise Pattern.MATCH
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch (k + 1) (typ_match thy (T,U) tyinsts, insts) (t,u)
      | (f$t, g$u) => mtch k (mtch k instsp (f,g)) (t, u)
      | (t, Abs(_,U,u))  =>  mtch (k + 1) instsp ((incr t)$(Bound 0), u)
      | _ => raise Pattern.MATCH
  in fn tu => fn env => mtch 0 env tu end;




(* matching were variables with same identity in pat and obj are regarded as shared
  NB: no deep variable bindings, as this would correspond to unification, so we only norm the object *)
fun gen_match_w_shared_vars is_decompose_match thy (po as (pat,obj)) envir =
  let
    fun toenv (iTs,itms) = Envir.Envir {maxidx=0, tenv=itms, tyenv=iTs}

    (* Pre: pat and obj have same type *)
    fun mtch binders (pat, obj0) (env as (iTs,itms)) =
      let 
        (* NB: we normalize in order to regard common variables in object and pattern as shared.
           Only object is normalized to avoid deep matching, which would correspond to unification. *)
        val obj = obj0 |> Envir.head_norm (toenv env)
      in
        case pat of
          Abs(ns,Ts,ts) =>
            (case obj of
               Abs(nt,Tt,tt) => mtch ((nt,Tt)::binders) (ts,tt) env
            | _ =>
              if is_decompose_match then raise Pattern.MATCH
              else
                let val Tt = Envir.subst_type iTs Ts
                in mtch((ns,Tt)::binders) (ts,(incr obj)$Bound(0)) env end)
        | _ => (case obj of
                  Abs(nt,Tt,tt) =>
                    mtch((nt,Tt)::binders) ((incr pat)$Bound(0),tt) env
               | _ => cases(binders,env,pat,obj))
      end

    and cases(binders,env as (iTs,itms),pat,obj) =
      let
        val (ph,pargs) = strip_comb pat
        val (oh,oargs) = strip_comb obj
        fun rigrig1 (iTs_,itms_) = fold (mtch binders) (pargs~~oargs) (iTs_,itms_)
          handle ListPair.UnequalLengths => raise Pattern.MATCH
        fun rigrig2 ((a,Ta), (b,Tb)) =
          if a <> b then raise Pattern.MATCH
          else rigrig1 (typ_match thy (Ta,Tb) iTs, itms)
      in
        case ph of
          Var(ixn,T) =>
            let
              fun varmatch () = 
                let
                  val _ =
                    if occurs(ixn,obj,toenv env) then
                      (ocheck_fail_matching thy (ixn,obj,binders,toenv env);
                      raise Pattern.MATCH)
                    else ()
                in 
                  case (SOME (ints_of pargs)
                    handle Pattern.Pattern => NONE)
                  of
                    SOME is => (case Envir.lookup' (itms, (ixn, T)) of
                        NONE => (iTs,match_bind(itms,binders,ixn,T,is,obj))
                      | SOME u =>
                          if Pattern.aeconv (obj, red u is []) then env
                          else raise Pattern.MATCH)
                  | NONE => (case pat of
                        (* pat is non-pattern, so we degrade to local first-order matching *)
                        pat1 $ pat2 => (case obj of
                          obj1 $ obj2 =>
                            let val typ_of = curry fastype_of1 (map snd binders)
                            in
                              (iTs, itms)
                              |>> typ_match thy (typ_of pat1, typ_of obj1)
                              |> fold (mtch binders) ([pat1, pat2] ~~ [obj1, obj2])
                            end
                        | _ => raise Pattern.MATCH)
                      | _ => error "gen_match_w_shared_vars: internal error: expected pattern application")
                 end
            in
              case oh of
                Var(ixn2,_) =>
                  if ixn = ixn2 then rigrig1 env
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

    val pT = fastype_of pat
    and oT = fastype_of obj
    val envir' = apfst (typ_match thy (pT, oT)) envir;
  in
    mtch [] po envir'
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
