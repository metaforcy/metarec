theory UniverseLevelInference
imports "../ZFMetaRec"
begin



ML {*

  val B_x = @{cpat "?B(x::i) :: i"} |> Thm.term_of
  val prod = @{cpat "PROD x:?C. ?D(x)"} |> Thm.term_of
  val env' = 
    StructUnify.unify @{theory} (B_x, prod) (Envir.empty 1)
  val B_x' = Envir.norm_term env' B_x |> cterm_of @{theory}
  val prod' = Envir.norm_term env' prod |> cterm_of @{theory}
*}



(* this is an improper axiomatization of a universe hierarchy:
   we just state closure under the things we need instead of closure under
   the primitive set theoretic constructions (union, replacement etc.) *)
axiomatization
  guniv :: "i => i" ("guniv _" [100] 100)
where
  nat_in_guniv: "i : nat ==> nat : guniv i"  and
  trans_guniv: "i : nat ==> x : A ==> A : guniv i ==> x : guniv i" and
  list_in_guniv: "[|  i : nat  ;  A : guniv i  |] ==> List_ZF.list(A) : guniv i" and
  prod_in_guniv:
    "[|  i : nat  ;  A : guniv i  ;  (!! x. x : A ==> B(x) : guniv i)  |]
     ==> (PROD x:A. B(x)) : guniv i" and
  guniv_in_guniv: "[|  i : nat  ;  j : nat  ;  i < j |] ==> guniv i : guniv j"



lemma guniv_cumul: "[|  i : nat  ;  j : nat  ;  i le j ;  x : guniv i |] ==> x : guniv j"
  apply (cases "i = j") apply simp
  apply (rule trans_guniv[of j x "guniv i"], assumption+)
  apply (rule guniv_in_guniv, assumption+)
  apply (rule Ord_linear_lt[of i j], simp+)
  by (simp add: le_iff)

lemma natelem_in_guniv: "i : nat ==> x : nat ==> x : guniv i"
  apply (rule trans_guniv) apply assumption+ by (rule nat_in_guniv)

(* Pseudo terms that will be elaborated.
   Note that we don't introduce a seperate type to allow the
   reuse of free variables in the pseudoterm when elaborating. *)

definition
  ptuniv :: "i" ("univ") where
  "ptuniv == 0"
definition (* $ is taken by ZFMetaRecSyntax, @ is taken by List_ZF *)
  ptapp :: "i => i => i" (infixl "#" 100) where
  "ptapp(f,x) == 0"
definition
  ptlambda :: "(i => i) => i" where
  "ptlambda(b) == 0"
definition
  ptprod :: "i => (i => i) => i" where
  "ptprod(A,F) == 0"

syntax
  "_fun" :: "[pttrn, i] => i"  ("(2fun _./ _)" 10)  (* lam already taken for proper ZF abstractions *)
  "_PI"     :: "[pttrn, i, i] => i"  ("(3PI _:_./ _)" 10)

translations
  "fun x. f"  == "CONST ptlambda(%x. f)"
  "PI x:A. B" == "CONST ptprod(A, %x. B)"

(* we use ~> because -> is already taken for the proper set-theoretic simple function space *)
abbreviation
  ptsimplefun :: "i => i => i" (infixr "~>" 60) where
  "A ~> B == ptprod(A, %_. B)"

term "PI x:A~>univ. PI z:A. x # ((fun y. y) # z)"

term "x : y"








(* elaboration rules *)


definition
  elabjud :: "i => i => i => o" ("_ elabto _ : _") where
  [MRjud 1 2]: "elabjud(t, t', A) == t' : A"

definition
  constraint_typing :: "i => i => o" ("_ <: _") where
  [MRjud 2 0]: "constraint_typing (t, A) == t : A"
definition
  syn_constraint_typing :: "i => i => o" ("_ :> _") where
  [MRjud 1 1]: "syn_constraint_typing (t, A) == t : A"

lemma [MRjud 2 0]: "i < j == i < j" by simp
lemma [MRjud 2 0]: "i le j == i le j" by simp
  
(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
(* low prio rule for type inference of free variable x *)
(* FIXME: statt immer neue Unifvar zu generieren bei bereits vorhandenem constraint (x <: A')
   sofort  Unifikation A == A'  durchfuehren. Entspricht also on-the-fly constraint propagation mit der
   Typ-Constraint-Sharing-Regel von unten. Hui! *)
lemma [MR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;  foconstraint (i <: nat)  ;  constraint (x <: A) |] ==>
  x elabto x : A"
 unfolding elabjud_def constraint_const_def constraint_typing_def .

lemma [MR_unchecked]: "[|
    t1 elabto t1' : T  ;
    freshunifvar A  ;  freshunifvar B  ;
    unify T (PROD x:A. B(x))  ;
    t2 elabto t2' : A'  ;
    unify A A'  |] ==>
 (t1 # t2) elabto (t1' ` t2') : B(t2')"
  unfolding elabjud_def unify_const_def
  by (rule apply_type)

(* TODO: unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [MR_unchecked]: "[|
    freshunifvar A  ;  freshunifvar i  ;
    constraint (A <: guniv i)  ;   foconstraint (i <: nat) ;
    !! x.  x elabto x : A  ==>  t(x) elabto t'(x) : B(x)  |] ==>
  (fun x. t(x)) elabto (lam x:A. t'(x)) : (PROD x:A. B(x))"
  unfolding elabjud_def fresh_unifvar_const_def
  by (rule lam_type)

lemma [MR]: "[|
    A elabto A' : guniv i  ;
    !! x.  x elabto x : A'  ==>  t(x) elabto t'(x) : B(x)  |] ==>
  (lam x:A. t(x)) elabto (lam x:A'. t'(x)) : (PROD x:A'. B(x))"
  unfolding elabjud_def fresh_unifvar_const_def
  by (rule lam_type)



lemma [MR]: "[|
    A elabto A' : guniv i  ;  foconstraint (i <: nat)  ;
    !! x.  x elabto x : A'  ==>  B(x) elabto B'(x) : guniv j  ;  foconstraint (j <: nat)  ;
    freshunifvar k  ;  foconstraint (k <: nat)  ;  foconstraint (i le k)  ;
    foconstraint (j le k)  |] ==>
  (PI x:A. B(x)) elabto (PROD x:A'. B'(x)) : guniv k"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def fresh_unifvar_const_def
  apply (rule prod_in_guniv)
  apply assumption
  apply (rule guniv_cumul[of i k], assumption+)
  by (rule guniv_cumul[of j k], assumption+)

(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [MR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar j  ;
    foconstraint (i <: nat)  ;  foconstraint (j <: nat)  ;   foconstraint (i < j)  |] ==>
  univ elabto (guniv i) : (guniv j)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (rule guniv_in_guniv)


lemma [MR_unchecked]: "[|
    freshunifvar j  ;
    foconstraint (i <: nat)  ;  foconstraint (j <: nat)  ;   foconstraint (i < j)  |] ==>
  (guniv i) elabto (guniv i) : (guniv j)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (rule guniv_in_guniv)

lemma [MR]: "[|
    freshunifvar i  ;  foconstraint (i <: nat)  |] ==>
  nat elabto nat : (guniv i)"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (rule nat_in_guniv)




(* constraint simplification *)

lemma [impl_frule]: "x elabto x : A ==> x :> A"
  by (simp add: syn_constraint_typing_def elabjud_def)

lemma [MR]: "
    constraint (t <: A) ==>
  t <: A"
  by (simp add: constraint_const_def)

lemma [MR]: "
    try (t :> A) ==>
  t <: A"
  by (simp add: syn_constraint_typing_def constraint_typing_def try_const_def)

lemma [MR]: "[|
    foconstraint (i <: nat)  ;
    A <: guniv i  ;  !! x. x :> A ==> B(x) <: guniv i  |] ==>
  (PROD x:A. B(x)) <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def syn_constraint_typing_def
  by (rule prod_in_guniv)

(* NB: i,j are always universe level variables, so the constraint (i < j) cannot really
   be solved right now and can at best be refuted if i = j *)
(* TODO(opt): syntactic constraint subsumption would be nice to immediately get rid
    of duplicate i <: nat constraints  *)
lemma [MR]: "[|
    foconstraint (i <: nat) ;  foconstraint (j <: nat)  ;  foconstraint (i < j) |] ==>
  guniv i <: guniv j"
  unfolding foconstraint_const_def constraint_typing_def
  by (rule guniv_in_guniv)

(* NB: relies on removal of non-relevant fixes and assms in front of the resulting constraints.
      Cannot be realized as an constraint simplification rule that is executed
      as part of the propagation machinery, because the fixes, assms context has to
      be gone then already. *)
(* NB: only realizes contextual discharge of typing constraints,
     because x :> A is only issued for fixes x.
   Discharging dependent B(x) to (PROD x:A. B(x)) does not work easily
   because B(x) constitutes a non-pattern.
   So dependent product typing constraints t <: (PROD x:A. B(x))
   can only be created by the free variable typing rule *)
lemma typ_constraint_ctxt_discharge_MR[MR]: "[|
     freshunifvar f  ;
     !! x. try (unify (appt(x)) (f ` x))  ; try (x :> A)  ;
     f <: A -> B  |] ==>
   appt(x) <: B"
  unfolding try_const_def unify_const_def elabjud_def
    constraint_typing_def syn_constraint_typing_def
  by simp



lemma constraint_typ_apply: "
  [|  x elabto x' : A  ;  g <: (PROD x:A. B(x))  |] ==> g ` x' <: B(x')"
  unfolding constraint_typing_def elabjud_def
  by (rule apply_type)

(* could be useful for more general type constraint context discharge
   into dependent products *)
ML {*
  (* returns SOME ((C', proof of normalized C0 with hyp C'), new context) on success *)
  fun typ_constraint_ctxt_discharger rel_fixes C0 ctxt =
    let
      val C = MetaRec.norm_with_env_in_run_state ctxt C0
      val gctxt = Context.Proof ctxt


      val rel_assms = MetaRec.get_assms gctxt |> map_filter (fn assm =>
        case MetaRec.decompose_judgement gctxt assm of
          SOME ("elabjud_jud", (x, [], [x', A ])) =>
            if member (op =) rel_fixes x andalso x = x' then
              SOME ((x, A), assm)
            else
              NONE
        | _ => NONE)
     
      fun zfapply_typ_constraint_prf h' larg B ctxt3 =
        case find_first (fn ((x, _), _) => larg = x) rel_assms of
          SOME ((x, A), assm) =>
            let
              val C2 = @{term constraint_typing} $ h' $ (@{term Pi} $ A $ Term.lambda larg B)
              (* prf3 proves C2 under hyp C3 *)
              val ((C3, prf3), ctxt4) =
                case typ_constraint_ctxt_discharger rel_fixes C2 ctxt3 of
                  SOME subres => subres
                | NONE => ((C2, MetaRec.assumption_prf C2), ctxt3)
              val (prf_res, ctxt5) = MetaRec.mps_match_on_freshthm_prf @{thm constraint_typ_apply}
                [MetaRec.assumption_prf assm, prf3] ctxt4
            in
              SOME ((C3, prf_res), ctxt5)
            end
        | NONE => NONE

    in
      case MetaRec.decompose_judgement gctxt C of
        SOME ("constraint_typing_jud", (t, [B], _)) =>
          let val (h, args) = Term.strip_comb t
          in
            case try Term.dest_Var h of
              NONE =>
                (case h of
                  Const(@{const_name apply}, _) $ h' $ larg =>
                    zfapply_typ_constraint_prf h' larg B ctxt
                | _ => NONE)
            | SOME (ixn, hT) =>
                (case try split_last args of
                  NONE => NONE
                | SOME (args', larg) =>
                    let
                      val v'T = map fastype_of args' ---> Term.body_type hT
                      val (v', ctxt2) = MetaRec.genvar_on_run_state (fst ixn) v'T ctxt
                      val h' = list_comb (v', args')
                      val v'app = @{term "apply"} $ h' $ larg |> fold_rev Term.lambda args
                      val ctxt3 = ctxt2 |> Context.proof_map (MetaRec.map_env_in_run_state
                        (curry Envir.update ((ixn, hT), v'app)))
                    in zfapply_typ_constraint_prf h' larg B ctxt3 end)
           end
      | _ => NONE
    end
*}









ML {*
  fun elab ctxt t =
    exception_trace (fn () =>
      MetaRec.metarec_fully_discharged ctxt "UniverseLevelInference.elabjud_jud" (t, []) |> fst)
*}
(* NB: exception traces seem better with deactivated debugging *)

ML {*  elab @{context} @{term "x :: i"}  *}

ML {*  elab @{context} @{term "(fun x. x)"}  *}

ML {*  elab @{context} @{term "f # x"}  *}

(* FIXME: bei Unifikationsproblem  ?B(t) == (PROD y:?C. ?D(y))  (konkret t:=x unten) muessen wir loesen mit
     ?B := (% x. PROD y:?C'(x). ?D'(x, y)),   ?C := ?C'(t)    ?D := ?D'(t)
   loesen. weiterhin brauchen wir allgemeiner strukturelle pattern unifikation (d.h. paralleler struktureller
   Abstieg auch in non-patterns moeglich), die das beachtet und auch die bestehende patternification durchfuehrt. *)
ML {*  elab @{context} @{term "f # x # y"}  *}

ML {*
  val fixes = Variable.dest_fixes @{context} |> map snd
  val constraints = Variable.constraints_of @{context} |> fst |> Vartab.dest |> filter (fn ((n, ix), _) => ix = ~1)
            |> map (fn ((n, _), T) => Free(n,T) |> Syntax.string_of_term @{context})
*}

ML {*  elab @{context} @{term "(fun f. fun x. (f ` x))"}  *}


ML {*  elab @{context} @{term "(fun f. fun x. f # x)"} *}


ML {*  elab @{context} @{term "(fun f. fun g. fun x. f # (g # x))"}  *}


(* TODO: universe level annotations can lead to unsatisfiable first-order constraints
     for universe levels that are used in subterms (we may not unlift them in that case).
   This should be resolvable by careful local type inference? *)
ML {*  elab @{context} @{term "(lam i:nat. lam x:guniv i. fun f. f # x)"} *}

ML {*  elab @{context} @{term "(lam i:nat. lam x:guniv i. fun f. f ` x)"} *}

(* FIXME: we need constraint propagation to combine the constraints to find the typing error *)
ML {*  elab @{context} @{term "x # x"} *}

(* fails with occurs check *)
(* ML {*  elab @{context} @{term "(fun x. x # x)"} *} *)











definition
 universe_inconsistency where
 [MRjud 1 0]: "universe_inconsistency(x) == False"


(* constraint loeser *)
(* ueber constraint handling rules die die Ableitungsschritte tracen? wir sollten uns auch
   merken welche Regelanwendung ein constraint erzeugt hat! *)
(* TODO: forward rules werden nicht fair angewandt, aber haben ja auch keine Simplification-Regeln
    also egal bzgl. Terminierung? *)
(* vllt CHRs am einfachsten zu implementieren wenn wir Propagation-Regel als Simplification-Regeln
   kodieren. !!! Dann kann man das auch als eine Art Multi-Head-Narrowing ansehen !!!
   Nervig wird dann hier vor allem die staendige Permutation der Metakonjunktionen im Goal so das
   eine Regel passt. Mit Konversions vermutlich zu nervig, stattdessen mit neuem Subgoal arbeiten
   das man mit viel conjI, conjE und assumption loest *)
(* bzgl. Constraint-Minimierung: klassisch bei CHRs soll alle Minimierung ueber Simplification passieren,
   aber das reicht uns nicht weil ja die Propagierungsresultate die nicht vereinfacht wurden noch
   rumschwirren. Kann man vllt einfach sagen das man die urspruenglichen Constraints nimmt, ohne die
   die vereinfacht wurden und zusaetzlich dazu die Vereinfachungsresultate? Aber so kriegt man ja
   die Redundanzen in den urspruenglichen Constraints nicht eliminiert!!

   Ansonsten: Gerichteten Hyper-Graph (Knoten sind Constraints, Kanten sind von einer
   Menge von Constraints zu einem dadurch implizierten Menge von Constraints) aufbauen der repraesentiert
   welche der urspruenglichen Constraints und vereinfachten Constraints
   einander implizieren (ggf nach Instantiierung?).
   Zur Minimierung dann eine kleinstmoegliche Menge von Constraints zuruecklassen (die nicht vereinfacht wurden)
   von denen alle anderen Constraints aus erreichbar sind im Hyper-Graph.
   Aus starken Zusammenhangskomponenten die nicht anders erreichbar sind nimmt man dann also
   nur ein Constraint. *)
(* Gesamt-Algorithmus ist dann wie folgt:
     * Constraint-Propagierung, d.h. alle relevanten Konsequenzen aus Constraints generieren
       und die Generierungsrelation als Hypergraph verwalten
     * dabei Vereinfachung (ggf. Eliminierung oder Gesamt-Fehlschlag) mancher Constraints 
       (wird als bidirektionale Kante im Hypergraph verwaltet, wobei die Constraints die vereinfacht
        wurden nicht genutzt werden duerfen; die Vereinfachung kann Unifikation
       als Seiteneffekt anstossen; ggf. Backtracking ueber solche Regelanwendungen weil sie
       globale Auswirkungen haben, oder nehmen wir Konfluenz an?)
     * Wahl einer minimalen Menge von Constraints die die Gesamtmenge erzeugen (modulo den Vereinfachungen) *)
(* wie bei echten CHRs matchen wir die Regeln bloss und nutzen dann ggf. explizite Unifikation in den Premissen *)
lemma [constraint_propag_rule]: "i < j &&& j < k ==> i < k"
  apply (erule conjunctionE) by (rule Ordinal.lt_trans)

lemma [constraint_propag_rule]: "i < j &&& j le k ==> i < k"
  apply (erule conjunctionE) by (rule Ordinal.lt_trans2)

lemma [constraint_propag_rule]: "i le j &&& j < k ==> i < k"
  apply (erule conjunctionE) by (rule Ordinal.lt_trans1)

lemma [constraint_propag_rule]: "i le j &&& j le k ==> i le k"
  apply (erule conjunctionE) by (rule Ordinal.le_trans)

lemma [constraint_simp_rule]: "universe_inconsistency(0) ==> (i < j &&& j < i)"
  apply (rule Pure.conjunctionI)
  by (simp add: universe_inconsistency_def)+


  (* NB: no try around unify. corresponds to CHR  (i <= j , j <= i) == (i = j) *)
lemma [constraint_simp_rule]: "[| unify i j  ;  constraint (i <: nat)  ;  constraint (j <: nat)  |] ==>
  (i le j &&& j le i)"
  apply (rule Pure.conjunctionI)

  by (simp add: unify_const_def constraint_const_def constraint_typing_def)+
lemma [constraint_simp_rule]: "constraint (i <: nat) ==> i le i"
  by (simp add: constraint_const_def constraint_typing_def)

(* TODO: entsprechendes um Sharing von Dictionaries gleicher Typklassenapplikationen zu erzwingen *)
lemma [constraint_propag_rule]: "[|  unify A A2  ;  t <: A &&& t <: A2  |] ==> True"
  by simp



(* examples *)

(* note that this is still slightly improper since we reuse Larry's list operator instead
   of a proper type constructor formulation
     list : (PI i:nat. guniv i -> guniv i)  *)

definition
  "list' == (lam i:nat. lam A:guniv i. List_ZF.list(A))"

lemma list'_ty: "list' : (PROD i:nat. guniv i -> guniv i)"
  unfolding list'_def
  apply typecheck
  by (rule list_in_guniv)

lemma [MR]: "[|
    foconstraint (i <: nat)  ;    A <: guniv i  |] ==>
  (list' ` i ` A) <: guniv i"
  unfolding foconstraint_const_def constraint_typing_def  list'_def
  apply simp
  by (rule list_in_guniv)


definition
  "nil' == (lam i:nat. lam A:guniv i. List_ZF.Nil)"
definition
  "cons' == (lam i:nat. lam A:guniv i. lam x:A. lam xs:(list'`i`A). List_ZF.Cons(x,xs))"
definition
  "map' == (lam i : nat. lam A : guniv i. lam B : guniv i. lam f : (A -> B). lam xs : (list' ` i ` A).
     List_ZF.map((% x. f ` x), xs) )"

lemma nil'_ty : "nil' : (PROD i:nat. PROD A:guniv i. list' ` i ` A)"
  unfolding nil'_def list'_def
  apply typecheck
  by simp 

lemma cons'_ty : "cons' : (PROD i:nat. PROD A:guniv i. A -> list' ` i ` A -> list' ` i ` A)"
  unfolding cons'_def list'_def
  apply typecheck
  by simp

definition
  list :: "i" where
  "list == 0"
definition
  map :: "i" where
  "map == 0"
(* also we are reusing List_ZF.{Nil,Cons} and their [..]-Syntax for pseudo-term lists *)



lemma [MR]: "[|
    freshunifvar i  ;  foconstraint (i <: nat)  |] ==>
  list elabto (list' ` i) : guniv i -> guniv i"
  unfolding elabjud_def foconstraint_const_def constraint_typing_def
  by (typecheck add: list'_ty)

lemma [MR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  |] ==>
  Nil elabto (nil' ` i ` A) : list' ` i ` A"
  unfolding elabjud_def foconstraint_const_def constraint_const_def constraint_typing_def
  by (typecheck add: nil'_ty)

(* TODO: actually we could use a checking judgements  i <= nat, A <= guniv i
   here instead of emitting a constraint *)
lemma [MR_unchecked]: "[|
    t elabto t' : A  ;
    ts elabto ts' : list' ` i ` A2  ;
    unify A A2  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)   |] ==>
  (Cons(t,ts)) elabto (cons' ` i ` A ` t' ` ts') : (list' ` i ` A)"
  unfolding elabjud_def constraint_const_def foconstraint_const_def
    unify_const_def constraint_typing_def
  by (typecheck add: cons'_ty)



(* unchecked because freshunifvar assums lead to moding-inconsistent facts in wellformedness checking *)
lemma [MR_unchecked]: "[|
    freshunifvar i  ;  freshunifvar A  ;  freshunifvar B  ;
    foconstraint (i <: nat)  ;  constraint (A <: guniv i)  ;  constraint (B <: guniv i)  |] ==>
  map elabto (map' ` i ` A ` B) : (A -> B) -> list' ` i ` A -> list' ` i ` B"
  unfolding elabjud_def foconstraint_const_def constraint_const_def constraint_typing_def
  by (simp add: map'_def list'_def)



ML {*  elab @{context} @{term "(map # f # [nat])"}  *}









(* Dinge die man beweisen sollte in einem Papier
     * Bezug zur Typisierung mit Typsystem mit nicht-triv Universenlevelausdruecken und insbesondere
         =========================
           univ i : univ (i + 1)
     * trivial: soundness bzgl Typsystem mit Universenlevel-Annotationen und vorgegebenen
       Universenlevel-Constraints
     * completeness dazu auch ?

     * zyklische Abhaengigkeiten zwischen freien Variablen und ihren den Typen, zB
         x : A(y) ==> y : B(x) ==> t(x,y) : C(x,y)
       ist bei uns moeglich weil Typisierungsregeln first-class sind und wir also nicht
       zwingend Typisierungsconstraints zu dependent products dischargen muessen!
       Dependent type theories koennen das nicht weil weder (% x y. t(x,y)) noch (% y x. t(x,y))
       typisierbar sind also muss man dann zu grober Typisierung von x,y und
       explizitem Beweisen x in A(y), y in B(x) uebergehen , d.h.
         (% x y : UnivElem. % p : proof(x in A(y)). % q : proof (y in B(x)). t(x,y))

       Grosse Auswirkungen??
         * Ist das innovativ bei Sharing-Problematik bei Records? eher nicht weil sobald man Variablen
           fuer Fields statt Projektionsanwendung shared ist man bei dem Ansatz von Spitters.
           Die dependent record fields im very dependent types paper sind auch wohlgeordnet.
         * man will Typkonstruktionen ja weiterhin schrittweise definieren und nicht fuer
           eine Menge von Variablen mit mutually-recursive Typisierung. Ausser man fuehrt irgendwann
           Vektorvariablen ein.

       Ulf Norell nennt das "insane pi-types" https://github.com/UlfNorell/insane
       circular signatures https://github.com/gelisam/circular-sig sollten auch einfach
         moeglich sein, weil das auf locales mit entsprechenden Annahmen fuehrt (fuer
         die es ja keine Einschraenkung gibt)

    * (fuer spaeter): interessante spezialisierte Typisierungsregeln fuer definierte Typkonstruktoren
        monotone A (<=) := { f : A -> A | ALL x1 x2 : A. x1 <= x2 --> f x1 <= f x2 }
      mit Typisierungsregel
            [|  !! x1 x2.  x1 <= x2  ==>  t x1 <= t x2  |] ==>
          t : monotone A
      oder gleich mit Relators und generalized parametricity?
    * very-dependent types ueber induktive Definitionen und entsprechende Typisierungsregeln.
      Interessant oder kann das Coq auch ueber inductive Types und iota-Reduktion?
*)

