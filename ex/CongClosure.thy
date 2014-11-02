
theory CongClosure
imports "../HOLMetaRec"
begin


definition
  find_occs ("_ <= _ under _") where
  [MRjud 2 1]: "find_occs t1 t2 eqs == PROP (eqs t1 t2)"

lemma find_occsI: "PROP eqs t1 t2 ==> PROP find_occs t1 t2 eqs"
  by (simp add: find_occs_def)


definition
  cc_eq where
  [MRjud 1 0]: "cc_eq t12 == (fst t12 = snd t12)"

abbreviation
  cc_eq_abbr (infixl "=cc=" 50) where
  "(t1 =cc= t2) == cc_eq (t1, t2)"

lemma cc_eq_refl: "t =cc= t"
  by (simp add: cc_eq_def)


definition
  add_eqs where
  [MRjud 1 0]: "add_eqs eqs == PROP eqs"


(* NB: we only need to search for syntactic occurrences in find_occs because derivations of the form
                               b = b'
                          --------------------
     a = b     f b' = c     b <= b' under f
  --------------------------------------------------
       f a = c

 can be realized in the following form instead
   
       a = b   b = b'
     -------------------
          a = b'              f b' = c        b' <= f b' under f
  -------------------------------------------------------------------
             f a = c 
*)

ML {*
  fun mk_cc_eq (t1, t2) =
    let val T = fastype_of t1
    in
      Const(@{const_name cc_eq}, HOLogic.mk_prodT (T, T) --> @{typ bool}) $ HOLogic.mk_prod (t1, t2)
    end
  fun mk_Tp_cc_eq (t1, t2) = HOLogic.mk_Trueprop (mk_cc_eq (t1, t2))
  
  fun find_occs ctxt hole_free t1 t2 =
    let
      fun hole_comb f t_w_hole =
        let
          val res = (t_w_hole $ hole_free) |> Envir.beta_norm |> f |> Term.lambda hole_free
          (* val _ = tracing ("hole_comb: transformed "^Syntax.string_of_term ctxt t_w_hole
            ^" to "^Syntax.string_of_term ctxt res) *)
        in res end

      fun hlp ctxt t2 =
        if t1 aconv t2 then
          [Term.lambda hole_free hole_free]
        else
          case t2 of
            t21 $ t22 =>
              map (hole_comb (fn X => X $ t22)) (hlp ctxt t21)
              @ map (hole_comb (fn X => t21 $ X)) (hlp ctxt t22)
          | Abs(x, T, t22) =>
              let
                val ([x'], ctxt2) = Variable.variant_fixes [x] ctxt
                val fix = Free(x', T)
              in
                hlp ctxt2 (subst_bound (fix, t22)) |> map (hole_comb (fn X => Term.lambda fix X))
              end
          | _ => []
    in
      hlp ctxt t2
    end

  fun find_occs_proc ctxt fail_cont (t1_ct, [t2_ct], _) =
    let
      (* NB: t1_ct, t2_ct beta-normal by invariant *)
      val thy = Proof_Context.theory_of ctxt
      val cert = Thm.cterm_of thy
      val certT = Thm.ctyp_of thy
      val (t1, t2) = pairself Thm.term_of (t1_ct, t2_ct)
      val (t1_T, t2_T) = pairself fastype_of (t1, t2)
      val ([t1_free_n, t2_free_n], ctxt2) =
        ctxt |> fold Variable.declare_term [t1, t2]
        |> Variable.variant_fixes (map StructUnify.term_name [t1, t2])
      val t1_free = Free(t1_free_n, t1_T)
      val t2_free = Free(t2_free_n, t2_T)

      val occs = find_occs ctxt2 t1_free t1 t2
    in
      if null occs then
        (fail_cont ctxt ("find_occs_proc: no occurrences of "^Syntax.string_of_term ctxt t1
          ^" were found in "^Syntax.string_of_term ctxt t2); error ("not reachable"))
      else
        let
          (* val _ = tracing ("found occs: "
            ^commas (map (Syntax.string_of_term ctxt) occs)) *)
          val eq_th = Drule.instantiate' [SOME (certT t2_T)]  [SOME (cert t2)] @{thm cc_eq_refl}
          (* val _ = tracing ("eq_th: "^Display.string_of_thm ctxt eq_th) *)
          val eq_ths = replicate (length occs) eq_th
          val eq_conjs_th = Conjunction.intr_balanced eq_ths
          val eq_conjs_absd = occs |> map (fn occ => mk_Tp_cc_eq (occ $ t1_free, t2_free))
            |> Logic.mk_conjunction_balanced
            |> Envir.beta_norm
            |> fold_rev Term.lambda [t1_free, t2_free]
          (* val _ = tracing ("eq_conjs_absd: "^Syntax.string_of_term ctxt eq_conjs_absd) *)
          val eq_conjs_absd_ct = cert eq_conjs_absd
          val th = @{thm find_occsI}
            |> Drule.instantiate' (map (SOME o certT) [t1_T, t2_T]) (map SOME [eq_conjs_absd_ct, cert t1, cert t2])
            |> Conv.fconv_rule (Thm.beta_conversion true)
            |> Thm.elim_implies eq_conjs_th
        in
          (th, [eq_conjs_absd_ct])
        end
    end

*}

setup {*
  Context.theory_map (MetaRec.add_failable_syn_proc "CongClosure.find_occs_jud" "find_occs_proc" find_occs_proc)
*}

(*
ML {*
  val t1 = @{term "(f :: 'a => 'b) y"}
  val t2 = @{term "% z. (g :: 'd => 'e) (h ((f :: 'a => 'b) y) (z :: 'c))"}
  val occs = find_occs @{context} @{term "hole :: 'a"} t1 t2
    |> map Envir.beta_norm
  val cert = Thm.cterm_of @{theory}
  val occs_th = find_occs_proc @{context} (cert t1, [cert t2], [])
*}
*)

lemma [impl_frule]: "
  PROP add_eqs (PROP eqs1 &&& PROP eqs2)
  ==> PROP add_eqs (PROP eqs1)  &&&  PROP add_eqs (PROP eqs2)"
  by (simp add: add_eqs_def)

lemma [impl_frule]: "
  PROP add_eqs (Trueprop (t1 =cc= t2))
  ==> t1 =cc= t2"
  by (simp add: add_eqs_def)


(* implements the schematic frule    [| a =cc= b &&& b' =cc= c ;  b <= b' under vec{f_n} |] ==>  vec{f_n a =cc= c} *)
lemma trans_mod_cong[impl_frule]: "[|
   t1 =cc= t2  &&&  t2' =cc= t3  ;
   try( t2 <= t2' under eqs )  |]
  ==>  PROP add_eqs (eqs t1 t3)"
  apply (erule conjunctionE)
  by (simp add: find_occs_def cc_eq_def try_const_def add_eqs_def)

lemma symm[impl_frule]: "
   t1 =cc= t2
  ==> t2 =cc= t1"
  by (simp add: cc_eq_def)



lemma refl[MR]: "
  t =cc= t"
  by (simp add: cc_eq_def)

lemma cong1[MR]: "
    t =cc= t' ==>
  f t =cc= f t'"
  by (simp add: cc_eq_def)

lemma cong2[MR]: "[|
    t1 =cc= t1'  ;  t2 =cc= t2'  |] ==>
  f t1 t2 =cc= f t1' t2'"
  by (simp add: cc_eq_def)

lemma cong3[MR]: "[|
    t1 =cc= t1'  ;  t2 =cc= t2'  ;  t3 =cc= t3' |] ==>
  f t1 t2 t3 =cc= f t1' t2' t3'"
  by (simp add: cc_eq_def)

lemma cong4[MR]: "[|
    t1 =cc= t1'  ;  t2 =cc= t2'  ;  t3 =cc= t3'  ;  t4 =cc= t4'|] ==>
  f t1 t2 t3 t4 =cc= f t1' t2' t3' t4'"
  by (simp add: cc_eq_def)




(* example
           x =cc= f y &&& g (g (f y)) =cc= z    f y <= g (g (f y)) under (% X. g (g X))
       ---------------------------------------------------------------------------------- trans-mod-cong
            g (g x) =cc= z
        -------------------------- sym
             z =cc= g (g x)
          -------------------------- cong
              h z =cc= h (g (g x))                   *)
lemma
  assumes assms[MRassm]: "x =cc= f y" "g (g (f y)) =cc= z"
  shows "h z =cc= h (g (g x))"
  (* ML_prf {* MetaRec.print_new_facts (Context.Proof @{context}) *} *)
  by (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})

lemma
  assumes assms[MRassm]: "x =cc= f y" "(% u. g (g (f y) u) u) =cc= z"
  shows "h z =cc= h (% u. g (g x u) u)"
  (* ML_prf {* MetaRec.print_new_facts (Context.Proof @{context}) *} *)
  by (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})


end
