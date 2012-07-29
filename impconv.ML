(* forward reasoning a la conversion using ==> instead of == 
   collecting all results *)
(* should be generalized to generalized rewriting on
     transitive relations (reflexivity is also beneficial for every, try, repeat) *)

structure ImpConv = struct

infix 1 then_iconv;
infix 0 else_iconv;
infix 0 and_iconv;
infix 0 or_iconv;

(* with each thm of the form
     redex_prop ==> reduct_prop
   failure indicated as empty result list or THM, CTERM, TERM, TYPE exception *)
type iconv = cterm -> thm list

val no_iconv = K []
fun all_iconv ct = [Thm.trivial ct];

val lhs_of_impl = Thm.cprop_of #> Thm.dest_implies #> fst
val rhs_of_impl = Thm.cprop_of #> Thm.dest_implies #> snd

fun prop_eq (th1, th2) = (Thm.prop_of th1) aconv (Thm.prop_of th2)
fun is_triv th = (op aconv) (Logic.dest_implies (Thm.prop_of th))

fun (cv1 then_iconv cv2) ct =
  let
    val imp1s = cv1 ct;
  in
    imp1s |> maps (fn imp1 =>
      let val imp2s = cv2 (rhs_of_impl imp1);
      in
        if is_triv imp1 then
          imp2s
        else if forall is_triv imp2s andalso not (null imp2s) then
          [imp1]
        else (* TODO(opt): analogon zu Thm.transitive *)
          imp2s |> map (fn imp2 => imp1 COMP imp2)  
      end)
  end

fun handle_exceptions failcont f x =
  f x
  handle
      THM _ => failcont ()
    | CTERM _ => failcont ()
    | TERM _ => failcont ()
    | TYPE _ => failcont ()

fun exception_to_emptyres f x = handle_exceptions (K []) f x

fun (cv1 else_iconv cv2) ct =
  case exception_to_emptyres cv1 ct of
    [] => cv2 ct
  | res => res


 (* applies all cvs; every one has to succeed *)
fun conj_branch_iconv cvs ct =
  let exception NORES
  in
    cvs |> maps (fn cv =>
      case cv ct of
        [] => raise NORES
      | res => res)
    handle NORES => []
  end
fun (cv1 and_iconv cv2) = conj_branch_iconv [cv1, cv2]

 (* applies all applicable cvs, collecting results *)
fun disj_branch_iconv cvs ct = maps (fn cv => exception_to_emptyres cv ct) cvs 
fun (cv1 or_iconv cv2) = disj_branch_iconv [cv1, cv2]

fun first_iconv cvs = fold_rev (curry op else_iconv) cvs no_iconv;
fun every_iconv cvs = fold_rev (curry op then_iconv) cvs all_iconv;

fun try_iconv cv = cv else_iconv all_iconv;
fun repeat_iconv cv ct = try_iconv (cv then_iconv repeat_iconv cv) ct;

fun cache_iconv (cv: iconv) = Thm.cterm_cache cv;






(** Pure iconversions **)

(* lambda terms *)
(* subterm structure *)
(* machen keinen Sinn fuer Implikation *)



(* primitive logic *)
(* TODO *)
(* fun forall_iconv cv ctxt ct =
  (case Thm.term_of ct of
    Const ("all", _) $ Abs _ => arg_iconv (abs_iconv cv ctxt) ct
  | _ => raise CTERM ("forall_iconv", [ct])); *)

(* macht keinen Sinn weil kontravariante Pos *)
(* fun implies_iconv cv1 cv2 ct =
  (case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => combination_iconv (arg_iconv cv1) cv2 ct
  | _ => raise CTERM ("implies_iconv", [ct])); *)

(* TODO *)
(* fun implies_concl_iconv cv ct =
  (case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => arg_iconv cv ct
  | _ => raise CTERM ("implies_concl_iconv", [ct])); *)


(* single rewrite step, cf. REWR_CONV in HOL *)

fun rewr_iconv rule ct =
  let
    val rule1 = Thm.incr_indexes (#maxidx (Thm.rep_cterm ct) + 1) rule;
    val lhs = lhs_of_impl rule1;
    val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1;
  in
    [Drule.instantiate_normalize (Thm.match (lhs, ct)) rule2]
      handle Pattern.MATCH => raise CTERM ("rewr_iconv", [lhs, ct])
  end;

fun first_rewrs_iconv rules = first_iconv (map rewr_iconv rules)
fun collect_rewrs_iconv rules = disj_branch_iconv (map rewr_iconv rules)


(* conversions on HHF rules *)

(*rewrite B in !!x1 ... xn. B*)
(* TODO *)
(* fun params_iconv n cv ctxt ct =
  if n <> 0 andalso Logic.is_all (Thm.term_of ct)
  then arg_iconv (abs_iconv (params_iconv (n - 1) cv o #2) ctxt) ct
  else cv ctxt ct; *)

(*rewrite the A's in A1 ==> ... ==> An ==> B*)
(* macht keinen Sinn weil contravariant *)

(*rewrite B in A1 ==> ... ==> An ==> B*)
(* TODO *)
(* fun concl_iconv 0 cv ct = cv ct
  | concl_iconv n cv ct =
      (case try Thm.dest_implies ct of
        NONE => cv ct
      | SOME (A, B) => Drule.imp_cong_rule (all_iconv A) (concl_iconv (n - 1) cv B)); *)

(* conversions as inference rules *)

(*forward conversion, cf. FCONV_RULE in LCF*)
fun ficonv_rule cv th =
  cv (Thm.cprop_of th) |> map (fn imp =>
    if is_triv imp then
      th
    else (* TODO(opt) *)
      imp OF [th])

(*goal conversion*)
(* macht keine Sinn weil kontravariante Position *)




 (* applies some cvs. fail if none applies ???? *)
(* fun collect_disj_iconv [] ct = []
  | collect_disj_iconv (cv :: cvs) ct =
      (exception_to_emptyres cv ct) @ collect_disj_iconv cvs ct *)

(* applies conversion to fact pool, pruning convertable facts,
     keeping nonconvertable facts *)
fun pool_apply cv facts =
  let
    val forw_iconv = ficonv_rule (exception_to_emptyres cv)
  in 
    []
    |> fold (fn fact =>
           fold (insert prop_eq)
             (case forw_iconv fact of 
               [] => [fact]
             | facts2 => facts2))
         facts
  end
fun saturate_pool cv facts =
  let val facts' = pool_apply cv facts
  in
    if length facts' = length facts then
      facts
    else
      saturate_pool cv facts'
  end
fun saturate_pool_from cv ct =
  cv ct |> saturate_pool cv


end;

