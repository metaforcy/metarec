
signature MetaRec_sig =
sig
  type judgements_type
  val get_judgements : Context.generic -> judgements_type

  val normalize : Proof.context -> thm -> thm
  val metarec : Proof.context -> Graph.key -> term * term list -> thm * term list
  val metarec_tac : Proof.context -> int -> tactic
  val decompose_judgement : Context.generic -> term ->
    (string * (term * term list * term list)) option
  val order_by_priority : ('a * int) list -> 'a list
  val eq_for_net : (thm * 'a) * (thm * 'b) -> bool
  val add_assm : bool -> thm -> Proof.context -> Proof.context
end

functor SimpleSolver(MetaRecData : MetaRec_sig) = struct


structure Data = Generic_Data
(
  type T = (thm * int) Item_Net.T
                                        (* indexing *)
  val empty = Item_Net.init MetaRecData.eq_for_net (single o Thm.concl_of o fst)
  val extend = I;
  fun merge (net1, net2) = Item_Net.merge (net1, net2);
);

(* high priority rules get priority before low priority rules *)
fun add_rule prio th = Data.map (Item_Net.update (th, prio))
fun del_rule th = Data.map (Item_Net.remove (th, 0))

val SSol_add = Thm.declaration_attribute (add_rule 0)
val SSol_del = Thm.declaration_attribute del_rule

val setup = Attrib.setup (Binding.name "SSol") (Attrib.add_del SSol_add SSol_del)
  "Declaration of Rules for the Simple Solver"

val rules_of = Data.get;

fun print_tcset ctxt =
  let val net = rules_of (Context.Proof ctxt) in
    Pretty.writeln (Pretty.big_list "solver rules:"
      (map (Display.pretty_thm ctxt o fst) (Item_Net.content net)))
  end;


(* tactics *)
fun net_res_tac ctxt =
  SUBGOAL (fn (goal, i) =>
    let
      val concl = Logic.strip_assums_concl goal
        (* Net-Unification doesn't mind loose bounds *)
      val rls = Item_Net.retrieve (rules_of (Context.Proof ctxt)) concl
        |> MetaRecData.order_by_priority
    in resolve_tac rls i end);



   (* besser rigidness-check bei moeglw passendem assume_tac? *)
fun step_tac ctxt =
  assume_tac ORELSE' MetaRecData.metarec_tac ctxt
  ORELSE' net_res_tac ctxt


fun simple_solver_det_tac ctxt i =
   (* zum debuggen besser nur REPEAT, wobei REPEAT keinen Fortschritt fordert *)
  SELECT_GOAL (REPEAT_DETERM_FIRST (step_tac ctxt)) i

fun simple_solver_tac ctxt i =
   (* zum debuggen besser nur REPEAT, wobei REPEAT keinen Fortschritt fordert *)
  SELECT_GOAL (REPEAT_FIRST (step_tac ctxt)) i


end
