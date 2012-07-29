(* like src-Pure/item_net.ML but with
   non-fixed indexing and with retrieve_match and cons *)

signature ITEM_NET2 =
sig
  type 'a T
  val init: ('a * 'a -> bool) -> 'a T
  val content: 'a T -> 'a list
  val retrieve: 'a T -> term -> 'a list
  val retrieve_match: 'a T -> term -> 'a list
  val member: ('a -> term list) -> 'a T -> 'a -> bool
  val member_match: ('a -> term list) -> 'a T -> 'a -> bool
  val merge: ('a -> term list) -> 'a T * 'a T -> 'a T
  val remove: 'a -> ('a -> term list) -> 'a T -> 'a T
  val update: 'a -> ('a -> term list) -> 'a T -> 'a T
  val cons: 'a -> ('a -> term list) -> 'a T -> 'a T
end;

structure Item_Net2: ITEM_NET2 =
struct

(* datatype *)

datatype 'a T =
  Items of {
    eq: 'a * 'a -> bool,
    content: 'a list,
    next: int,
    net: (int * 'a) Net.net};

fun mk_items eq content next net =
  Items {eq = eq, content = content, next = next, net = net};

fun init eq = mk_items eq [] ~1 Net.empty;

fun content (Items {content, ...}) = content;
fun retrieve (Items {net, ...}) = order_list o Net.unify_term net;
fun retrieve_match (Items {net, ...}) = order_list o Net.match_term net;


(* standard operations *)

fun member index (Items {eq, content, net, ...}) x =
  (case index x of
    [] => Library.member eq content x
  | t :: _ => exists (fn (_, y) => eq (x, y)) (Net.unify_term net t));
fun member_match index (Items {eq, content, net, ...}) x =
  (case index x of
    [] => Library.member eq content x
  | t :: _ => exists (fn (_, y) => eq (x, y)) (Net.match_term net t));

fun cons x index (Items {eq, content, next, net}) =
  mk_items eq (x :: content) (next - 1)
    (fold (fn t => Net.insert_term (K false) (t, (next, x))) (index x) net);

fun cons_priorized prio x index (Items {eq, content, next, net}) =
  mk_items eq (x :: content) (Integer.min (prio - 1) (next - 1))
    (fold (fn t => Net.insert_term (K false) (t, (prio, x))) (index x) net);

(* merge respecting priorities *)
fun merge index (items1, Items {net = net2, ...}) =
  fold_rev (fn (prio, y) => if member index items1 y then I else cons_priorized prio y index)
    (Net.content net2) items1;

fun remove x index (items as Items {eq, content, next, net}) =
  if member index items x then
    mk_items eq (Library.remove eq x content) next
      (fold (fn t => Net.delete_term_safe (eq o pairself #2) (t, (0, x))) (index x) net)
  else items;

fun update x index items = cons x index (remove x index items);

end;
