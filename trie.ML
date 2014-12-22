
signature TRIE = sig
  type key
  type 'a T

  val empty : 'a T

  val is_empty : 'a T -> bool
  val lookup : 'a T -> key -> 'a option

  val fold_trie : (key * 'a -> 'b -> 'b) -> 'a T -> 'b -> 'b
  val exists : (key * 'a -> bool) -> 'a T -> bool
  val get_first : (key * 'a -> 'b option) -> 'a T -> 'b option

  val dest : 'a T -> (key * 'a) list

  exception DUP
  val modify : key -> ('a option -> 'a option) -> 'a T -> 'a T
  val update : key * 'a -> 'a T -> 'a T
  val update_new : key * 'a -> 'a T -> 'a T
  val insert : ('a * 'a -> bool) -> key * 'a -> 'a T -> 'a T
  val map_entry : key -> ('a -> 'a) -> 'a T -> 'a T
  val map_default : key * 'a -> ('a -> 'a) -> 'a T -> 'a T

  exception UNDEF
  val delete : key -> 'a T -> 'a T

  val lookup_some_subset : 'a T -> key ->  (key * 'a) option
  val lookup_some_superset : 'a T -> key -> (key * 'a) option

  (* does not check equality to the entry with a subsuming key,
     should it exist *)
  val subsuming_insert : key * 'a -> 'a T -> 'a T * bool
end




signature FIXORDER_SET = sig
  type T
  val empty : T
  val split_first : T -> (int * T) option
  val insert : int -> T -> T
end


(* Trie indexing structure for bit vectors of arbitrary size.
   NB: actually slower for common purposes than subsumptive management of a bitvector list. *)
functor FixOrderSetTrie(Set : FIXORDER_SET) : TRIE = struct

  type key = Set.T
  datatype 'a T = Node of 'a option * 'a T Inttab.table

  val empty = Node (NONE, Inttab.empty)

  fun is_empty (Node (opt_entry, subs)) =
    not (is_some opt_entry) andalso Inttab.is_empty subs

  fun lookup (Node (opt_entry, subs)) set =
    case Set.split_first set of
      NONE => opt_entry
    | SOME (i, set2) => (case Inttab.lookup subs i of
        NONE => NONE
      | SOME node2 => lookup node2 set2)

  fun fold_trie f =
    let
      fun aux set0 (Node (opt_entry, subs)) =
        (case opt_entry of
          SOME x => f (set0, x)
        | NONE => I)
        #> Inttab.fold (fn (i, node2) => aux (Set.insert i set0) node2) subs
    in
      aux Set.empty 
    end
  fun exists p node = false
    |> fold_trie (fn (set, x) => fn b => b orelse p (set, x)) node

  fun get_first f =
    let
      fun first_in_subs set0 = 
        Inttab.get_first (fn (i, node2) => aux (Set.insert i set0) node2)
      and aux set0 (Node (opt_entry, subs)) =
        case opt_entry of
          SOME x => (case f (set0, x) of 
            SOME y => SOME y
          | NONE => first_in_subs set0 subs)
        | NONE => first_in_subs set0 subs
    in
      aux Set.empty
    end

  fun dest t = fold_trie cons t []



  exception UNDEF

  fun delete set node =
    let
      fun aux set (Node (opt_entry, subs)) =
        case Set.split_first set of
          NONE => (Node(NONE, subs), not (Inttab.is_empty subs))
        | SOME (i, set2) => (case Inttab.lookup subs i of
            NONE => raise UNDEF
          | SOME node2 =>
              let
                val (node2', non_collapse2) = aux set2 node2
                val subs' =
                  if non_collapse2 then Inttab.update (i, node2') subs
                  else Inttab.delete i subs
                val non_collapse = is_some opt_entry orelse not (Inttab.is_empty subs')
              in (Node (opt_entry, subs'), non_collapse) end)
    in
      aux set node |> fst
    end

  fun modify set f (Node (opt_entry, subs)) =
    case Set.split_first set of
      NONE => Node (f opt_entry, subs)
    | SOME (i, set2) =>
        let val subs2 = subs |> Inttab.map_default (i, empty) (modify set2 f)
        in Node (opt_entry, subs2) end

  exception DUP

  fun update_new (set, x) = modify set (fn SOME _ => raise DUP | NONE => SOME x)
  fun update (set, x) = modify set (K (SOME x))
  fun insert eq (set, x) = modify set (fn NONE => SOME x | SOME y => if eq (x, y) then SOME y else raise DUP)
  fun map_entry set f = modify set (fn SOME x => SOME (f x) | NONE => NONE)
  fun map_default (set, default) f = modify set (fn SOME x => SOME (f x) | NONE => SOME (f default))

  fun lookup_some_subset node set =
    let
      fun aux (node as Node (opt_entry, subs)) set0 set =
        case opt_entry of
          SOME x => SOME (set0, x)
        | NONE => (case Set.split_first set of
            NONE => NONE
          | SOME (i, set2) => case Inttab.lookup subs i of
              NONE => aux node set0 set2 
            | SOME node2 => (case aux node2 (Set.insert i set0) set2 of
                SOME res => SOME res
              | NONE => aux node set0 set2))
    in
      aux node Set.empty set
    end

  fun lookup_some_superset node set =
    let
      fun aux (Node (opt_entry, subs)) set0 set =
        case Set.split_first set of
          NONE => (case opt_entry of
            SOME x => SOME (set0, x)
          | NONE => (case Inttab.min_key subs of
              NONE => NONE
            | SOME min_i =>
                (* NB: we know there must this subtrie must contain some set due to
                   collapsing of unnecessary subtrie nodes on removal *)
                aux (Inttab.lookup subs min_i |> the) (Set.insert min_i set0) Set.empty))
        | SOME (i, set2) => (case Inttab.lookup subs i of
            NONE => NONE
          | SOME node2 => aux node2 (Set.insert i set0) set2)
    in
      aux node Set.empty set
    end
  

  fun insert_w_superset_prune (set, x) (Node (opt_entry, subs)) =
    case Set.split_first set of
      NONE => (case opt_entry of
        SOME y => Node (SOME y, Inttab.empty)
      | NONE => Node (SOME x, Inttab.empty))
    | SOME (i, set2) =>
        let
          val subs2 = subs |> Inttab.map_default (i, empty)
            (insert_w_superset_prune (set2, x))
        in Node (opt_entry, subs2) end

  fun subsuming_insert (set, x) node =
    case lookup_some_subset node set of
      NONE => (insert_w_superset_prune (set, x) node, true)
    | SOME (_, y) => (node, false)

end




structure BitVectorFixOrderSet : FIXORDER_SET = struct
  type T = BitVector.bitvec
  val empty = BitVector.empty
  val split_first = BitVector.split_first
  fun insert i = BitVector.union (BitVector.single i)
end

structure BitVectorTrie : TRIE = FixOrderSetTrie(BitVectorFixOrderSet);



functor ProductTrie(structure Trie1 : TRIE   structure Trie2 : TRIE) : TRIE = struct

  type key = Trie1.key * Trie2.key
  type 'a T = ('a Trie2.T) Trie1.T

  val empty = Trie1.empty
  val is_empty = Trie1.is_empty 
  fun lookup t (k1, k2) =
    case Trie1.lookup t k1 of
      NONE => NONE
    | SOME t2 => Trie2.lookup t2 k2

  fun fold_trie f = Trie1.fold_trie (fn (k1, t2) =>
    Trie2.fold_trie (fn (k2, x) => f ((k1, k2), x)) t2)
  fun exists p t = false |> fold_trie (fn (ks, x) => fn b => b orelse p (ks, x)) t
  fun get_first f = Trie1.get_first (fn (k1, t2) =>
    Trie2.get_first (fn (k2, x) => f ((k1, k2), x)) t2)

  fun dest t = fold_trie cons t []

  fun modify (k1, k2) (f : 'a option -> 'a option) (t : 'a T) =
    Trie1.map_default (k1, Trie2.empty) (Trie2.modify k2 f) t

  exception DUP

  fun update_new (ks, x) = modify ks (fn SOME _ => raise DUP | NONE => SOME x)
  fun update (ks, x) = modify ks (K (SOME x))
  fun insert eq (ks, x) = modify ks (fn NONE => SOME x | SOME y => if eq (x, y) then SOME y else raise DUP)
  fun map_entry ks f = modify ks (fn SOME x => SOME (f x) | NONE => NONE)
  fun map_default (ks, default) f = modify ks (fn SOME x => SOME (f x) | NONE => SOME (f default))

  exception UNDEF

  fun delete (k1, k2) t = case Trie1.lookup t k1 of
      NONE => raise UNDEF
    | SOME t2 => (case Trie2.lookup t2 k2 of
        NONE => raise UNDEF
      | SOME _ =>
          let val t2' = Trie2.delete k2 t2
          in
            if Trie2.is_empty t2' then Trie1.delete k1 t
            else Trie1.update (k1, t2') t
          end)


  fun lookup_some_subset t (k1, k2) =
    case Trie1.lookup_some_subset t k1 of
      NONE => NONE
    | SOME (k1', t2) => (case Trie2.lookup_some_subset t2 k2 of
        NONE => NONE
      | SOME (k2', x) => SOME ((k1', k2'), x))
  fun lookup_some_superset t (k1, k2) =
    case Trie1.lookup_some_superset t k1 of
      NONE => NONE
    | SOME (k1', t2) => (case Trie2.lookup_some_superset t2 k2 of
        NONE => NONE
      | SOME (k2', x) => SOME ((k1', k2'), x))

  fun subsuming_insert ((k1, k2), x) t =
    case Trie1.lookup_some_subset t k1 of
      NONE => (insert (K true) ((k1, k2), x) t, true)
    | SOME (k1', t2) => 
        let val (t2', ch) = Trie2.subsuming_insert (k2, x) t2
        in
          if ch then (Trie1.update (k1', t2') t, true)
          else (t, false)
        end
end





structure IntTrie : TRIE = struct

  type key = int
  type 'a T = 'a Inttab.table

  val empty = Inttab.empty
  val is_empty = Inttab.is_empty
  val lookup = Inttab.lookup
  val fold_trie = Inttab.fold
  val exists = Inttab.exists
  val get_first = Inttab.get_first

  val dest = Inttab.dest

  exception DUP

  fun modify k f tab = 
    case f (Inttab.lookup tab k) of
      NONE => Inttab.delete_safe k tab
    | SOME x2 => Inttab.update (k, x2) tab


  fun update_new (k, x) tab =
    Inttab.update_new (k, x) tab handle Inttab.DUP _ => raise DUP
  val update = Inttab.update
  val insert = Inttab.insert
  val map_entry = Inttab.map_entry
  val map_default = Inttab.map_default

  exception UNDEF

  fun delete k tab =
    Inttab.delete k tab handle Inttab.UNDEF _ => raise UNDEF

  fun lookup_some_subset tab k = lookup tab k |> Option.map (pair k)
  fun lookup_some_superset tab k = lookup tab k |> Option.map (pair k)

  fun subsuming_insert (k, x) tab =
    (insert (K true) (k, x) tab, true)
end

