(* Immutable bit vectors of arbitrary size, based on SMLs arbitrary size integers.
   Bit indexing is zero-based. *)
signature BIT_VECTOR = sig

  type bitvec

  val empty : bitvec

  val is_empty : bitvec -> bool
  (* size is slow: O(largest contained index) *)
  val size : bitvec -> int 
  val contains : int -> bitvec -> bool

  val single : int -> bitvec
  val insert : int -> bitvec -> bitvec
  val remove : int -> bitvec -> bitvec
  val intersect : bitvec -> bitvec -> bitvec
  val union : bitvec -> bitvec -> bitvec
  val subtract : bitvec -> bitvec -> bitvec

  val to_int : bitvec -> int
  val from_int : int -> bitvec

  val to_list : bitvec -> bool list
  val from_list : bool list -> bitvec
  val to_string : bitvec -> string

  val eq : bitvec * bitvec -> bool
  val subset : bitvec -> bitvec -> bool
  (* EQUAL means equals or incomparable *)
  val subset_ord : bitvec * bitvec -> order
  val bv_int_ord : bitvec * bitvec -> order
end


structure BitVector :> BIT_VECTOR = struct
  type bitvec = int

  val empty = 0

  fun is_empty bv = (bv = 0)
  fun size bv =
    if is_empty bv then
      0
    else
      size (IntInf.~>>(bv, Word.fromInt 1))
      + (if IntInf.andb(bv, 1) > 0 then 1 else 0)
  fun contains i bv = IntInf.andb(IntInf.~>>(bv, Word.fromInt i), 1) > 0

  fun single i = IntInf.<<(1, Word.fromInt i)
  fun intersect bv1 bv2 = IntInf.andb(bv1, bv2)
  fun union bv1 bv2 = IntInf.orb(bv1, bv2)
  fun subtract bv1 bv2 =
    (* toggles, i.e. removes, bits of bv2 in common with bv1 because
         bit XOR 1 = not bit,   bit XOR 0 = bit *)
    IntInf.xorb(bv2, intersect bv1 bv2)
  fun insert i bv = union bv (single i)
  fun remove i bv = bv |> subtract (single i)

  val to_int = I
  val from_int = I

  fun to_list bv =
    if is_empty bv then
      []
    else
      let val b1 = IntInf.andb(bv, 1) > 0
      in b1 :: to_list (IntInf.~>>(bv, Word.fromInt 1)) end
  fun from_list [] = 0
    | from_list (b :: bs) =
        IntInf.orb(IntInf.<<(from_list bs, Word.fromInt 1), 
          if b then 1 else 0)
  val to_string =
    to_list #> map (fn b => if b then "1" else "0") #> implode #> quote

  fun eq (bv1, bv2) = bv1 = bv2
  fun subset bv1 bv2 = (intersect bv1 bv2 = bv1)

  fun subset_ord (bv1, bv2) =
    if eq (bv1, bv2) then EQUAL
    else if subset bv1 bv2 then LESS
    else if subset bv2 bv1 then GREATER
    else EQUAL
  val bv_int_ord = pairself to_int #> int_ord
end


structure BitVectorTab = Table(type key = BitVector.bitvec val ord = BitVector.bv_int_ord);
structure BitVectorGraph = Graph(type key = BitVector.bitvec val ord = BitVector.bv_int_ord);

(*tests*)
(*
  val bv1 = BitVector.insert 5 (BitVector.empty);
  val bv2 = BitVector.insert 7 (BitVector.empty);
  val c1 = BitVector.contains 5 bv1;
  val nc1 = BitVector.contains 7 bv1;
  val c2 = BitVector.contains 7 bv2;
  val nc2 = BitVector.contains 5 bv2;
  val l1 = BitVector.to_list bv1;
  val l2 = BitVector.to_list bv2;
  val bv1' = BitVector.from_list l1;
  val bv2' = BitVector.from_list l2;
  val bv_un = BitVector.union bv1 bv2
  val bv_ins2 = BitVector.insert 5 bv2
  val bv_int = BitVector.intersect bv1 bv2
  val l_un = BitVector.to_list bv_un
  val l_int = BitVector.to_list bv_int
  val bv_un_rem = BitVector.remove 7 bv_un
  val b_un_rem = BitVector.to_list bv_un_rem
  val bv1_subset_bv_un = BitVector.subset bv1 bv_un
  val nsubset = BitVector.subset (BitVector.single 6) bv_un
  val subtr_irrel = BitVector.subtract bv_un (BitVector.single 8) |> BitVector.to_list
  val subtr_rel = BitVector.subtract bv_un (BitVector.insert 4 bv_un) |> BitVector.to_list
*)
