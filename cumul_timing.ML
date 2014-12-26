
signature CUMUL_TIMING = sig

  type cumul_timing_block

  val start_block : string -> string list -> cumul_timing_block
  val endprint_block : cumul_timing_block -> unit 

  val print_block : string -> string list -> (unit -> 'a) -> 'a

  val timing : string -> ('a -> 'b) -> 'a -> 'b
end



structure CumulTiming : CUMUL_TIMING = struct

(* FIXME:
    The characterization of recursive timings does not work in some non-trivial uses (compiler bug?!),
    so we do not try to recognize it anymore.
      Also I have observed many implausible timings (compiler bug?!), even for time spent in subcalls relative
    to calling functions, so the timings are best regarded as hints. *)

(* NB: Timing assumes single-threaded execution in ML process,
     so we make no efforts to provide thread-safe cumulative timing functions *)
(* the involved cases regarding recursive cumulative timing are

     output_local n (prints t1 + t2)
       cumul_timing n  with t1 + t2
         cumul_timing n  with t1 (does not register because recursive)
         output_local .. [n]   (prints t2, does not propagate registered subtiming t2 because recursive)
           cumul_timing n  with t2  (registers)

     output_local n (prints t1 + t2)
       cumul_timing n  with t1 (registers)
       output_local .. [n]   (prints t2, registers t1 + t2)
         cumul_timing n  with t2 (registers)

     output_local n (prints t1 + t2)
       output_local .. [n]   (prints t1, registers t1)
         cumul_timing n  with t1 (registers)
       cumul_timing n  with t2 (registers)
*)




type timing = { elapsed : Time.time, cpu : Time.time, gc : Time.time }

val timing_to_str = Timing.message
(*fun timing_to_str { elapsed } = Time.toString elapsed*)

(* Invariant: if we are timing recursively, i.e. there is a cumul_timing_active_tab entry for a timing name,
   there cannot be a corresponding timing entry, i.e. a cumul_timing_tab entry for that timing name *)
val cumul_timing_tab = Unsynchronized.ref (Symtab.empty : timing Symtab.table)
(* val cumul_timing_active_tab = Unsynchronized.ref (Symtab.empty : unit Symtab.table) *)

val timing_zero = { elapsed = Time.zeroTime, cpu = Time.zeroTime, gc = Time.zeroTime }
fun timing_plus timing1 timing2 =
  { elapsed = #elapsed timing1 + #elapsed timing2,
    cpu = #cpu timing1 + #cpu timing2,
    gc = #gc timing1 + #gc timing2 }

type cumul_timing_block = {
  cumul_name : string,
  timing_names : string list,
  timer_start: Timing.start,
  old_cumul_timing_tab : timing Symtab.table (*,
  old_cumul_timing_active_tab : unit Symtab.table*) }

fun start_block cumul_name timing_names = 
  let
    val tab0 = ! cumul_timing_tab
    val _ = cumul_timing_tab := (tab0 |> fold Symtab.delete_safe timing_names)
    (*val act_tab0 = ! cumul_timing_active_tab
    val _ = cumul_timing_active_tab := (act_tab0 |> fold Symtab.delete_safe timing_names)*)
  in
    { cumul_name = cumul_name, timing_names = timing_names,
      timer_start = Timing.start (),
      old_cumul_timing_tab = tab0 (*, old_cumul_timing_active_tab = act_tab0*) }
  end

fun endprint_block { cumul_name, timing_names, timer_start, 
    old_cumul_timing_tab (*, old_cumul_timing_active_tab*) } =
  let
    (* val _ = cumul_timing_active_tab := old_cumul_timing_active_tab *)

    val tab = ! cumul_timing_tab
    val _ = cumul_timing_tab := 
      let
        val _ = tracing (quote cumul_name^" cumulative timing point \n"
          ^"  complete time: "^timing_to_str (Timing.result timer_start)^"\n"
          ^cat_lines (timing_names |> map (fn n =>
            "  "^quote n^": "^(case Symtab.lookup tab n of
                SOME timing => timing_to_str timing
              | NONE => "no timing (not called?)"))))
      in
        tab |> fold (fn n =>
            (* if Symtab.defined old_cumul_timing_active_tab n then
              (* no propagation of subtiming because this is a recursive timing outside
                 of this local timing block *)
              Symtab.delete_safe n
            else *)
              (* subtiming propagation *)
              case Symtab.lookup old_cumul_timing_tab n of
                SOME timing0 => Symtab.map_default (n, timing_zero) (timing_plus timing0)
              | NONE => I)
          timing_names
      end
   in
     ()
   end

fun print_block cumul_name timing_names f =
  let
    val cumul_timing_block = start_block cumul_name timing_names
    val res0 = Exn.interruptible_capture f ()
    val _ = endprint_block cumul_timing_block
  in Exn.release res0 end


(* NB: since we do not treat timings of recursive functions,
   f may not contain recursion leading towards this timing call, otherwise
   timings of recursive subcalls are counted multiple times *)
fun timing timing_name f x =
  let
    (* val timing_recursively = Symtab.defined (! cumul_timing_active_tab) timing_name
    val _ =
      if timing_recursively then ()
      else
        cumul_timing_active_tab := (! cumul_timing_active_tab |> Symtab.update_new (timing_name, ())) *)

    val (timing, res0) = Timing.timing (Exn.interruptible_capture (fn () => f x)) ()
    (* val _ = warning ("timing for "^quote timing_name^":  "^Timing.message timing) *)
    val res = Exn.release res0

    val timing0 = Symtab.lookup (! cumul_timing_tab) timing_name |> the_default timing_zero
    val timing2 = timing_plus timing timing0
    (* val _ = tracing ("accumulating timing "^quote timing_name^" := "^timing_to_str timing2
      ^" = "^timing_to_str timing0^" + "^timing_to_str timing) *)

    val _ =
      (* if timing_recursively then ()
      else *)
        let 
          (* accumulation of subsequent timings *)
          val _ = cumul_timing_tab := (! cumul_timing_tab |> Symtab.update (timing_name, timing2))
          (*val _ = cumul_timing_active_tab := (! cumul_timing_active_tab |> Symtab.delete timing_name)
          val _ =
            if Symtab.defined (! cumul_timing_active_tab) timing_name then
              error "recursiveness of timing not removed"
            else () *)
        in () end
  in
    res
  end




(*
ML {*

  val _ = CumulTiming.print_block "top6" ["t6", "t6sub"] (fn () =>
    let
      val _ = CumulTiming.timing "t6" (fn () =>
        let
          val _ = OS.Process.sleep (seconds 0.2)
          val _ = CumulTiming.timing "t6sub" (fn () => OS.Process.sleep (seconds 0.3)) ()
        in () end) ()
      val _ = CumulTiming.timing "t6" (fn () =>
        let
          val _ = OS.Process.sleep (seconds 0.2)
          val _ = CumulTiming.timing "t6sub" (fn () => OS.Process.sleep (seconds 0.3)) ()
        in () end) ()
    in () end)

  val _ = CumulTiming.print_block "top8" ["t8", "t8sub"] (fn () =>
    let
      val _ = CumulTiming.timing "t8" (fn () =>
        let
          val _ = OS.Process.sleep (seconds 0.2)
          val _ = CumulTiming.timing "t8sub" (fn () => OS.Process.sleep (seconds 0.3)) ()
        in () end) ()
      val _ = CumulTiming.timing "t8sub" (fn () => OS.Process.sleep (seconds 0.3)) ()
    in () end)
*}

ML {*
  val _ = CumulTiming.print_block "top7" ["t7", "t7sub"] (fn () =>
    let
      val _ = CumulTiming.timing "t7" (fn () =>
        let
          val _ = OS.Process.sleep (seconds 0.2)
          val _ = CumulTiming.timing "t7sub" (fn () => OS.Process.sleep (seconds 0.3)) ()
        in () end) ()
    in () end)

  val _ = CumulTiming.print_block "top1" ["t1"] (fn () =>
    let
      val _ = CumulTiming.timing "t1" (fn () => OS.Process.sleep (seconds 0.2)) ()
      val _ = CumulTiming.timing "t1" (fn () => OS.Process.sleep (seconds 0.3)) ()
    in () end)

  val _ = CumulTiming.print_block "top2" ["t2"] (fn () =>
    CumulTiming.timing "t2" (fn () =>
      CumulTiming.timing "t2" (fn () => OS.Process.sleep (seconds 0.5)) ()) ())

  val _ = CumulTiming.print_block "top3" ["t3"] (fn () =>
    CumulTiming.timing "t3" (fn () =>
      let
        val _ = CumulTiming.timing "t3" (fn () => OS.Process.sleep (seconds 0.2)) ()
        val _ = CumulTiming.print_block "sub3" ["t3"] (fn () => 
         CumulTiming.timing "t3" (fn () => OS.Process.sleep (seconds 0.3)) ())
      in () end) ())

  val _ = CumulTiming.print_block "top4" ["t4"] (fn () =>
    let
      val _ = CumulTiming.timing "t4" (fn () => OS.Process.sleep (seconds 0.2)) ()
      val _ = CumulTiming.print_block "sub4" ["t4"] (fn () => 
       CumulTiming.timing "t4" (fn () => OS.Process.sleep (seconds 0.3)) ())
    in () end)

val _ = CumulTiming.print_block "top5" ["t5"] (fn () =>
    let
      val _ = CumulTiming.print_block "sub5" ["t5"] (fn () => 
       CumulTiming.timing "t5" (fn () => OS.Process.sleep (seconds 0.3)) ())
      val _ = CumulTiming.timing "t5" (fn () => OS.Process.sleep (seconds 0.2)) ()
    in () end)
  
*}

*)


end
