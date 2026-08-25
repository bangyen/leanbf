/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Parser
import LeanBF.Theory.BodyLoop

/-!
# Cat

The `cat` program `,[.,]`, which echoes its input. It is the first example
here whose behaviour depends on the input rather than on constants fixed in
the program, so unlike `HelloWorld` it is stated as a theorem quantified over
every input, with `decide` reserved for concrete illustrations.

What it actually computes is narrower than "echo the input", and two of this
formalization's design choices are the reason.

A `,` at end of input writes `0` rather than leaving the cell alone or
failing, so on empty input the loop is never entered and the program halts in
two steps. And `[` exits on a zero cell, so a `0` byte anywhere in the input
ends the loop: the program copies the input's *zero-free prefix* and stops,
leaving the rest unread. `cat` is an echo only on inputs that contain no zero
byte, which `catRuns` states exactly rather than assuming — the output is
`input.takeWhile (· != 0)` and the unread remainder is
`(input.dropWhile (· != 0)).tail`.

The pointer never moves: every instruction is `,`, `.` or a loop over them,
so the whole program works in one cell.

## Main definitions

* `cat`: The program `,[.,]`.
* `catSource`: The concrete Brainfuck source for `cat`.
* `catLoop`: The loop `[.,]` that `cat` runs after its first read.
* `catState`: The initial state, holding the input on an empty tape.
* `catFinal`: The state `cat` ends in on a given input.

## Theorems

* `parse_catSource`: The program is exactly what its concrete syntax parses to.
* `loop_free_catBody`: The loop's body contains no loop.
* `runsTo_catLoop_zero`: A zero cell exits the loop at once.
* `runsTo_catLoop`: The loop copies the zero-free prefix of what remains.
* `catRuns`: `cat` outputs the input's zero-free prefix and halts.
* `cat_executes`: `cat` completes in an exact number of steps.
* `cat_halts`: `cat` halts on every input.
-/

namespace LeanBF.Examples

open LeanBF

/-- The `cat` program `,[.,]`: read a byte, then echo and read until a `0`. -/
def cat : Program :=
  [.read, .loop [.write, .read]]

/-- The concrete Brainfuck source for `cat`. -/
def catSource : String := ",[.,]"

/-- The loop `[.,]` that `cat` runs after its first read. -/
def catLoop : Program :=
  [.loop [.write, .read]]

/-- The initial state: the input on an empty tape, pointer at cell `0`. -/
def catState (input : List Nat) : State where
  ptr := 0
  tape := fun _ => 0
  input := input
  output := []

/-- The state `cat` ends in: the zero-free prefix of the input written out
    (most recent first), the rest of the input unread, and the single cell it
    works in left at `0`. -/
def catFinal (input : List Nat) : State where
  ptr := 0
  tape := fun _ => 0
  input := (input.dropWhile (· != 0)).tail
  output := (input.takeWhile (· != 0)).reverse

/-- The hand-written `cat` program is exactly what its concrete syntax parses
    to, so the transcription in this file is machine-checked. -/
theorem parse_catSource : parse catSource = cat := by
  rfl

/-- The loop's body contains no loop. -/
theorem loop_free_catBody : LoopFree [Instruction.write, Instruction.read] := by
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  exact loop_free_single _ (by intro body h; cases h)

/-- A zero cell exits the loop at once, leaving the state untouched. This is
    the loop's base case in both directions: an input that starts with a zero
    byte, and an input that has run out (where the preceding `,` wrote `0`). -/
theorem runsTo_catLoop_zero (s : State) (hv : s.tape s.ptr = 0) :
    RunsTo (catLoop, s) { s with tape := fun i => if i = s.ptr then 0 else s.tape i } := by
  have hzero : s.currentVal = 0 := by simp only [State.currentVal, hv]
  have hstep : step catLoop s = some ([], s) := by
    simp only [catLoop, step, if_pos hzero]
  have heq : { s with tape := fun i => if i = s.ptr then 0 else s.tape i } = s := by
    apply State.ext
    · rfl
    · funext i
      by_cases hi : i = s.ptr
      · simp only [hi, if_true, hv]
      · simp only [if_neg hi]
    · rfl
    · rfl
  rw [heq]
  exact RunsTo.step catLoop s s [] s hstep (RunsTo.halt s)

/-- The loop `[.,]` copies the zero-free prefix of the remaining input.

    Stated for an arbitrary current cell value `v` and remaining input, so
    that it composes with the `,` that precedes it. A zero cell exits at once,
    leaving the input untouched; otherwise the loop writes `v`, reads the next
    byte, and repeats. The byte that eventually stops the loop has already been
    consumed by a `,`, which is why the surviving input drops it. -/
theorem runsTo_catLoop : ∀ (inp : List Nat) (v : Nat) (s : State),
    s.tape s.ptr = v → s.input = inp →
    RunsTo (catLoop, s)
      { s with
        tape := fun i => if i = s.ptr then 0 else s.tape i,
        input := if v = 0 then inp else (inp.dropWhile (· != 0)).tail,
        output := (if v = 0 then [] else v :: inp.takeWhile (· != 0)).reverse
          ++ s.output } := by
  intro inp
  induction inp with
  | nil =>
      intro v s hv hinp
      by_cases hv0 : v = 0
      · -- Zero cell: the loop exits without running its body.
        have hz := runsTo_catLoop_zero s (by rw [hv, hv0])
        have heq :
            { s with
              tape := fun i => if i = s.ptr then 0 else s.tape i }
            = { s with
              tape := fun i => if i = s.ptr then 0 else s.tape i,
              input := if v = 0 then ([] : List Nat)
                else (([] : List Nat).dropWhile (· != 0)).tail,
              output := (if v = 0 then []
                else v :: ([] : List Nat).takeWhile (· != 0)).reverse ++ s.output } := by
          apply State.ext
          · rfl
          · rfl
          · simp only [hv0, if_true, hinp]
          · simp only [hv0, if_true, List.reverse_nil, List.nil_append]
        rwa [heq] at hz
      · -- Non-zero cell, spent input: write `v`, then the `,` at end of input
        -- writes `0`, and the next test exits.
        set t : State :=
          { s with
            tape := fun i => if i = s.ptr then 0 else s.tape i,
            input := [],
            output := v :: s.output } with ht
        have hne : s.currentVal ≠ 0 := by simp only [State.currentVal, hv]; exact hv0
        have hstep : step catLoop s = some ([.write, .read] ++ catLoop, s) := by
          simp only [catLoop, step, if_neg hne, List.append_nil]
        have hbody : RunsTo ([Instruction.write, Instruction.read], s) t := by
          have h := runsTo_of_loopFree [Instruction.write, Instruction.read] s
            loop_free_catBody
          have hrun : runSeq [Instruction.write, Instruction.read] s = t := by
            simp only [runSeq, stepOne, hinp, ht, State.currentVal, hv]
          rwa [hrun] at h
        have hz := runsTo_catLoop_zero t (by simp only [ht, if_true])
        have hfinal :
            { t with tape := fun i => if i = t.ptr then 0 else t.tape i }
            = { s with
              tape := fun i => if i = s.ptr then 0 else s.tape i,
              input := if v = 0 then ([] : List Nat)
                else (([] : List Nat).dropWhile (· != 0)).tail,
              output := (if v = 0 then []
                else v :: ([] : List Nat).takeWhile (· != 0)).reverse ++ s.output } := by
          apply State.ext
          · rfl
          · funext i
            by_cases hi : i = s.ptr
            · simp only [ht, hi, if_true]
            · simp only [ht, if_neg hi]
          · simp only [ht, if_neg hv0, List.dropWhile_nil, List.tail_nil]
          · simp only [ht, if_neg hv0, List.takeWhile_nil, List.reverse_cons,
              List.reverse_nil, List.nil_append, List.cons_append]
        rw [hfinal] at hz
        exact RunsTo.step catLoop s s ([.write, .read] ++ catLoop) _ hstep
          (RunsTo_append catLoop t _ hbody hz)
  | cons x xs ih =>
      intro v s hv hinp
      by_cases hv0 : v = 0
      · -- Zero cell: the loop exits, leaving the unread input alone.
        have hz := runsTo_catLoop_zero s (by rw [hv, hv0])
        have heq :
            { s with
              tape := fun i => if i = s.ptr then 0 else s.tape i }
            = { s with
              tape := fun i => if i = s.ptr then 0 else s.tape i,
              input := if v = 0 then (x :: xs)
                else ((x :: xs).dropWhile (· != 0)).tail,
              output := (if v = 0 then []
                else v :: (x :: xs).takeWhile (· != 0)).reverse ++ s.output } := by
          apply State.ext
          · rfl
          · rfl
          · simp only [hv0, if_true, hinp]
          · simp only [hv0, if_true, List.reverse_nil, List.nil_append]
        rwa [heq] at hz
      · -- Non-zero cell: write `v`, read `x`, and recurse on `xs`.
        set t : State :=
          { s with
            tape := fun i => if i = s.ptr then x else s.tape i,
            input := xs,
            output := v :: s.output } with ht
        have hne : s.currentVal ≠ 0 := by simp only [State.currentVal, hv]; exact hv0
        have hstep : step catLoop s = some ([.write, .read] ++ catLoop, s) := by
          simp only [catLoop, step, if_neg hne, List.append_nil]
        have hbody : RunsTo ([Instruction.write, Instruction.read], s) t := by
          have h := runsTo_of_loopFree [Instruction.write, Instruction.read] s
            loop_free_catBody
          have hrun : runSeq [Instruction.write, Instruction.read] s = t := by
            simp only [runSeq, stepOne, hinp, ht, State.currentVal, hv]
          rwa [hrun] at h
        have hrest := ih x t (by simp only [ht, if_true]) rfl
        have hfinal :
            { t with
              tape := fun i => if i = t.ptr then 0 else t.tape i,
              input := if x = 0 then xs else (xs.dropWhile (· != 0)).tail,
              output := (if x = 0 then [] else x :: xs.takeWhile (· != 0)).reverse
                ++ t.output }
            = { s with
              tape := fun i => if i = s.ptr then 0 else s.tape i,
              input := if v = 0 then (x :: xs)
                else ((x :: xs).dropWhile (· != 0)).tail,
              output := (if v = 0 then []
                else v :: (x :: xs).takeWhile (· != 0)).reverse ++ s.output } := by
          apply State.ext
          · rfl
          · funext i
            by_cases hi : i = s.ptr
            · simp only [ht, hi, if_true]
            · simp only [ht, if_neg hi]
          · by_cases hx : x = 0
            · simp only [hx, if_neg hv0, if_true, List.dropWhile_cons]
              norm_num
            · simp only [if_neg hv0, if_neg hx, List.dropWhile_cons]
              norm_num [hx]
          · by_cases hx : x = 0
            · simp only [ht, hx, if_neg hv0, if_true, List.takeWhile_cons]
              norm_num
            · simp only [ht, if_neg hv0, if_neg hx, List.takeWhile_cons]
              norm_num [hx]
        rw [hfinal] at hrest
        exact RunsTo.step catLoop s s ([.write, .read] ++ catLoop) _ hstep
          (RunsTo_append catLoop t _ hbody hrest)

/-- `cat` outputs the input's zero-free prefix and halts.

    The initial `,` reads the first byte — or writes `0` if there is none —
    and the loop then copies until it meets a zero. So the output is
    `input.takeWhile (· != 0)`, most recent write first, and whatever follows
    the stopping byte is left unread. On an input with no zero byte this is a
    faithful echo; on any other it stops early, and on the empty input it
    halts having written nothing. -/
theorem catRuns (input : List Nat) :
    RunsTo (cat, catState input) (catFinal input) := by
  cases input with
  | nil =>
      -- No input: `,` writes `0`, so the loop is never entered.
      have hstep : step cat (catState []) = some (catLoop, catState []) := by
        simp only [cat, catLoop, step, catState]
        congr 2
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = (0 : Int)
          · simp only [hi, if_true]
          · simp only [if_neg hi]
        · rfl
        · rfl
      have hz := runsTo_catLoop_zero (catState []) rfl
      have heq : { catState [] with
          tape := fun i => if i = (catState []).ptr then 0 else (catState []).tape i }
          = catFinal [] := by
        apply State.ext
        · rfl
        · funext i
          simp only [catState, catFinal]
          by_cases hi : i = (0 : Int)
          · simp only [hi, if_true]
          · simp only [if_neg hi]
        · rfl
        · rfl
      rw [heq] at hz
      exact RunsTo.step cat (catState []) (catState []) catLoop (catFinal []) hstep hz
  | cons x xs =>
      -- The first `,` consumes `x`, and the loop copies from there.
      set s0 : State :=
        { ptr := 0,
          tape := fun i => if i = 0 then x else 0,
          input := xs,
          output := [] } with hs0
      have hstep : step cat (catState (x :: xs)) = some (catLoop, s0) := by
        simp only [cat, catLoop, step, catState, hs0]
      have hloop := runsTo_catLoop xs x s0 (by simp only [hs0, if_true]) rfl
      have hfinal :
          { s0 with
            tape := fun i => if i = s0.ptr then 0 else s0.tape i,
            input := if x = 0 then xs else (xs.dropWhile (· != 0)).tail,
            output := (if x = 0 then [] else x :: xs.takeWhile (· != 0)).reverse
              ++ s0.output }
          = catFinal (x :: xs) := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = (0 : Int)
          · simp only [hs0, hi, if_true, catFinal]
          · simp only [hs0, if_neg hi, catFinal]
        · by_cases hx : x = 0
          · simp only [hx, if_true, catFinal, List.dropWhile_cons]
            norm_num
          · simp only [if_neg hx, catFinal, List.dropWhile_cons]
            norm_num [hx]
        · by_cases hx : x = 0
          · simp only [hs0, hx, if_true, catFinal, List.takeWhile_cons]
            norm_num
          · simp only [hs0, if_neg hx, catFinal, List.takeWhile_cons]
            norm_num [hx]
      rw [hfinal] at hloop
      exact RunsTo.step cat (catState (x :: xs)) s0 catLoop (catFinal (x :: xs)) hstep hloop

/-- `cat` completes in an exact number of steps on every input, ending in
    `catFinal`. Unlike the loops it is built from, this needs no side
    condition: the input is a finite list, and the `,` at end of input supplies
    the `0` that stops the loop once the list runs out. -/
theorem cat_executes (input : List Nat) :
    ∃ n, RunsExactly n cat (catState input) (catFinal input) :=
  run_of_RunsTo (cat, catState input) (catFinal input) (catRuns input)

/-- `cat` halts on every input. -/
theorem cat_halts (input : List Nat) : halts cat (catState input) := by
  obtain ⟨n, _, hsteps⟩ := cat_executes input
  exact ⟨n + 1, by simp only [haltsWithin, hsteps]; omega⟩

/-- On an input with no zero byte, `cat` is a faithful echo. -/
example : (run 30 cat (catState [72, 105])).map (fun s => s.output)
    = some [105, 72] := by
  decide

/-- A zero byte stops it early: `105` is never read, let alone written. -/
example : (run 30 cat (catState [72, 0, 105])).map (fun s => s.output)
    = some [72] := by
  decide

/-- On empty input the loop is never entered, and `cat` halts in two steps. -/
example : stepsToHalt 30 cat (catState []) = 2 := by
  decide

end LeanBF.Examples
