/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Transfer.Loops

/-!
# Composite Register Fragments

Fragments built by combining the transfer loops: copying a register without
destroying it, adding two registers, and running a body once per unit of a
counter.

Draining is destructive, so `copy_reaches` sends each drained unit to two
targets and `copyBack_reaches` pours one of them back. That is how a register
is read more than once, which `Nat.pair` requires of its arguments.

`copyBack_effect` restates the copy by what it does to each register rather
than as a nested state term. Fragments chain by matching one's postcondition
against the next one's precondition, and effects match where nested
constructor applications do not; `addVar_effect` is the immediate payoff.

The two iteration lemmas differ in what they let a body do. `iterate_reaches`
takes the body as a state transformer, which suits a body whose effect is a
fixed function of the state. `iterate_inv` threads an invariant indexed by
the iterations remaining, which is what a loop that accumulates needs —
multiplying by repeated addition, or primitive recursion. Its invariant must
ignore the counter, which is what makes decrementing the counter harmless.

## Main definitions

* `copied`: The state after the copy loop has run to completion.
* `copyMid`: The copy loop's state after its first increment.
* `copyLoop`: The copy loop's state back at the loop head.
* `copyDec`: The copy loop's state after its `jzdec` step.

## Theorems

* `copy_reaches`: The copy loop duplicates a register into two others.
* `iterate_reaches`: A counted loop runs a body once per unit of a counter.
* `copyBack_reaches`: A register is copied without being destroyed.
* `copyBack_effect`: The copy stated by its effect on each register.
* `addVar_effect`: Two registers are added into a third, both preserved.
* `iterate_inv`: A counted loop whose body maintains an invariant.
-/

namespace LeanBF

namespace Register

/-- The state after copying `n` units from `a` into both `t1` and `t2`. -/
def copied (a t1 t2 exit n : Nat) (s : State) : State :=
  { pc := exit,
    regs := fun i => if i = a then 0 else if i = t1 then s.regs t1 + n
      else if i = t2 then s.regs t2 + n else s.regs i }

/-- After the first increment of one iteration. -/
def copyMid (a t1 base n : Nat) (s : State) : State :=
  { pc := base + 2, regs := fun i => if i = t1 then s.regs t1 + 1
      else if i = a then n else s.regs i }

/-- After both increments of one iteration, back at the loop head. -/
def copyLoop (a t1 t2 base n : Nat) (s : State) : State :=
  { pc := base, regs := fun i => if i = t2 then s.regs t2 + 1
      else if i = t1 then s.regs t1 + 1 else if i = a then n else s.regs i }

/-- After the jzdec of one iteration. -/
def copyDec (a base n : Nat) (s : State) : State :=
  { pc := base + 1, regs := fun i => if i = a then n else s.regs i }

/-- The copy loop duplicates the source into two targets, emptying it. -/
theorem copy_reaches (p : Program) (a t1 t2 base exit : Nat)
    (h1 : a ≠ t1) (h2 : a ≠ t2) (h12 : t1 ≠ t2)
    (h0 : p[base]? = some (Instruction.jzdec a exit (base + 1)))
    (hi1 : p[base + 1]? = some (Instruction.inc t1 (base + 2)))
    (hi2 : p[base + 2]? = some (Instruction.inc t2 base)) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n →
      Reaches p s (copied a t1 t2 exit n s) := by
  have h1' : t1 ≠ a := fun hc => h1 hc.symm
  have h2' : t2 ≠ a := fun hc => h2 hc.symm
  have h12' : t2 ≠ t1 := fun hc => h12 hc.symm
  intro n
  induction n with
  | zero =>
      intro s hpc ha
      have hstep : step p s = some { s with pc := exit } := by
        simp only [step, hpc, h0, ha, if_pos]
      have hst : ({ pc := exit, regs := s.regs } : State) = copied a t1 t2 exit 0 s := by
        unfold copied
        ext i
        · simp only
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, hia, ha]
          · rw [if_neg hia]
            by_cases hit1 : i = t1
            · rw [if_pos hit1, hit1, Nat.add_zero]
            · rw [if_neg hit1]
              by_cases hit2 : i = t2
              · rw [if_pos hit2, hit2, Nat.add_zero]
              · rw [if_neg hit2]
      rw [← hst]
      exact Reaches.step s _ _ hstep (Reaches.refl _)
  | succ m ih =>
      intro s hpc ha
      have hs1 : step p s = some (copyDec a base m s) := by
        unfold copyDec
        simp only [step, hpc, h0, ha, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hs2 : step p (copyDec a base m s) = some (copyMid a t1 base m s) := by
        unfold copyDec copyMid
        simp only [step, hi1, setReg, if_neg h1']
      have hs3 : step p (copyMid a t1 base m s) = some (copyLoop a t1 t2 base m s) := by
        unfold copyMid copyLoop
        simp only [step, hi2, setReg, if_neg h12', if_neg h2']
      have hpcL : (copyLoop a t1 t2 base m s).pc = base := by simp only [copyLoop]
      have hregL : (copyLoop a t1 t2 base m s).regs a = m := by
        simp only [copyLoop, if_neg h2, if_neg h1, if_true]
      have hrec := ih (copyLoop a t1 t2 base m s) hpcL hregL
      have hfin : copied a t1 t2 exit m (copyLoop a t1 t2 base m s)
          = copied a t1 t2 exit (m + 1) s := by
        unfold copied copyLoop
        ext i
        · simp only
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia]
            by_cases hit1 : i = t1
            · subst hit1
              simp only [if_neg h12, if_neg hia, if_true]
              omega
            · rw [if_neg hit1, if_neg hit1]
              by_cases hit2 : i = t2
              · subst hit2
                simp only [if_neg hia, if_true, if_neg hit1]
                omega
              · rw [if_neg hit2, if_neg hit2]
                simp only [if_neg hit2, if_neg hit1, if_neg hia]
      rw [← hfin]
      exact Reaches.step s _ _ hs1 (Reaches.step _ _ _ hs2 (Reaches.step _ _ _ hs3 hrec))

/-- Iterating a body: the counter register drives how many times the body
    runs. The body is given abstractly as a state transformer `F` together
    with the fact that it reaches `F s` from `base + 1`, returning to `base`.
    The counter must not be touched by the body. -/
theorem iterate_reaches (p : Program) (c base exit : Nat) (F : State → State)
    (h0 : p[base]? = some (Instruction.jzdec c exit (base + 1)))
    (hbody : ∀ (s : State), s.pc = base + 1 → Reaches p s (F s))
    (hbodyPc : ∀ (s : State), (F s).pc = base)
    (hbodyC : ∀ (s : State), (F s).regs c = s.regs c) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs c = n →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs c = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hpc hc
      refine ⟨{ s with pc := exit }, ?_, rfl, hc⟩
      exact Reaches.step s _ _ (by simp only [step, hpc, h0, hc, if_pos]) (Reaches.refl _)
  | succ m ih =>
      intro s hpc hc
      -- Decrement the counter and enter the body.
      have hstep : step p s
          = some { pc := base + 1, regs := fun i => if i = c then m else s.regs i } := by
        simp only [step, hpc, h0, hc, setReg]
        rw [if_neg (by omega)]
        congr 1
      set s1 : State := { pc := base + 1, regs := fun i => if i = c then m else s.regs i }
      have hbodyRun := hbody s1 rfl
      have hpc2 : (F s1).pc = base := hbodyPc s1
      have hc2 : (F s1).regs c = m := by
        rw [hbodyC s1]
        simp only [s1, if_true]
      rcases ih (F s1) hpc2 hc2 with ⟨s', hrest, hexit, hzero⟩
      exact ⟨s', Reaches.step s s1 s' hstep (reaches_trans hbodyRun hrest), hexit, hzero⟩

/-- Copying a register without destroying it: duplicate into the target and
    a scratch, then drain the scratch back. Draining is destructive, so this
    is the only way a register is read more than once. -/
theorem copyBack_reaches (p : Program) (a t sc base mid exit : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (h0 : p[base]? = some (Instruction.jzdec a mid (base + 1)))
    (hi1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (hi2 : p[base + 2]? = some (Instruction.inc sc base))
    (hd0 : p[mid]? = some (Instruction.jzdec sc exit (mid + 1)))
    (hd1 : p[mid + 1]? = some (Instruction.inc a mid)) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n → s.regs sc = 0 →
      Reaches p s (drained sc a exit n (copied a t sc mid n s)) := by
  have hsca : sc ≠ a := fun hc => hasc hc.symm
  have hsct : sc ≠ t := fun hc => htsc hc.symm
  intro n s hpc ha hsc
  have hcopy := copy_reaches p a t sc base mid hat hasc htsc h0 hi1 hi2 n s hpc ha
  have hpc2 : (copied a t sc mid n s).pc = mid := by simp only [copied]
  have hreg2 : (copied a t sc mid n s).regs sc = n := by
    simp only [copied, if_neg hsca, if_neg hsct, if_true, hsc, Nat.zero_add]
  exact reaches_trans hcopy
    (drain_reaches p sc a mid exit hsca hd0 hd1 n _ hpc2 hreg2)

/-- Copy-back stated by its effect rather than by nested state terms: the
    source keeps its value, the target gains it, the scratch stays clear, and
    nothing else moves. -/
theorem copyBack_effect (p : Program) (a t sc base mid exit : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (h0 : p[base]? = some (Instruction.jzdec a mid (base + 1)))
    (hi1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (hi2 : p[base + 2]? = some (Instruction.inc sc base))
    (hd0 : p[mid]? = some (Instruction.jzdec sc exit (mid + 1)))
    (hd1 : p[mid + 1]? = some (Instruction.inc a mid)) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
        s'.regs t = s.regs t + s.regs a ∧ s'.regs sc = 0 ∧
        (∀ r, r ≠ a → r ≠ t → r ≠ sc → s'.regs r = s.regs r) := by
  have hsca : sc ≠ a := fun hc => hasc hc.symm
  have hsct : sc ≠ t := fun hc => htsc hc.symm
  have hta : t ≠ a := fun hc => hat hc.symm
  intro s hpc hsc
  refine ⟨drained sc a exit (s.regs a) (copied a t sc mid (s.regs a) s), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact copyBack_reaches p a t sc base mid exit hat hasc htsc h0 hi1 hi2 hd0 hd1
      (s.regs a) s hpc rfl hsc
  · simp only [drained]
  · simp only [drained, if_neg hasc, if_true, copied, if_true, Nat.zero_add]
  · simp only [drained, if_neg hta, if_neg hat, if_true, copied, if_true, if_neg htsc]
  · simp only [drained, if_true]
  · intro r hra hrt hrsc
    simp only [drained, copied, if_neg hra, if_neg hrt, if_neg hrsc]

/-- Adding two registers into a third: copy each in turn, preserving both. -/
theorem addVar_effect (p : Program) (a b t sc base m1 m2 m3 exit : Nat)
    (hab : a ≠ b) (hat : a ≠ t) (hasc : a ≠ sc)
    (hbt : b ≠ t) (hbsc : b ≠ sc) (htsc : t ≠ sc)
    (ha0 : p[base]? = some (Instruction.jzdec a m1 (base + 1)))
    (ha1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (ha2 : p[base + 2]? = some (Instruction.inc sc base))
    (hr0 : p[m1]? = some (Instruction.jzdec sc m2 (m1 + 1)))
    (hr1 : p[m1 + 1]? = some (Instruction.inc a m1))
    (hb0 : p[m2]? = some (Instruction.jzdec b m3 (m2 + 1)))
    (hb1 : p[m2 + 1]? = some (Instruction.inc t (m2 + 2)))
    (hb2 : p[m2 + 2]? = some (Instruction.inc sc m2))
    (hs0 : p[m3]? = some (Instruction.jzdec sc exit (m3 + 1)))
    (hs1 : p[m3 + 1]? = some (Instruction.inc b m3)) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
        s'.regs b = s.regs b ∧ s'.regs t = s.regs t + s.regs a + s.regs b ∧
        s'.regs sc = 0 := by
  intro s hpc hsc
  rcases copyBack_effect p a t sc base m1 m2 hat hasc htsc ha0 ha1 ha2 hr0 hr1 s hpc hsc with
    ⟨s1, hr1', hpc1, hA1, hT1, hS1, hF1⟩
  rcases copyBack_effect p b t sc m2 m3 exit hbt hbsc htsc hb0 hb1 hb2 hs0 hs1 s1 hpc1 hS1 with
    ⟨s2, hr2', hpc2, hB2, hT2, hS2, hF2⟩
  refine ⟨s2, reaches_trans hr1' hr2', hpc2, ?_, ?_, ?_, hS2⟩
  · rw [hF2 a hab hat hasc, hA1]
  · rw [hB2, hF1 b hab.symm hbt hbsc]
  · rw [hT2, hT1, hF1 b hab.symm hbt hbsc]

/-- Iterating a body that maintains an invariant on the registers other than
    the counter. Indexing the invariant by the iterations remaining lets an
    accumulator grow; requiring it to ignore the counter means decrementing
    the counter cannot disturb it. -/
theorem iterate_inv (p : Program) (c base exit : Nat) (I : Nat → (Nat → Nat) → Prop)
    (hIc : ∀ n f g, (∀ i, i ≠ c → f i = g i) → I n f → I n g)
    (h0 : p[base]? = some (Instruction.jzdec c exit (base + 1)))
    (hbody : ∀ (m : Nat) (s : State), s.pc = base + 1 → s.regs c = m → I (m + 1) s.regs →
      ∃ s', Reaches p s s' ∧ s'.pc = base ∧ s'.regs c = m ∧ I m s'.regs) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs c = n → I n s.regs →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs c = 0 ∧ I 0 s'.regs := by
  intro n
  induction n with
  | zero =>
      intro s hpc hc hI
      exact ⟨{ s with pc := exit }, Reaches.step s _ _
        (by simp only [step, hpc, h0, hc, if_pos]) (Reaches.refl _), rfl, hc, hI⟩
  | succ m ih =>
      intro s hpc hc hI
      have hstep : step p s
          = some { pc := base + 1, regs := fun i => if i = c then m else s.regs i } := by
        simp only [step, hpc, h0, hc, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hI1 : I (m + 1) (fun i => if i = c then m else s.regs i) :=
        hIc _ _ _ (fun i hic => by rw [if_neg hic]) hI
      rcases hbody m { pc := base + 1, regs := fun i => if i = c then m else s.regs i }
        rfl (if_pos rfl) hI1 with ⟨s1, hr1, hpc1, hc1, hI2⟩
      rcases ih s1 hpc1 hc1 hI2 with ⟨s2, hr2, hpc2, hc2, hI3⟩
      exact ⟨s2, Reaches.step s _ _ hstep (reaches_trans hr1 hr2), hpc2, hc2, hI3⟩

end Register

end LeanBF
