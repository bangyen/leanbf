import Mathlib.Data.Nat.Basic

namespace Minsky

/-- A Minsky machine has two counters (c1, c2) -/
structure State where
  pc : Nat
  c1 : Nat
  c2 : Nat
  deriving Repr, Inhabited

/-- Minsky machine instructions -/
inductive Instruction where
  | inc1 (next : Nat) : Instruction
  | inc2 (next : Nat) : Instruction
  | jzdec1 (ifZero : Nat) (ifNonZero : Nat) : Instruction
  | jzdec2 (ifZero : Nat) (ifNonZero : Nat) : Instruction
  | halt : Instruction
  deriving Repr

/-- A Minsky machine program is a list of instructions -/
abbrev Program := List Instruction

def step (p : Program) (s : State) : Option State :=
  match (p : List Instruction)[s.pc]? with
  | none => none
  | some Instruction.halt => none
  | some (Instruction.inc1 next) => some { s with pc := next, c1 := s.c1 + 1 }
  | some (Instruction.inc2 next) => some { s with pc := next, c2 := s.c2 + 1 }
  | some (Instruction.jzdec1 ifZero ifNonZero) =>
    if s.c1 = 0 then
      some { s with pc := ifZero }
    else
      some { s with pc := ifNonZero, c1 := s.c1 - 1 }
  | some (Instruction.jzdec2 ifZero ifNonZero) =>
    if s.c2 = 0 then
      some { s with pc := ifZero }
    else
      some { s with pc := ifNonZero, c2 := s.c2 - 1 }

/-- Reflexive-transitive closure of the Minsky step -/
inductive RunsTo (p : Program) : State → State → Prop where
  | halt (s : State) :
    (p : List Instruction)[s.pc]? = some Instruction.halt ∨
    (p : List Instruction)[s.pc]? = none → RunsTo p s s
  | step (s s' s_final : State) :
    step p s = some s' → RunsTo p s' s_final → RunsTo p s s_final

end Minsky
