import LeanBF.Basic

namespace LeanBF

/-- A single step of the Brainfuck machine -/
def step (prog : Program) (s : State) : Option (Program × State) :=
  match prog with
  | [] => none
  | instr :: rest =>
    match instr with
    | .inc_ptr => some (rest, s.incPtr)
    | .dec_ptr => some (rest, s.decPtr)
    | .inc_val => some (rest, s.incVal)
    | .dec_val => some (rest, s.decVal)
    | .read    =>
      match s.input with
      | [] => some (rest, { s with tape := fun i ↦ if i = s.ptr then 0 else s.tape i })
      | x :: xs => some (rest, { s with tape := fun i ↦ if i = s.ptr then x else s.tape i, input := xs })
    | .write   => some (rest, { s with output := s.currentVal :: s.output })
    | .loop body =>
      if s.currentVal = 0 then
        some (rest, s)
      else
        -- If current value is not 0, execute body and then the loop again.
        some (body ++ [instr] ++ rest, s)

/-- Reflexive-transitive closure of the step relation -/
inductive RunsTo : (Program × State) → State → Prop where
  | halt (s : State) : RunsTo ([], s) s
  | step (p : Program) (s s' : State) (p' : Program) (s_final : State) :
      step p s = some (p', s') → RunsTo (p', s') s_final → RunsTo (p, s) s_final

end LeanBF
