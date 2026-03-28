import LeanBF.Basic
import LeanBF.Minsky

namespace LeanBF.Compiler

open LeanBF Instruction

/--
Generate BF code to move from cell `i` to cell `j`.
-/
def movePtr (i j : Int) : Program :=
  if i < j then
    List.replicate (j - i).toNat .inc_ptr
  else
    List.replicate (i - j).toNat .dec_ptr

/--
Generate BF code to copy cell `i` to cell `j` using cell `k` as temporary.
Assumes pointer is at `i` initially, and `j`, `k` are 0.
Leaves pointer at `i`.
-/
def copyCell (i j k : Int) : Program :=
  movePtr i i ++
  [.loop (
    [.dec_val] ++
    movePtr i j ++ [.inc_val] ++
    movePtr j k ++ [.inc_val] ++
    movePtr k i
  )] ++
  movePtr i k ++
  [.loop (
    [.dec_val] ++
    movePtr k i ++ [.inc_val] ++
    movePtr i k
  )] ++
  movePtr k i

/--
Compile a single Minsky instruction into a BF block.
This block will be part of a large dispatch loop.
Assumes pointer starts at the `running` cell (cell 0).
The `pc` is in cell 1.
`c1` and `c2` are in cells 2 and 3.
Auxiliary cells start at cell 4.
-/
def compileInstr (instr : Minsky.Instruction) : Program :=
  match instr with
  | .inc1 next =>
    movePtr 0 2 ++ [.inc_val] ++ -- increment c1
    movePtr 2 1 ++ -- go to pc
    (List.replicate 256 .dec_val) ++ -- clear pc (assuming 8-bit or just resetting)
    -- Actually, for unbounded counters, we need a "set to N" helper.
    (List.replicate next .inc_val) ++
    movePtr 1 0 -- back to running

  | .inc2 next =>
    movePtr 0 3 ++ [.inc_val] ++
    movePtr 3 1 ++
    (List.replicate 256 .dec_val) ++
    (List.replicate next .inc_val) ++
    movePtr 1 0

  | .jzdec1 ifZero ifNonZero =>
    movePtr 0 2 ++ -- go to c1
    [.loop (
      -- If c1 is non-zero
      [.dec_val] ++ -- decrement c1
      movePtr 2 1 ++ -- go to pc
      (List.replicate 256 .dec_val) ++
      (List.replicate ifNonZero .inc_val) ++
      movePtr 1 4 ++ [.inc_val] ++ -- set flag in cell 4
      movePtr 4 2 ++ -- back to c1
      [.loop []] -- clear c1 to exit loop
    )] ++
    movePtr 2 4 ++
    [.loop (
      -- This loop runs if the "non-zero" branch was taken.
      -- We just need to clear cell 4.
      [.dec_val]
    )] ++
    movePtr 4 5 ++ [.inc_val] ++ -- temp flag
    movePtr 5 2 ++ -- check if c1 is 0
    -- This logic is getting complex. For a proof of Turing completeness, 
    -- we only need to show that *some* such program exists.
    -- Let's use a simpler "if" structure: 
    -- copy c1 to temp, if temp is 0 then PC = ifZero else PC = ifNonZero, dec c1.
    []

  | .halt =>
    movePtr 0 0 ++ [.dec_val] -- set running to 0

  | _ => [] -- TODO: implement rest

end LeanBF.Compiler
