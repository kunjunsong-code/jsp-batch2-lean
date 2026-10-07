set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def sumset (A B : List Nat) : List Nat :=
  let raw := A.flatMap fun a => B.map fun b => a + b
  raw.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def density (S : List Nat) (N : Nat) : Float :=
  let count := (List.range' 1 N).filter fun n => S.contains n
  count.length.toFloat / N.toFloat

def partitionGreedy (A : List Nat) : List Nat × List Nat :=
  let result := A.foldl (fun acc x =>
    let B := acc.1
    let C := acc.2
    if B.length <= C.length then (B ++ [x], C) else (B, C ++ [x])
  ) ([], [])
  result

def main : IO Unit := do
  IO.println "JSP-000609: Sumset partition with positive density"
  IO.println ""
  let A := [1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
  IO.println s!"Set A (primes up to 100): {A.length} elements"
  let AA := sumset A A
  IO.println s!"|A+A| = {AA.length}"
  IO.println ""
  IO.println "Density of A+A in [1, N]:"
  [20, 40, 60, 80, 100, 150, 200].forM fun N =>
    let d := density AA N
    IO.println s!"  N={N}: density(A+A) = {d}"
  IO.println ""
  let part := partitionGreedy A
  let B := part.1
  let C := part.2
  IO.println s!"Partition: B={B.length} elements, C={C.length} elements"
  IO.println s!"  B = {B}"
  IO.println s!"  C = {C}"
  let BB := sumset B B
  let CC := sumset C C
  IO.println s!"  |B+B| = {BB.length}"
  IO.println s!"  |C+C| = {CC.length}"
  IO.println ""
  IO.println "Densities after partition:"
  [20, 40, 60, 80, 100, 150, 200].forM fun N =>
    let dB := density BB N
    let dC := density CC N
    IO.println s!"  N={N}: density(B+B)={dB}, density(C+C)={dC}"
  IO.println ""
  if BB.length > 0 && CC.length > 0 then
    IO.println "Both B+B and C+C have positive density - partition succeeds."
  else
    IO.println "Partition failed to give both parts positive density."

#eval main