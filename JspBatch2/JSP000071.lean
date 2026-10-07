set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def hasDistinctPairwiseSums (S : List Nat) : Bool :=
  let pairs := S.flatMap fun a =>
    (S.filter fun b => b > a).map fun b => (a + b, a, b)
  let allSums := pairs.map fun (s, _, _) => s
  let uniqueSums := allSums.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  allSums.length == uniqueSums.length

def diffSet (S : List Nat) : List Nat :=
  let diffs := S.flatMap fun a =>
    S.filter (fun b => a > b) |>.map (fun b => a - b)
  diffs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def disjointDiffs (A B : List Nat) : Bool :=
  let dA := diffSet A
  let dB := diffSet B
  !(dA.any fun d => dB.contains d)

def main : IO Unit := do
  IO.println "JSP-000071: Sets with distinct pairwise sums and disjoint difference sets"
  IO.println ""
  IO.println "Testing sets for distinct pairwise sums property:"
  let testSets := [
    [0, 1, 3, 7],
    [0, 1, 2, 5, 11],
    [0, 1, 3, 8, 17],
    [0, 1, 4, 6],
    [0, 1, 2, 3, 4, 5]
  ]
  testSets.forM fun S => do
    let ok := hasDistinctPairwiseSums S
    IO.println s!"  S={S}: distinctSums={ok}"
  IO.println ""
  IO.println "Testing pairs for disjoint difference sets:"
  let A1 := [0, 1, 3]
  let B1 := [0, 4, 9]
  IO.println s!"  A={A1}, B={B1}: disjointDiffs={disjointDiffs A1 B1}"
  IO.println s!"  diffSet(A)={diffSet A1}"
  IO.println s!"  diffSet(B)={diffSet B1}"
  let A2 := [0, 1, 3, 7]
  let B2 := [0, 2, 8, 18]
  IO.println s!"  A={A2}, B={B2}: disjointDiffs={disjointDiffs A2 B2}"
  IO.println s!"  diffSet(A)={diffSet A2}"
  IO.println s!"  diffSet(B)={diffSet B2}"
  IO.println ""
  IO.println "Searching for max |A|+|B| with distinct sums and disjoint diffs:"
  let base := List.range' 0 10
  let subsets := (List.range' 1 (2 ^ base.length)).map fun mask =>
    (List.range' 0 base.length).filter (fun i => (mask / (2 ^ i)) % 2 == 1) |>.map (fun i => base.getD i 0)
  let validSubsets := subsets.filter fun S => S.length >= 2 && hasDistinctPairwiseSums S
  let result := validSubsets.foldl (fun acc A =>
    validSubsets.foldl (fun acc2 B =>
      if disjointDiffs A B then
        let total := A.length + B.length
        if total > acc2.1 then (total, A, B) else acc2
      else acc2
    ) acc
  ) (0, [], [])
  let (bestSum, bA, bB) := result
  IO.println s!"  Best: A={bA} (|A|={bA.length}), B={bB} (|B|={bB.length}), total={bestSum}"

#eval main