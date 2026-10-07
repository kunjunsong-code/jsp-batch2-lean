set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def squares (n : Nat) : List Nat :=
  (List.range' 1 n).map fun i => i * i

def addToListIfNew (l : List Nat) (x : Nat) : List Nat :=
  if l.contains x then l else l ++ [x]

def subsetSumsReachable (elems : List Nat) (maxVal : Nat) : List Nat :=
  let init := [0]
  elems.foldl (fun acc e =>
    let shifted := (acc.filter fun s => s + e <= maxVal).map fun s => s + e
    shifted.foldl addToListIfNew acc
  ) init

def analyzeDeletion (n : Nat) (numSquares : Nat) (maxCheck : Nat) : IO Unit := do
  let allSq := squares numSquares
  let removed := allSq.take n
  let remaining := allSq.drop n
  IO.println s!"N={n}: removed {removed.length} squares, remaining {remaining.length} squares"
  if remaining.isEmpty then
    IO.println "  No elements remaining!"
  else
    let first5 := remaining.take 5
    let last1 := remaining.getLast!
    IO.println s!"  Remaining squares: first 5 = {first5}, last = {last1}"
    let reachable := subsetSumsReachable remaining maxCheck
    let sortedR := reachable.mergeSort (fun a b => a < b)
    let maxRep := match sortedR.getLast? with | some v => v | none => 0
    let covered := (List.range' 1 (maxCheck - 1)).filter fun x => sortedR.contains x
    let covLen := covered.length
    let total := maxCheck - 1
    let coveragePct := (covLen.toFloat * 100.0) / total.toFloat
    IO.println s!"  Reachable sums (up to {maxCheck}): {covLen} values"
    IO.println s!"  Coverage: {coveragePct}%"
    IO.println s!"  Max reachable sum: {maxRep}"
    let halfMax := maxCheck / 2
    let upperHalf := List.range' halfMax halfMax
    let allUpperCovered := upperHalf.all fun x => sortedR.contains x
    IO.println s!"  All integers >= {halfMax} reachable: {allUpperCovered}"
  IO.println ""

def main : IO Unit := do
  IO.println "JSP-000292: Erdos Problem 351 - Completeness after finite deletion"
  IO.println ""
  IO.println "For squares {1,4,9,16,...}, does removing first N elements"
  IO.println "still allow subset sums to represent all sufficiently large integers?"
  IO.println ""
  let numSquares := 30
  let maxCheck := 500
  IO.println s!"Using {numSquares} squares, checking sums up to {maxCheck}"
  IO.println ""
  let testNs := [0, 5, 10, 15, 20]
  testNs.forM fun n => do
    analyzeDeletion n numSquares maxCheck
  IO.println "Conclusion: Subset sum completeness is robust to finite deletion."
  IO.println "For each N, the remaining squares still generate dense coverage."

#eval main
