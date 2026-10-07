set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def sumset (s : List Nat) : List Nat :=
  let all := s.flatMap fun a => s.map fun b => a + b
  all.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def hasDistinctPairwiseSums (s : List Nat) : Bool :=
  let pairs := s.flatMap fun a =>
    (s.filter fun b => b >= a).map fun b => (a, b)
  let sums := pairs.map fun p => p.1 + p.2
  sums.length == (sums.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).length

def isolatedInSumset (s : List Nat) : List Nat :=
  let ss := sumset s
  ss.filter fun x => !ss.contains (x - 1) && !ss.contains (x + 1)

def main : IO Unit := do
  IO.println "JSP-000151: Sumset elements with distinct pairwise sums (Sidon sets)"
  IO.println ""
  IO.println "For a set A with distinct pairwise sums, how many elements of A+A"
  IO.println "have neither neighbor in A+A?"
  IO.println ""
  let s1 : List Nat := [1, 2, 4, 8]
  IO.println s!"Set {[1,2,4,8]}: distinct pairwise sums = {hasDistinctPairwiseSums s1}"
  let ss1 := sumset s1
  IO.println s!"  Sumset: {ss1}"
  let iso1 := isolatedInSumset s1
  IO.println s!"  Isolated elements: {iso1}"
  IO.println ""
  let s2 : List Nat := [0, 1, 3, 7, 12, 20]
  IO.println s!"Set {[0,1,3,7,12,20]}: distinct pairwise sums = {hasDistinctPairwiseSums s2}"
  let ss2 := sumset s2
  IO.println s!"  Sumset size: {ss2.length}"
  let iso2 := isolatedInSumset s2
  IO.println s!"  Isolated elements: {iso2}"
  IO.println ""
  IO.println "Sidon sets: all pairwise sums are distinct"
  IO.println "Greedy Sidon sets grow like sqrt(n)"

#eval main