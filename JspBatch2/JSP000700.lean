set_option maxRecDepth 10000000
set_option maxHeartbeats 0

abbrev Point := Int × Int

def collinear (p1 p2 p3 : Point) : Bool :=
  let dx1 := p2.1 - p1.1
  let dy1 := p2.2 - p1.2
  let dx2 := p3.1 - p1.1
  let dy2 := p3.2 - p1.2
  dx1 * dy2 - dx2 * dy1 == 0

def hasCollinearTriple (pts : List Point) : Bool :=
  let n := pts.length
  (List.range' 0 n).any fun i =>
    (List.range' (i + 1) (n - i - 1)).any fun j =>
      (List.range' (j + 1) (n - j - 1)).any fun k =>
        collinear pts[i]! pts[j]! pts[k]!

def isGPSet (pts : List Point) : Bool :=
  !hasCollinearTriple pts

def maxGPSubsetGreedy (pts : List Point) : List Point :=
  pts.foldl (fun acc p =>
    let test := acc ++ [p]
    if isGPSet test then test else acc
  ) []

partial def partitionAux (remaining : List Point) (acc : List (List Point)) : List (List Point) :=
  if remaining.isEmpty then acc
  else
    let gp := maxGPSubsetGreedy remaining
    let newRemaining := remaining.filter fun p => !gp.contains p
    partitionAux newRemaining (acc ++ [gp])

def partitionIntoGPSets (pts : List Point) : List (List Point) :=
  partitionAux pts []

def gridPoints (size : Nat) : List Point :=
  (List.range' 0 size).flatMap fun x =>
    (List.range' 0 size).map fun y => (Int.ofNat x, Int.ofNat y)

partial def pseudoRandomAux (s : Nat) (count : Nat) (acc : List Point) : List Point :=
  if count == 0 then acc
  else
    let s1 := (s * 1103515245 + 12345) % (2 ^ 31)
    let x := Int.ofNat (s1 % 50)
    let s2 := (s1 * 1103515245 + 12345) % (2 ^ 31)
    let y := Int.ofNat (s2 % 50)
    pseudoRandomAux s2 (count - 1) (acc ++ [(x, y)])

def pseudoRandomPoints (seed : Nat) (count : Nat) : List Point :=
  pseudoRandomAux seed count []

def printGPSets (sets : List (List Point)) (idx : Nat) : IO Unit := do
  match sets with
  | [] => pure ()
  | s :: rest => do
    IO.println s!"    Set {idx + 1}: {s.length} points"
    printGPSets rest (idx + 1)

def analyzePointSet (name : String) (pts : List Point) : IO Unit := do
  let n := pts.length
  let gp := maxGPSubsetGreedy pts
  let gpLen := gp.length
  let gpRatio := gpLen.toFloat / n.toFloat
  let partition := partitionIntoGPSets pts
  IO.println s!"{name}: {n} points"
  IO.println s!"  Max GP subset (greedy): {gpLen} points, ratio = {gpRatio}"
  IO.println s!"  Partition into GP sets: {partition.length} sets"
  printGPSets partition 0
  IO.println ""

def main : IO Unit := do
  IO.println "JSP-000700: Erdos Problem 846 - General position partitioning"
  IO.println ""
  IO.println "If every finite part of a planar set has a fixed proportion in"
  IO.println "general position (no 3 collinear), can the whole set be"
  IO.println "partitioned into finitely many GP sets?"
  IO.println ""
  IO.println "Testing on various point configurations:"
  IO.println ""
  let grid3 := gridPoints 3
  analyzePointSet "3x3 Grid" grid3
  let grid4 := gridPoints 4
  analyzePointSet "4x4 Grid" grid4
  let grid5 := gridPoints 5
  analyzePointSet "5x5 Grid" grid5
  let rand1 := pseudoRandomPoints 42 20
  analyzePointSet "Random 20 points" rand1
  let rand2 := pseudoRandomPoints 123 30
  analyzePointSet "Random 30 points" rand2
  IO.println "Observation: Every finite planar set can be partitioned into"
  IO.println "finitely many GP sets. The GP density ratio varies by configuration."

#eval main
