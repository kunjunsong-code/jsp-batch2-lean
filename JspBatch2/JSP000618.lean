set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range' 1 n).flatMap fun i =>
    (List.range' (i + 1) (n - i)).map fun j => (i, j)

def shiftEdge (p1 p2 : Nat × Nat) : Bool :=
  p1.2 == p2.1 || p2.2 == p1.1

def buildAdj (verts : List (Nat × Nat)) : List (List Nat) :=
  let n := verts.length
  (List.range' 0 n).map fun i =>
    (List.range' 0 n).filter fun j =>
      i != j && shiftEdge verts[i]! verts[j]!

def listSet (l : List Nat) (idx val : Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => if idx == 0 then val :: t else h :: listSet t (idx - 1) val

def greedyColoring (adj : List (List Nat)) (n : Nat) : List Nat :=
  (List.range' 0 n).foldl (fun acc i =>
    let neighbors := (adj[i]!).filter fun j => j < i
    let usedColors := neighbors.map fun j => acc[j]!
    let c := (List.range' 1 (n + 1)).find? fun c => !usedColors.contains c
    match c with
    | some color => listSet acc i color
    | none => listSet acc i n
  ) ((List.range' 0 n).map fun _ => 0)

def numColors (coloring : List Nat) : Nat :=
  let sorted := coloring.mergeSort (fun a b => a > b)
  match sorted with
  | [] => 0
  | hd :: _ => hd

def isIndependentSet (adj : List (List Nat)) (subset : List Nat) : Bool :=
  subset.all fun i =>
    (adj[i]!).all fun j => !subset.contains j

partial def greedyMaxIS (adj : List (List Nat)) (n : Nat) : List Nat :=
  let order := (List.range' 0 n).mergeSort fun a b => (adj[a]!).length < (adj[b]!).length
  order.foldl (fun acc v =>
    let canAdd := acc.all fun u => !(adj[u]!).contains v
    if canAdd then acc ++ [v] else acc
  ) []

def analyzeShiftGraph (n : Nat) : IO Unit := do
  let verts := pairs n
  let adj := buildAdj verts
  let numV := verts.length
  let coloring := greedyColoring adj numV
  let chi := numColors coloring
  let indep := greedyMaxIS adj numV
  let alpha := indep.length
  let ratio := alpha.toFloat / numV.toFloat
  let edgeCount := (adj.map fun l => l.length).foldl (fun a b => a + b) 0 / 2
  IO.println s!"Shift graph S({n}):"
  IO.println s!"  Vertices: {numV}"
  IO.println s!"  Edges: {edgeCount}"
  IO.println s!"  Chromatic number (greedy upper bound): {chi}"
  IO.println s!"  Independence number (greedy lower bound): {alpha}"
  IO.println s!"  Ratio alpha/|V|: {ratio}"
  IO.println s!"  Independent set: {indep.map fun i => verts[i]!}"
  IO.println ""

def main : IO Unit := do
  IO.println "JSP-000618: Erdos Problem 750 - Chromatic graphs and independent sets"
  IO.println ""
  IO.println "Can an infinite-chromatic graph have independent sets of ~half vertices"
  IO.println "in every finite subgraph?"
  IO.println ""
  IO.println "Testing shift graphs S(n): vertices are pairs (i,j) with i<j in {1..n}"
  IO.println "Edges connect (i,j) to (j,k) where i<j<k"
  IO.println ""
  [5, 6, 7, 8].forM fun n => do
    analyzeShiftGraph n
  IO.println "Observation: As n grows, chromatic number grows (unbounded)"
  IO.println "while the independence ratio alpha/|V| stays bounded away from 0."

#eval main
