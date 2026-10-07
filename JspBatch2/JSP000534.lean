set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def dist2 (p1 : Nat × Nat) (p2 : Nat × Nat) : Nat :=
  let dx := if p1.1 >= p2.1 then p1.1 - p2.1 else p2.1 - p1.1
  let dy := if p1.2 >= p2.2 then p1.2 - p2.2 else p2.2 - p1.2
  dx * dx + dy * dy

def distinctDistances (pts : List (Nat × Nat)) : List Nat :=
  let allDists := pts.flatMap fun p1 =>
    (pts.filter fun p2 => p2 != p1).map fun p2 => dist2 p1 p2
  allDists.foldl (fun acc d => if acc.contains d then acc else acc ++ [d]) []

def distinctDistsIn4 (quad : List (Nat × Nat)) : Nat :=
  let subPairs := quad.flatMap fun p1 =>
    (quad.filter fun p2 => p2 != p1).map fun p2 => (p1, p2)
  let ds := subPairs.map fun pair => dist2 pair.1 pair.2
  (ds.foldl (fun acc d => if acc.contains d then acc else acc ++ [d]) []).length

def makeQuads (pts : List (Nat × Nat)) : List (List (Nat × Nat)) :=
  pts.flatMap fun a =>
    (pts.filter fun b => b != a).flatMap fun b =>
      (pts.filter fun c => c != a && c != b).flatMap fun c =>
        (pts.filter fun d => d != a && d != b && d != c).map fun d =>
          [a, b, c, d]

def allQuads3Dists (pts : List (Nat × Nat)) : Bool :=
  let quads := makeQuads pts
  quads.all fun q => distinctDistsIn4 q >= 3

def main : IO Unit := do
  IO.println "JSP-000534: Distinct distances from 4-point condition"
  IO.println ""
  let grid3 : List (Nat × Nat) := (List.range' 0 3).flatMap fun x =>
    (List.range' 0 3).map fun y => (x, y)
  IO.println s!"3x3 grid: {grid3.length} points"
  let dd := distinctDistances grid3
  IO.println s!"  Distinct distances: {dd.length}"
  IO.println s!"  Values: {dd}"
  let ok3 := allQuads3Dists grid3
  IO.println s!"  Every 4 points have >= 3 distances: {ok3}"
  IO.println ""
  let grid4 : List (Nat × Nat) := (List.range' 0 4).flatMap fun x =>
    (List.range' 0 4).map fun y => (x, y)
  IO.println s!"4x4 grid: {grid4.length} points"
  let dd4 := distinctDistances grid4
  IO.println s!"  Distinct distances: {dd4.length}"
  IO.println s!"  Values: {dd4}"
  let ok4 := allQuads3Dists grid4
  IO.println s!"  Every 4 points have >= 3 distances: {ok4}"
  IO.println ""
  let line : List (Nat × Nat) := (List.range' 1 8).map fun x => (x, 0)
  IO.println s!"8 points on a line: {line.length} points"
  let ddL := distinctDistances line
  IO.println s!"  Distinct distances: {ddL.length}"
  IO.println s!"  Values: {ddL}"
  let okL := allQuads3Dists line
  IO.println s!"  Every 4 points have >= 3 distances: {okL}"
  IO.println ""
  let tri : List (Nat × Nat) := (List.range' 0 6).map fun k =>
    (k * 10, k * k * 3)
  IO.println s!"6 triangular-lattice points: {tri.length} points"
  let ddT := distinctDistances tri
  IO.println s!"  Distinct distances: {ddT.length}"

#eval main