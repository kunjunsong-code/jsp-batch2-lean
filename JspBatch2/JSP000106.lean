set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def dist2Nat (p1 : Nat × Nat) (p2 : Nat × Nat) : Nat :=
  let dx := if p1.1 >= p2.1 then p1.1 - p2.1 else p2.1 - p1.1
  let dy := if p1.2 >= p2.2 then p1.2 - p2.2 else p2.2 - p1.2
  dx * dx + dy * dy

def countUnitDistances (pts : List (Nat × Nat)) : Nat :=
  let pairs := pts.flatMap fun p1 =>
    (pts.filter fun p2 => p2 != p1).map fun p2 => (p1, p2)
  let unitPairs := pairs.filter fun p => dist2Nat p.1 p.2 == 1
  unitPairs.length / 2

def countDists (pts : List (Nat × Nat)) : List Nat :=
  let pairs := pts.flatMap fun p1 =>
    (pts.filter fun p2 => p2 != p1).map fun p2 => (p1, p2)
  let ds := pairs.map fun p => dist2Nat p.1 p.2
  ds.foldl (fun acc d => if acc.contains d then acc else acc ++ [d]) []

def gridPoints (n : Nat) : List (Nat × Nat) :=
  (List.range' 0 n).flatMap fun x =>
    (List.range' 0 n).map fun y => (x, y)

def circlePoints (r : Nat) : List (Nat × Nat) :=
  let r2 := r * r
  (List.range' 0 (r + 1)).flatMap fun x =>
    let y2 := r2 - x * x
    ((List.range' 0 (r + 1)).filter fun y => y * y == y2).map fun y => (x, y)

def main : IO Unit := do
  IO.println "JSP-000106: Maximum unit distances among n planar points"
  IO.println ""
  [2, 3, 4, 5, 6, 7, 8].forM fun n => do
    let pts := gridPoints n
    let u := countUnitDistances pts
    IO.println s!"  {n}x{n} grid ({pts.length} pts): unit distances = {u}"
  IO.println ""
  IO.println "Circle lattice points at various radii:"
  [1, 5, 10, 13, 25, 50].forM fun r => do
    let pts := circlePoints r
    IO.println s!"  r={r}: {pts.length} lattice points on circle of radius {r}"
  IO.println ""
  IO.println "Unit distances for small grids:"
  [3, 4, 5, 6].forM fun n => do
    let pts := gridPoints n
    let u := countUnitDistances pts
    let d := countDists pts
    IO.println s!"  n={n}: {pts.length} points, {u} unit distances, {d.length} distinct distances"
  IO.println ""
  IO.println "Known: max unit distances = O(n^{4/3}) by Spencer-Szemeredi-Trotter"

#eval main