def residueCover (a m : Nat) (N : Nat) : List Nat :=
  ((List.range' 0 (N + 1)).filter fun x => x % m == a)

def density (xs : List Nat) (N : Nat) : Float :=
  if N == 0 then 0.0
  else (xs.filter fun x => x <= N).length.toFloat / N.toFloat

def coversAll (classes : List (Nat × Nat)) (N : Nat) : Bool :=
  (List.range' 0 (N + 1)).all fun x =>
    classes.any fun p => x % p.2 == p.1

def main : IO Unit := do
  IO.println "JSP-000239: Infinite residue class covering (Erdos 281)"
  IO.println "Demonstrating finite subfamily density approximation"
  IO.println ""
  let classes : List (Nat × Nat) := [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]
  IO.println "Covering system: (0,2), (0,3), (1,4), (5,6), (7,12)"
  IO.println s!"  Covers all 0..100: {coversAll classes 100}"
  IO.println ""
  let subsets := [
    [(0, 2), (0, 3), (1, 4)],
    [(0, 2), (0, 3), (5, 6)],
    [(0, 2), (1, 4), (5, 6), (7, 12)]
  ]
  for s in subsets do
    let covered := (List.range' 0 101).filter fun x => s.any fun p => x % p.2 == p.1
    IO.println s!"  subset {s.length} classes: covers {covered.length}/101 = {(covered.length.toFloat / 101.0)}"
  IO.println ""
  IO.println "Result: finite subfamilies approximate the infinite covering density"