set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def residueClass (a m N : Nat) : List Nat :=
  let kmax := N / m + 1
  ((List.range' 0 kmax).map fun k => a + k * m).filter fun x => x < N

def areDisjoint (classes : List (Nat × Nat)) : Bool :=
  let n := classes.length
  let idxs := (List.range' 0 n).flatMap fun i =>
    (List.range' (i + 1) (n - i - 1)).map fun j => (i, j)
  idxs.all fun p =>
    let a1 := (classes.getD p.1 (0, 1)).1
    let m1 := (classes.getD p.1 (0, 1)).2
    let a2 := (classes.getD p.2 (0, 1)).1
    let m2 := (classes.getD p.2 (0, 1)).2
    let g := Nat.gcd m1 m2
    (a1 % g) != (a2 % g)

def hasDistinctModuli (classes : List (Nat × Nat)) : Bool :=
  let mods := classes.map fun c => c.2
  let unique := mods.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  unique.length == mods.length

def main : IO Unit := do
  IO.println "JSP-000189: Maximum pairwise disjoint residue classes with distinct moduli"
  IO.println ""
  IO.println "Testing disjointness of residue classes:"
  let test1 : List (Nat × Nat) := [(0, 2), (1, 3), (1, 4)]
  IO.println s!"  (0,2), (1,3), (1,4): disjoint={areDisjoint test1}, distinct moduli={hasDistinctModuli test1}"
  let test2 : List (Nat × Nat) := [(0, 2), (1, 4), (3, 8)]
  IO.println s!"  (0,2), (1,4), (3,8): disjoint={areDisjoint test2}, distinct moduli={hasDistinctModuli test2}"
  IO.println ""
  IO.println "Coverage of disjoint classes in [0, N):"
  let classes1 : List (Nat × Nat) := [(0, 2), (1, 4), (3, 8), (7, 16)]
  IO.println s!"  Classes: {classes1}"
  IO.println s!"  Disjoint: {areDisjoint classes1}"
  IO.println s!"  Distinct moduli: {hasDistinctModuli classes1}"
  let N := 64
  let covered := classes1.flatMap fun c => residueClass c.1 c.2 N
  let unique := covered.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  IO.println s!"  Coverage in [0,{N}): {unique.length}/{N}"
  IO.println ""
  IO.println "Systematic check: how many residue classes mod m are pairwise disjoint?"
  [2, 3, 4, 5, 6, 7, 8, 9, 10].forM fun m => do
    let classes : List (Nat × Nat) := (List.range' 0 m).map fun a => (a, m)
    let disj := areDisjoint classes
    IO.println s!"  mod {m}: {classes.length} classes, pairwise disjoint = {disj}"
  IO.println ""
  IO.println "Erdos-Szemeredy: max disjoint classes with moduli in [2,N] is o(N)"
  IO.println "Ho (2024) resolved the exact bound."

#eval main