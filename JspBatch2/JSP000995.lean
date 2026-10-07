set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isPairwiseDisjoint (mods : List Nat) (ress : List Nat) : Bool :=
  let pairs := mods.flatMap fun m1 =>
    mods.filter (fun m2 => m2 > m1) |>.map (fun m2 => (m1, m2))
  pairs.all fun (m1, m2) =>
    let common := (List.range' 0 (m1 * m2)).filter (fun x => x % m1 == ress.getD 0 0 && x % m2 == ress.getD 1 0)
    common.isEmpty

def reciprocalSum (mods : List Nat) : Float :=
  mods.foldl (fun acc m => acc + 1.0 / m.toFloat) 0.0

def maxReciprocalForDisjoint (maxMod : Nat) (numClasses : Nat) : Float :=
  let mods := (List.range' 2 maxMod)
  let best := mods.foldl (fun (best : Float) m =>
    if 1.0 / m.toFloat + 1.0 / (m + 1).toFloat > best
    then 1.0 / m.toFloat + 1.0 / (m + 1).toFloat
    else best) 0.0
  best

def verifyBound : List (Nat × Float) :=
  (List.range' 2 20).map fun n =>
    (n, reciprocalSum (List.range' 2 (n + 1)))

def main : IO Unit := do
  IO.println "JSP-000995: Max reciprocal sum of moduli with disjoint residue classes"
  IO.println ""
  IO.println "For disjoint residue classes mod m1, m2, ..., need sum 1/m_i <= 1"
  IO.println ""
  IO.println "Reciprocal sums for consecutive moduli 2..n:"
  verifyBound.forM fun (n, s) =>
    IO.println s!"  sum(1/k for k in 2..{n}) = {s}"
  IO.println ""
  IO.println "Key insight: for pairwise disjoint residue classes,"
  IO.println "the sum of reciprocals of moduli cannot exceed 1."
  IO.println "This is because disjoint classes cover at most all integers."
  IO.println ""
  IO.println "Example: mod 2 residue 0, mod 3 residue 1 -> disjoint check"
  let check := (List.range' 0 6).filter (fun x => x % 2 == 0 && x % 3 == 1)
  IO.println s!"  Common elements in [0,5]: {check}"

#eval main