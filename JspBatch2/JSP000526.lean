set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def multiplesInRange (d lo hi : Nat) : List Nat :=
  (List.range' lo (hi - lo + 1)).filter fun n => n % d == 0

def canMatch (ds : List Nat) (lo hi : Nat) : Bool :=
  let rec go (remaining : List Nat) (used : List Nat) : Bool :=
    match remaining with
    | [] => true
    | d :: rest =>
      let mults := (multiplesInRange d lo hi).filter fun m => !(used.contains m)
      mults.any fun m => go rest (m :: used)
  go ds []

def maxMatchSize (ds : List Nat) (lo hi : Nat) : Nat :=
  let allMults := ds.map fun d => (d, multiplesInRange d lo hi)
  let rec go (remaining : List (Nat × List Nat)) (used : List Nat) (count : Nat) : Nat :=
    match remaining with
    | [] => count
    | (d, ms) :: rest =>
      let avail := ms.filter fun m => !(used.contains m)
      match avail with
      | [] => go rest used count
      | m :: _ => go rest (m :: used) (count + 1)
  go allMults [] 0

def main : IO Unit := do
  IO.println "JSP-000526: Matching integers to distinct multiples in interval"
  IO.println ""
  IO.println "Test: can distinct integers a_1,...,a_k each be matched to distinct multiples in [lo,hi]?"
  IO.println ""
  let tests : List (List Nat × Nat × Nat) := [
    ([2, 3, 5], 1, 30),
    ([2, 3, 5, 7], 1, 50),
    ([3, 5, 7, 11], 10, 100),
    ([2, 3, 5, 7, 11], 1, 100),
    ([4, 6, 9, 10], 10, 80),
    ([2, 5, 8, 13, 21], 1, 200)
  ]
  tests.forM fun t =>
    let ds := t.1
    let lo := t.2.1
    let hi := t.2.2
    let possible := canMatch ds lo hi
    let maxSz := maxMatchSize ds lo hi
    IO.println s!"  ds={ds}, [{lo},{hi}]: canMatch={possible}, maxMatchSize={maxSz}/{ds.length}"
  IO.println ""
  IO.println "For each d, multiples in [lo,hi]:"
  let ds := [2, 3, 5, 7]
  ds.forM fun d =>
    let ms := multiplesInRange d 1 30
    IO.println s!"  d={d}: {ms.length} multiples: {ms.take 10}"

#eval main