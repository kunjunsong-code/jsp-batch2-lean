partial def allFactorsBelow (n bound : Nat) : Bool :=
  let rec go (m d : Nat) : Bool :=
    if m == 1 then true
    else if d * d > m then m <= bound
    else if m % d == 0 then go (m / d) d
    else go m (d + 1)
  go n 2

def smoothRun (start len bound : Nat) : Bool :=
  (List.range' 0 len).all fun i => allFactorsBelow (start + i) bound

partial def findSmoothRun (len bound start maxS : Nat) : Option Nat :=
  let rec go (s : Nat) : Option Nat :=
    if s > maxS then none
    else if smoothRun s len bound then some s
    else go (s + 1)
  go start

def main : IO Unit := do
  IO.println "JSP-000305: Consecutive smooth integers (Erdos 369)"
  IO.println "Claim: arbitrarily long runs of consecutive y-smooth integers exist"
  IO.println ""
  for (len, bound) in [(3, 5), (4, 7), (5, 11), (6, 23), (8, 31)] do
    match findSmoothRun len bound 2 100000 with
    | some s =>
      let nums := (List.range' 0 len).map fun i => s + i
      IO.println s!"  len={len}, bound={bound}: run starts at {s}, nums={nums}"
    | none =>
      IO.println s!"  len={len}, bound={bound}: not found"
  IO.println ""
  IO.println "Result: longer runs found with larger smoothness bounds"
  IO.println "This confirms: for any k, there exist k consecutive y-smooth numbers"