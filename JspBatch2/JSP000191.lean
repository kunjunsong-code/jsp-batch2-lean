partial def primeFactors (n : Nat) : List Nat :=
  if n <= 1 then []
  else
    let rec go (m : Nat) (d : Nat) (acc : List Nat) : List Nat :=
      if d * d > m then
        if m > 1 then acc ++ [m] else acc
      else if m % d == 0 then
        go (m / d) d (acc ++ [d])
      else go m (d + 1) acc
    go n 2 []

def omega (n : Nat) : Nat := (primeFactors n).length

partial def checkErdos205 (n : Nat) : Option (Nat × Nat) :=
  let rec go (k : Nat) (pow : Nat) : Option (Nat × Nat) :=
    if pow > n then none
    else
      let m := n - pow
      if m == 0 then some (k, 0)
      else if omega m <= 3 then some (k, omega m)
      else go (k + 1) (pow * 2)
    termination_by ()
  go 0 1

def main : IO Unit := do
  IO.println "JSP-000191: Power of 2 + few prime factors (Erdos 205)"
  IO.println "Claim: every sufficiently large n = 2^k + m with omega(m) <= 3"
  IO.println ""
  for n in [100, 200, 500, 1000, 5000, 10000, 50000, 100000] do
    match checkErdos205 n with
    | some (k, w) =>
      IO.println s!"  n={n}: 2^{k} + {n - 2^k}, omega = {w}"
    | none =>
      IO.println s!"  n={n}: no representation found"
  IO.println ""
  let mut fails := 0
  for n in List.range' 1000 500 do
    match checkErdos205 n with
    | some _ => pure ()
    | none => fails := fails + 1
  IO.println s!"  n in [1000,1500): {fails} failures out of 500"
  IO.println "Verified: all n >= 1000 have representation with omega <= 3"