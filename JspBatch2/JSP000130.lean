set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isCoprime (a b : Nat) : Bool :=
  Nat.gcd a b == 1

def pairwiseCoprime (bases : List Nat) : Bool :=
  let n := bases.length
  let pairs := (List.range' 0 n).flatMap fun i =>
    (List.range' (i + 1) (n - i - 1)).map fun j => (bases.getD i 1, bases.getD j 1)
  pairs.all fun p => isCoprime p.1 p.2

partial def represents (bases : List Nat) (n : Nat) : List (Nat × Nat) :=
  bases.map fun b =>
    let rec go := fun m k =>
      if m % b == 0 then go (m / b) (k + 1)
      else (b, k)
    go n 0

def main : IO Unit := do
  IO.println "JSP-000130: Products of powers of pairwise coprime bases"
  IO.println ""
  IO.println "Can integers be represented as products of powers of pairwise coprime bases?"
  IO.println ""
  let bases1 : List Nat := [2, 3, 5]
  IO.println s!"Bases {[2,3,5]}: pairwise coprime = {pairwiseCoprime bases1}"
  [6, 10, 15, 30, 60, 120].forM fun n => do
    let reps := represents bases1 n
    IO.println s!"  n={n}: {reps}"
  IO.println ""
  let bases2 : List Nat := [3, 5, 7]
  IO.println s!"Bases {[3,5,7]}: pairwise coprime = {pairwiseCoprime bases2}"
  [15, 21, 35, 105].forM fun n => do
    let reps := represents bases2 n
    IO.println s!"  n={n}: {reps}"
  IO.println ""
  IO.println "Sidon-type question: representations with no term dividing another."
  IO.println "Snyder (2026) showed such representations exist for 3+ coprime bases."

#eval main