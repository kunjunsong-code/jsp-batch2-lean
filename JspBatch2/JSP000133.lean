set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else !(List.range' 2 (n - 2)).any fun d => n % d == 0

def primeFactors (n : Nat) : List Nat :=
  if n <= 1 then []
  else
    (List.range' 2 (n - 1)).filter fun d =>
      n % d == 0 && isPrime d

def pairwiseSums (S : List Nat) : List Nat :=
  S.flatMap fun a =>
    (S.filter fun b => b > a).map fun b => a + b

def distinctPrimeFactorsOfProduct (S : List Nat) : List Nat :=
  let sums := pairwiseSums S
  let allFactors := sums.flatMap primeFactors
  allFactors.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def main : IO Unit := do
  IO.println "JSP-000133: Distinct prime factors in product of pairwise sums"
  IO.println ""
  IO.println "Prime factorization check:"
  (List.range' 2 12).forM fun n => do
    let pf := primeFactors n
    IO.println s!"  {n} = {pf}"
  IO.println ""
  IO.println "For various sets S, distinct prime factors of product of pairwise sums:"
  let testSets := [
    [1, 2, 3],
    [1, 2, 3, 4],
    [1, 2, 3, 4, 5],
    [1, 2, 4, 7],
    [1, 2, 4, 8, 16],
    [0, 1, 3, 7, 12],
    [1, 3, 5, 7, 11, 13]
  ]
  testSets.forM fun S => do
    let sums := pairwiseSums S
    let pfs := distinctPrimeFactorsOfProduct S
    IO.println s!"  S={S}"
    IO.println s!"    pairwise sums={sums}"
    IO.println s!"    distinct prime factors={pfs}, count={pfs.length}"
  IO.println ""
  IO.println "Growth with set size:"
  (List.range' 3 12).forM fun n => do
    let S := List.range' 1 (n + 1)
    let pfs := distinctPrimeFactorsOfProduct S
    let numSums := (n * (n - 1)) / 2
    IO.println s!"  n={n}: |sums|={numSums}, distinct prime factors={pfs.length}"

#eval main