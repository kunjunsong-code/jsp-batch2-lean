set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def myFact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFact n

def myPow (base exp : Nat) : Nat :=
  (List.range' 0 exp).foldl (fun acc _ => acc * base) 1

def firstPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

def prodFirst (r : Nat) : Nat :=
  (firstPrimes.take r).foldl (fun acc p => acc * p) 1

def checkDivisibility (n a1 a2 r : Nat) : Bool :=
  let lhs := myFact a1 * myFact a2
  let pr := prodFirst r
  let rhs := myFact n * myPow pr n
  rhs % lhs == 0

def findValidTriple (n r : Nat) : Option (Nat × Nat) :=
  let candidates := (List.range' 1 (n + 20)).flatMap fun a1 =>
    (List.range' 1 (n + 20)).map fun a2 => (a1, a2)
  candidates.find? fun (a1, a2) => checkDivisibility n a1 a2 r

def main : IO Unit := do
  IO.println "Factorial product divisibility: a1!*a2! | n!*P_r^n"
  IO.println ""
  let testCases := [
    (1, 3), (2, 7), (3, 12), (5, 20), (10, 30)
  ]
  testCases.forM fun (r, n) => do
    let pr := prodFirst r
    match findValidTriple n r with
    | some (a1, a2) =>
      let lhs := myFact a1 * myFact a2
      let rhs := myFact n * myPow pr n
      IO.println s!"r={r}, n={n}: a1={a1}, a2={a2}, a1+a2={a1+a2}, n+r*ceilLog2(n)={n + r * 4}, div={checkDivisibility n a1 a2 r}"
    | none => IO.println s!"r={r}, n={n}: no triple found"
  IO.println ""
  IO.println "Product of first r primes:"
  (List.range' 0 6).forM fun r =>
    IO.println s!"  P({r}) = {prodFirst r}"
  IO.println ""
  IO.println "Detailed verification for r=1:"
  (List.range' 2 20).forM fun n => do
    let pr := prodFirst 1
    let triple := findValidTriple n 1
    match triple with
    | some (a1, a2) =>
      IO.println s!"  n={n}: a1={a1}, a2={a2}, sum={a1+a2}"
    | none => IO.println s!"  n={n}: no valid pair"

#eval main