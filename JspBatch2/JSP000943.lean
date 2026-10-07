set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else !(List.range' 2 (n - 2)).any fun d => n % d == 0

def primesUpTo (N : Nat) : List Nat :=
  (List.range' 2 (N - 1)).filter isPrime

def nextPrime (n : Nat) : Nat :=
  ((List.range' (n + 1) (2 * n + 2)).filter isPrime).getD 0 0

def primeGap (p : Nat) : Nat :=
  nextPrime (p + 1) - p

def countPrimesInInterval (a b : Nat) : Nat :=
  if b < a then 0
  else ((List.range' a (b - a + 1)).filter isPrime).length

def main : IO Unit := do
  IO.println "JSP-000943: Prime counts in intervals comparable to largest prime gaps"
  IO.println ""
  IO.println "Prime gaps for small primes:"
  let smallPrimes := primesUpTo 50
  smallPrimes.forM fun p => do
    let g := primeGap p
    IO.println s!"  p={p}, gap to next={g}"
  IO.println ""
  IO.println "Counting primes in [p, p+g(p)]:"
  let testPrimes := primesUpTo 100
  testPrimes.forM fun p => do
    let g := primeGap p
    let cnt := countPrimesInInterval p (p + g)
    IO.println s!"  p={p}, gap={g}, primes in [p, p+gap]={cnt}"
  IO.println ""
  IO.println "Ratio of prime count to gap length for larger primes:"
  let bigPrimes := primesUpTo 500
  let sampled := bigPrimes.filter fun p => p >= 50
  sampled.forM fun p => do
    let g := primeGap p
    let cnt := countPrimesInInterval p (p + g)
    let ratio := if g > 0 then (cnt.toFloat) / (g.toFloat) else 0.0
    IO.println s!"  p={p}, gap={g}, count={cnt}, ratio={ratio}"

#eval main