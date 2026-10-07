set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def myFact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFact n

def gcdNat (a b : Nat) : Nat :=
  Nat.gcd a b

def smallPrimeFactorsOnly (n : Nat) (maxPrime : Nat) : Bool :=
  if n <= 1 then true
  else
    let factors := (List.range' 2 n).filter (fun d => n % d == 0)
    factors.all (fun d => d <= maxPrime || !(List.range' 2 d).any (fun k => d % k == 0))

def main : IO Unit := do
  IO.println "JSP-000597: Factorial ratios with small prime factors in denominator"
  IO.println ""
  IO.println "For a!/b!, the reduced denominator's prime factors:"
  (List.range' 1 10).forM fun a => do
    (List.range' 1 (a + 1)).forM fun b => do
      let num := myFact a
      let den := myFact b
      let g := gcdNat num den
      let redDen := den / g
      let hasSmall := smallPrimeFactorsOnly redDen 5
      if hasSmall && redDen > 1 then
        IO.println s!"  {a}!/{b}!, reduced denominator={redDen}, all primes <= 5: true"

#eval main