set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def primesUpTo (limit : Nat) : List Nat :=
  (List.range' 2 (limit - 1)).filter fun n =>
    (List.range' 2 (n - 2)).all fun d => n % d != 0

def sumOfConsec (primes : List Nat) (start len : Nat) : Nat :=
  let sub := (primes.drop start).take len
  sub.foldl (fun acc x => acc + x) 0

def representations (primes : List Nat) (target : Nat) : List (Nat × Nat) :=
  let n := primes.length
  (List.range' 0 n).flatMap fun start =>
    ((List.range' 1 (n - start + 1)).filter fun len =>
      sumOfConsec primes start len == target).map fun len => (start, len)

def main : IO Unit := do
  IO.println "JSP-000296: Representations as sums of consecutive primes"
  IO.println ""
  let primes := primesUpTo 100
  IO.println s!"Primes up to 100: {primes.length} primes"
  IO.println s!"  {primes}"
  IO.println ""
  IO.println "Number of representations of n as sum of consecutive primes:"
  [10, 17, 28, 41, 53, 67, 83, 97, 100, 127, 150, 171, 200].forM fun n => do
    let reps := representations primes n
    IO.println s!"  n={n}: {reps.length} representations"
    reps.forM fun r => do
      let s := sumOfConsec primes r.1 r.2
      IO.println s!"    start={r.1}, len={r.2}: sum={s}"
  IO.println ""
  IO.println "Some numbers have 0, 1, or multiple representations"

#eval main