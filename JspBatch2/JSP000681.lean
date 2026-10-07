set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def divisors (n : Nat) : List Nat :=
  (List.range' 1 n).filter (fun d => n % d == 0)

def properDivisors (n : Nat) : List Nat :=
  (divisors n).filter (fun d => d < n)

def divisorSum (n : Nat) : Nat :=
  (divisors n).foldl (fun acc d => acc + d) 0

def properDivisorSum (n : Nat) : Nat :=
  (properDivisors n).foldl (fun acc d => acc + d) 0

def divisorCount (n : Nat) : Nat :=
  (divisors n).length

def canSumToN (n : Nat) : Bool :=
  let ds := properDivisors n
  let target := n
  let sums := ds.foldl (fun (acc : List Nat) d =>
    acc ++ (acc.map (fun s => s + d))) [0]
  sums.contains target

def main : IO Unit := do
  IO.println "JSP-000681: Does large divisor sum => n is sum of some proper divisors?"
  IO.println ""
  IO.println "Checking numbers with sigma(n) > 2n (abundant numbers):"
  (List.range' 2 101).forM fun n => do
    let ds := divisorSum n
    if ds > 2 * n then
      let can := canSumToN n
      IO.println s!"  n={n}, sigma={ds}, sigma/2n={ds.toFloat / (2*n).toFloat}, canSumToN={can}"
  IO.println ""
  IO.println "Threshold check: for which n does sigma(n)/n exceed threshold?"
  [2, 3, 4, 5, 10, 50, 100].forM fun n => do
    let ds := divisorSum n
    let can := canSumToN n
    IO.println s!"  n={n}, sigma(n)={ds}, ratio={ds.toFloat/n.toFloat}, subsetSum={can}"

#eval main