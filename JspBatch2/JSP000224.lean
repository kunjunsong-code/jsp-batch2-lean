set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def divisorCount (n : Nat) : Nat :=
  if n == 0 then 0
  else (List.range' 1 n).filter (fun d => n % d == 0) |>.length

def d (n : Nat) : Nat := divisorCount n

def term (n : Nat) : Float :=
  let dn := d n
  let dn1 := d (n + 1)
  if dn * dn1 > 0 then 1.0 / (dn * dn1).toFloat else 0.0

def partialSum (N : Nat) : Float :=
  (List.range' 1 (N + 1)).foldl (fun acc n => acc + term n) 0.0

def main : IO Unit := do
  IO.println "JSP-000224: Reciprocal series with d(n)*d(n+1) denominators"
  IO.println ""
  IO.println "d(n) = number of divisors of n"
  IO.println "Series: sum_{n=1}^{inf} 1/(d(n)*d(n+1))"
  IO.println ""
  IO.println "First terms:"
  (List.range' 1 21).forM fun n => do
    let dn := d n
    IO.println s!"  n={n}, d(n)={dn}, d(n)*d(n+1)={dn * d (n+1)}, term={term n}"
  IO.println ""
  IO.println "Partial sums:"
  [1, 2, 5, 10, 20, 50, 100, 200, 500].forM fun N => do
    let s := partialSum N
    IO.println s!"  S({N}) = {s}"
  IO.println ""
  IO.println "The series diverges since d(n) grows slowly (like O(n^eps))"
  IO.println "so 1/(d(n)*d(n+1)) does not decay fast enough."

#eval main