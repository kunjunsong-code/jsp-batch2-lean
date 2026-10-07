set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def divisors (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun d => n % d == 0

def properDivisors (n : Nat) : List Nat :=
  (List.range' 1 (n - 1)).filter fun d => n % d == 0

def sigma (n : Nat) : Nat :=
  (divisors n).foldl (fun acc d => acc + d) 0

partial def hasSubsetSum (target : Nat) (xs : List Nat) : Bool :=
  if target == 0 then true
  else match xs with
    | [] => false
    | x :: rest =>
      if x > target then hasSubsetSum target rest
      else hasSubsetSum (target - x) rest || hasSubsetSum target rest

def isSemiperfect (n : Nat) : Bool :=
  hasSubsetSum n (properDivisors n)

def isPrimitiveSemiperfect (n : Nat) : Bool :=
  isSemiperfect n && (properDivisors n).all fun d => d > 0 && !(isSemiperfect d)

def main : IO Unit := do
  IO.println "JSP-000381: Primitive semiperfect numbers"
  IO.println ""
  IO.println "Semiperfect numbers up to 100:"
  let semi := (List.range' 1 101).filter fun n => isSemiperfect n
  IO.println s!"  {semi.length} semiperfect numbers"
  IO.println s!"  First 20: {semi.take 20}"
  IO.println ""
  IO.println "Primitive semiperfect numbers up to 500:"
  let primSemi := (List.range' 1 501).filter fun n => isPrimitiveSemiperfect n
  IO.println s!"  {primSemi.length} primitive semiperfect numbers"
  IO.println s!"  {primSemi}"
  IO.println ""
  IO.println "Reciprocal sum of primitive semiperfect numbers:"
  let recSum := primSemi.foldl (fun acc n => acc + 1.0 / n.toFloat) 0.0
  IO.println s!"  Sum of 1/n = {recSum}"
  IO.println ""
  IO.println "Question: does the reciprocal sum converge?"
  IO.println "Lewis (2024) proved the sum converges."

#eval main