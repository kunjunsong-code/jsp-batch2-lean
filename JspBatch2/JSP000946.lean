set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else !(List.range' 2 (n - 1)).any (fun d => d * d <= n && n % d == 0)

def checkProp (n : Nat) : Bool :=
  let ks := (List.range' 1 n).filter (fun k => k * k < n)
  ks.all (fun k => Nat.gcd k n != 1 || isPrime (n - k * k))

def search (limit : Nat) : Option Nat :=
  (List.range' 2 limit).find? checkProp

def main : IO Unit := do
  match search 10000 with
  | some n => IO.println s!"Found smallest n = {n}"
  | none => IO.println "No answer found up to 10000"

#eval main

#eval (List.range' 2 20).map (fun n => (n, checkProp n))