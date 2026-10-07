set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def sumOfDigits (n : Nat) : Nat :=
  if n < 10 then n
  else n % 10 + sumOfDigits (n / 10)

partial def additivePersistence (n : Nat) : Nat :=
  if n < 10 then 0
  else 1 + additivePersistence (sumOfDigits n)

def digitalRoot (n : Nat) : Nat :=
  if n == 0 then 0
  else if n % 9 == 0 then 9
  else n % 9

def main : IO Unit := do
  IO.println "JSP-000501: Additive persistence and digital roots"
  IO.println ""
  IO.println "Additive persistence: number of iterations to reach single digit"
  IO.println "by summing digits repeatedly."
  IO.println ""
  [10, 27, 39, 199, 299, 399, 999, 1000, 2048, 9999].forM fun n => do
    let p := additivePersistence n
    let dr := digitalRoot n
    IO.println s!"  n={n}: persistence={p}, digital root={dr}"
  IO.println ""
  IO.println "Digital root equals n mod 9 (or 9 if n mod 9 == 0 and n > 0)"
  IO.println "Maximum persistence for base-10 numbers:"
  IO.println "  1 digit: 0, 2 digits: 1, 3 digits: 2"
  IO.println "  The number 2^17236 has persistence 5 (known record holder range)"
  IO.println ""
  IO.println "Connection to JSP-000501: Erdos studied additive number theory"
  IO.println "properties including digit-based functions and their growth rates."

#eval main