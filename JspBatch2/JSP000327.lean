set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def centralBinom (n : Nat) : Nat :=
  factorial (2 * n) / (factorial n * factorial n)

def main : IO Unit := do
  IO.println "JSP-000327: Equalities between products of central binomial coefficients"
  IO.println ""
  IO.println "Central binomial coefficients C(2n,n) for n=1..20:"
  (List.range' 1 21).forM fun n =>
    IO.println s!"  n={n}: C(2n,n) = {centralBinom n}"
  IO.println ""
  let nats := List.range' 1 21
  IO.println "Checking for equal C(2a,a) = C(2b,b) with a < b:"
  let eqPairs := nats.flatMap fun a =>
    let bs := (List.range' (a + 1) (21 - a)).filter fun b => centralBinom a == centralBinom b
    bs.map fun b => (a, b)
  if eqPairs.isEmpty then
    IO.println "  No equal central binomial coefficients found (all distinct)."
  else
    eqPairs.forM fun p =>
      IO.println s!"  C(2*{p.1},{p.1}) = C(2*{p.2},{p.2}) = {centralBinom p.1}"
  IO.println ""
  IO.println "Products C(2a,a)*C(2b,b) for a < b in [1,20]:"
  let allPairs := nats.flatMap fun a =>
    (List.range' (a + 1) (21 - a)).map fun b => (a, b)
  let triples := allPairs.map fun p => (p.1, p.2, centralBinom p.1 * centralBinom p.2)
  triples.forM fun t =>
    IO.println s!"  C(2*{t.1},{t.1}) * C(2*{t.2},{t.2}) = {t.2.2}"
  let allProds := triples.map fun t => t.2.2
  let uniqueProds := allProds.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  IO.println ""
  IO.println s!"  Unique products: {uniqueProds.length} out of {allProds.length} total"
  if uniqueProds.length < allProds.length then
    IO.println "  Found product equalities!"
  else
    IO.println "  All products are distinct."

#eval main