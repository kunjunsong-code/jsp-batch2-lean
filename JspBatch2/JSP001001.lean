set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isPrimitive (S : List Nat) : Bool :=
  S.all fun a => (S.filter fun b => b != a).all fun b => !(a > 0 && b > 0 && (a % b == 0 || b % a == 0))

def reciprocalLogWeight (n : Nat) : Float :=
  if n <= 1 then 0.0 else 1.0 / (n.toFloat * (n.toFloat).log)

def primitiveSetWeight (S : List Nat) : Float :=
  S.foldl (fun acc n => acc + reciprocalLogWeight n) 0.0

def primesUpTo (limit : Nat) : List Nat :=
  (List.range' 2 (limit - 1)).filter fun n =>
    (List.range' 2 (n - 2)).all fun d => n % d != 0

def compositesUpTo (limit : Nat) : List Nat :=
  (List.range' 2 (limit - 1)).filter fun n =>
    (List.range' 2 (n - 1)).any fun d => n % d == 0

def main : IO Unit := do
  IO.println "JSP-001001: Primitive set reciprocal log weight sums"
  IO.println ""
  let primes := primesUpTo 100
  IO.println s!"Primes up to 100: {primes.length} primes"
  let primeWeight := primitiveSetWeight primes
  IO.println s!"Sum of 1/(n*ln(n)) over primes up to 100 = {primeWeight}"
  IO.println ""
  let composites := compositesUpTo 100
  IO.println s!"Composites in [2,100]: {composites.length}"
  let compPrim := composites.filter fun n =>
    (composites.filter fun m => m != n).all fun m => !(m > 0 && n % m == 0)
  IO.println s!"Primitive subset of composites: {compPrim.length} elements"
  let compWeight := primitiveSetWeight compPrim
  IO.println s!"Weight of primitive composites = {compWeight}"
  IO.println ""
  IO.println "Comparison for increasing limits:"
  [10, 20, 50, 100, 200, 500].forM fun N =>
    let p := primesUpTo N
    let pw := primitiveSetWeight p
    IO.println s!"  N={N}: primes={p.length}, weight={pw}"
  IO.println ""
  IO.println "Checking primitive set property:"
  let testSet := [6, 10, 15, 35, 77, 91]
  IO.println s!"  Set {testSet} is primitive: {isPrimitive testSet}"
  let testSet2 := [2, 4, 6, 8, 10]
  IO.println s!"  Set {testSet2} is primitive: {isPrimitive testSet2}"
  IO.println ""
  IO.println "Erdos conjecture: prime sum is maximal among primitive set sums"

#eval main