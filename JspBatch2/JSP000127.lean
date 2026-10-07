set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def evalPoly (coeffs : List Float) (x : Float) : Float :=
  coeffs.foldl (fun acc c => acc * x + c) 0.0

def polyFromRoot (root : Float) (prev : List Float) : List Float :=
  let neg_r := -root
  let scaled := prev.map fun c => c * neg_r
  let padded := scaled ++ [0.0]
  let orig := [0.0] ++ prev
  (padded.zip orig).map fun p => p.1 + p.2

def polyFromRoots (roots : List Float) : List Float :=
  roots.foldl (fun acc r => polyFromRoot r acc) [1.0]

def maxModulusOnInterval (coeffs : List Float) (lo hi : Float) (steps : Nat) : Float :=
  let pts := (List.range steps).map fun i =>
    lo + (hi - lo) * (i.toFloat) / ((steps - 1).toFloat)
  let vals := pts.map fun x =>
    let v := evalPoly coeffs x
    if v < 0 then -v else v
  vals.foldl (fun acc v => if v > acc then v else acc) 0.0

def rootsOfUnity (n : Nat) : List Float :=
  (List.range n).map fun k =>
    let theta := 2.0 * 3.14159265358979 * (k.toFloat) / (n.toFloat)
    theta.cos

def main : IO Unit := do
  IO.println "JSP-000127: Polynomial maximum modulus growth with degree"
  IO.println ""
  let results := (List.range' 2 14).map fun n =>
    let roots := rootsOfUnity n
    let coeffs := polyFromRoots roots
    let mx := maxModulusOnInterval coeffs 0.5 2.0 500
    (n, mx)
  IO.println "max|p(x)| on [0.5, 2.0] for polynomials with zeros on unit circle:"
  results.forM fun p =>
    IO.println s!"  n={p.1}: max modulus = {p.2}"
  IO.println ""
  IO.println "Growth ratios max(n)/max(n-1):"
  let vals := results.map fun p => p.2
  let ns := results.map fun p => p.1
  let shifted := vals.drop 1
  let origVals := vals.take (vals.length - 1)
  let ns1 := ns.take (ns.length - 1)
  let ns2 := ns.drop 1
  let triples := (ns1.zip ns2).zip (origVals.zip shifted)
  triples.forM fun t =>
    let n1 := t.1.1
    let n2 := t.1.2
    let mx1 := t.2.1
    let mx2 := t.2.2
    if mx1 > 0 then
      IO.println s!"  n={n1} -> n={n2}: ratio = {mx2 / mx1}"
    else pure ()

#eval main