set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def divisors (n : Nat) : List Nat :=
  (List.range' 1 n).filter (fun d => n % d == 0)

def divisorDifferences (n : Nat) : List Nat :=
  let ds := divisors n
  let pairs := ds.flatMap fun d1 =>
    ds.filter (fun d2 => d2 > d1) |>.map (fun d2 => d2 - d1)
  pairs

def distinctDivisorDifferences (n : Nat) : List Nat :=
  let diffs := divisorDifferences n
  diffs.foldl (fun acc d => if acc.contains d then acc else acc ++ [d]) []

def consecutiveDivisorDifferences (n : Nat) : List Nat :=
  let ds := divisors n
  (List.range' 0 (ds.length - 1)).map (fun i => ds.getD (i + 1) 0 - ds.getD i 0)

def recipSum (xs : List Nat) : Float :=
  xs.foldl (fun acc x => if x > 0 then acc + 1.0 / x.toFloat else acc) 0.0

def main : IO Unit := do
  IO.println "JSP-000735: Reciprocal sum of distinct vs consecutive divisor differences"
  IO.println ""
  [12, 24, 36, 48, 60, 120, 180, 240, 360, 720, 840, 2520].forM fun n => do
    let dist := distinctDivisorDifferences n
    let cons := consecutiveDivisorDifferences n
    let rsDist := recipSum dist
    let rsCons := recipSum cons
    IO.println s!"  n={n}: distinct={dist}, consec={cons}"
    IO.println s!"    recipSum(distinct)={rsDist}, recipSum(consec)={rsCons}, ratio={rsDist / rsCons}"

#eval main