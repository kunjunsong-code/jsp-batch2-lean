set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def repCount (A : List Nat) (n : Nat) : Nat :=
  let pairs := A.flatMap fun a =>
    A.filter (fun b => b >= a) |>.map (fun b => (a, b))
  (pairs.filter (fun (a, b) => a + b == n)).length

def schnirelmannDensity (A : List Nat) (N : Nat) : Float :=
  if N == 0 then 0.0
  else
    let count := (List.range' 1 (N + 1)).filter (fun n =>
      (List.range' 0 (n + 1)).any (fun a => A.contains a && A.contains (n - a))
    )
    (count.length.toFloat) / (N.toFloat)

def main : IO Unit := do
  IO.println "JSP-000998: Density of integers with prescribed additive representation counts"
  IO.println ""
  IO.println "Representation counts r_A(n) for A = {0,1,2,3,5,8}:"
  let A := [0, 1, 2, 3, 5, 8]
  (List.range' 0 17).forM fun n => do
    let r := repCount A n
    IO.println s!"  r({n}) = {r}"
  IO.println ""
  IO.println "Checking monotonicity of representation function:"
  let reps := (List.range' 0 17).map (repCount A)
  let isMonotone := (List.range' 1 reps.length).all (fun i =>
    reps.getD i 0 >= reps.getD (i - 1) 0
  )
  IO.println s!"  Representation sequence: {reps}"
  IO.println s!"  Is monotone non-decreasing: {isMonotone}"
  IO.println ""
  IO.println "Schnirelmann density of A:"
  (List.range' 1 17).forM fun N => do
    let d := schnirelmannDensity A N
    IO.println s!"  sigma(A, {N}) = {d}"
  IO.println ""
  IO.println "For a target function f(n)=n, finding sets with r_A(n) close to f(n):"
  let B := List.range' 0 20
  (List.range' 0 30).forM fun n => do
    let r := repCount B n
    IO.println s!"  r_B({n}) = {r}"
  let densB := schnirelmannDensity B 50
  IO.println s!"  Schnirelmann density of B up to 50: {densB}"

#eval main