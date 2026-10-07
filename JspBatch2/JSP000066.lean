set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def schnirelmannDensity (A : List Nat) (N : Nat) : Float :=
  if N == 0 then 0.0
  else
    let counts := (List.range' 1 (N + 1)).filter fun n =>
      (List.range' 0 (n + 1)).any fun a => A.contains a && A.contains (n - a)
    (counts.length.toFloat) / (N.toFloat)

def sumset (A B : List Nat) : List Nat :=
  (A.flatMap fun a => B.map fun b => a + b)

def main : IO Unit := do
  IO.println "JSP-000066: Schnirelmann density and additive non-basis sets"
  IO.println ""
  IO.println "Schnirelmann density of A = {0,1,2,3} up to N:"
  let A := [0, 1, 2, 3]
  (List.range' 1 11).forM fun N => do
    let d := schnirelmannDensity A N
    IO.println s!"  N={N}: density={d}"
  IO.println ""
  IO.println "Schnirelmann density of A+A (sumset):"
  let AA := sumset A A
  let AAuniq := AA.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  (List.range' 1 11).forM fun N => do
    let d := schnirelmannDensity AAuniq N
    IO.println s!"  N={N}: density={d}"
  IO.println ""
  let B := [0, 1, 4, 5]
  IO.println s!"B = {B} is not a basis:"
  (List.range' 1 11).forM fun N => do
    let d := schnirelmannDensity B N
    IO.println s!"  N={N}: density={d}"
  IO.println ""
  IO.println "A + B sumset density:"
  let AB := sumset A B
  let ABuniq := AB.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  (List.range' 1 11).forM fun N => do
    let d := schnirelmannDensity ABuniq N
    IO.println s!"  N={N}: density={d}"

#eval main