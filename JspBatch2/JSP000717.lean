set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def hasPairwiseSums (S : List Nat) : Bool :=
  S.any fun a =>
    (S.filter (fun b => b > a)).any fun b =>
      (S.filter (fun c => c > b)).any fun c =>
        S.contains (a + b) && S.contains (a + c) && S.contains (b + c)

def density (S : List Nat) : Float :=
  if S.isEmpty then 0.0
  else
    let mx := S.max?.getD 0
    if mx == 0 then 1.0
    else (S.length.toFloat) / (mx + 1).toFloat

def main : IO Unit := do
  IO.println "JSP-000717: Dense sets contain 3 elements with all pairwise sums"
  IO.println ""
  IO.println "Testing sets {1, ..., n} for pairwise sum property:"
  (List.range' 1 15).forM fun n => do
    let S := List.range' 1 (n + 1)
    let has := hasPairwiseSums S
    let dens := (n.toFloat) / (n + 1).toFloat
    IO.println s!"  set 1..{n}: density={dens}, hasPairwiseSums={has}"
  IO.println ""
  IO.println "Testing specific dense subsets:"
  let subsets := [
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    [1, 2, 3, 5, 8, 13],
    [2, 4, 6, 8, 10, 12],
    [1, 3, 5, 7, 9, 11, 13, 15],
    [1, 2, 3, 4, 5, 6, 8, 10, 12]
  ]
  subsets.forM fun S => do
    let has := hasPairwiseSums S
    let d := density S
    IO.println s!"  set: density={d}, hasPairwiseSums={has}"

#eval main