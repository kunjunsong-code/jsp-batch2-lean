set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isSquare (n : Nat) : Bool :=
  let cands := (List.range' 0 (n + 1)).filter (fun x => x * x == n)
  cands.any (fun _ => true)

def hasSquareProductProperty (S : List Nat) : Bool :=
  let quads := S.flatMap fun a =>
    S.filter (fun b => b > a) |>.flatMap fun b =>
    S.filter (fun c => c > b) |>.flatMap fun c =>
    S.filter (fun d => d > c) |>.map fun d => (a, b, c, d)
  quads.all fun (a, b, c, d) =>
    let prod := a * b * c * d
    if isSquare prod then
      (a * b == c * d) || (a * c == b * d) || (a * d == b * c)
    else true

def main : IO Unit := do
  IO.println "JSP-000739: Max set size where square products force cross-product equality"
  IO.println ""
  IO.println "Testing sets of form {1, 2, ..., n}:"
  (List.range' 1 8).forM fun n => do
    let S := List.range' 1 (n + 1)
    let prop := hasSquareProductProperty S
    IO.println s!"  n={n}, property={prop}"
  IO.println ""
  IO.println "Testing specific sets:"
  let testSets := [
    [1, 2, 3, 4],
    [1, 2, 3, 4, 5],
    [1, 2, 3, 6],
    [1, 4, 9, 16],
    [2, 3, 8, 12],
    [1, 2, 8, 16]
  ]
  testSets.forM fun S => do
    let prop := hasSquareProductProperty S
    IO.println s!"  {S}: property={prop}"

#eval main