set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def repCount (A : List Nat) (n : Nat) : Nat :=
  let pairs := A.flatMap fun a =>
    A.filter (fun b => b >= a) |>.map (fun b => (a, b))
  (pairs.filter (fun (a, b) => a + b == n)).length

def isBasisOfOrder2 (A : List Nat) (N : Nat) : Bool :=
  (List.range' 0 (N + 1)).all (fun n => repCount A n > 0)

def isMinimalBasis (A : List Nat) (N : Nat) : Bool :=
  isBasisOfOrder2 A N &&
  A.all (fun a =>
    let A' := A.filter (fun x => x != a)
    !isBasisOfOrder2 A' N)

def main : IO Unit := do
  IO.println "JSP-000719: Additive basis with growing representation counts"
  IO.println ""
  IO.println "Testing if sets are order-2 additive bases for [0, N]:"
  let testSets := [
    [0, 1, 2, 3, 4, 5],
    [0, 1, 3, 5, 7, 9],
    [0, 1, 2, 4, 7, 11],
    [0, 1, 3, 7, 12, 20]
  ]
  testSets.forM fun A => do
    let isB := isBasisOfOrder2 A 10
    IO.println s!"  A={A}: isBasis[0..10]={isB}"
    if isB then
      let isM := isMinimalBasis A 10
      IO.println s!"    isMinimal={isM}"
  IO.println ""
  IO.println "Representation counts for A = {0,1,3,7}:"
  let A := [0, 1, 3, 7]
  (List.range' 0 15).forM fun n => do
    let rc := repCount A n
    if rc > 0 then
      IO.println s!"  r({n}) = {rc}"

#eval main