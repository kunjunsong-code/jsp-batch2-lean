set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def repCount (A : List Nat) (n : Nat) : Nat :=
  let pairs := A.flatMap fun a =>
    A.filter (fun b => b >= a) |>.map (fun b => (a, b))
  (pairs.filter (fun (a, b) => a + b == n)).length

def isBasisOfOrder2 (A : List Nat) (N : Nat) : Bool :=
  (List.range' 0 (N + 1)).all (fun n => repCount A n > 0)

def canPartition (A : List Nat) (N : Nat) : Bool :=
  let halves := A.flatMap fun a =>
    A.filter (fun b => b > a) |>.map (fun b => (a, b))
  (List.range' 0 (2 ^ A.length)).any fun mask =>
    let part1 := (List.range' 0 A.length).filter (fun i => (mask / (2 ^ i)) % 2 == 1) |>.map (fun i => A.getD i 0)
    let part2 := (List.range' 0 A.length).filter (fun i => (mask / (2 ^ i)) % 2 == 0) |>.map (fun i => A.getD i 0)
    isBasisOfOrder2 part1 N && isBasisOfOrder2 part2 N

def main : IO Unit := do
  IO.println "JSP-000722: Partition into two order-2 additive bases"
  IO.println ""
  IO.println "Testing small sets for partition into two bases:"
  let testSets := [
    [0, 1, 2, 3],
    [0, 1, 2, 3, 4],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 4, 7],
    [0, 1, 3, 4, 6, 8]
  ]
  testSets.forM fun A => do
    let isB := isBasisOfOrder2 A 8
    let canP := if isB then canPartition A 8 else false
    IO.println s!"  A={A}: isBasis={isB}, canPartition={canP}"
  IO.println ""
  IO.println "Representation counts for A = {0,1,2,3,4}:"
  let A := [0, 1, 2, 3, 4]
  (List.range' 0 9).forM fun n => do
    let rc := repCount A n
    IO.println s!"  r({n}) = {rc}"

#eval main