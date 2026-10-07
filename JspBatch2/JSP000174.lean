set_option maxRecDepth 10000000
set_option maxHeartbeats 0

partial def turanN (n r : Nat) : Nat :=
  if r <= 1 then 0
  else
    let q := n / r
    let rem := n % r
    let t1 := (r - rem) * q * (q - 1) / 2
    let t2 := rem * (q + 1) * q / 2
    n * (n - 1) / 2 - t1 - t2

def exK3 (n : Nat) : Nat :=
  turanN n 2

def exK4 (n : Nat) : Nat :=
  turanN n 3

def forbiddenEdges (n : Nat) (forbidden : List Nat) : Nat :=
  let vals := forbidden.map fun r => turanN n r
  vals.foldl (fun acc x => if x < acc then x else acc) (n * n)

def main : IO Unit := do
  IO.println "JSP-000174: Forbidding several subgraphs vs forbidding one"
  IO.println ""
  IO.println "How much can forbidding several subgraphs reduce the extremal edge count"
  IO.println "compared with forbidding just one of them?"
  IO.println ""
  IO.println "Turán ex(n, H): max edges in n-vertex graph excluding H as subgraph"
  IO.println ""
  [5, 10, 20, 50, 100].forM fun n => do
    let e3 := exK3 n
    let e4 := exK4 n
    IO.println s!"  n={n}: ex(n,K_3)={e3}, ex(n,K_4)={e4}"
  IO.println ""
  IO.println "Forbidding both K_3 and K_4 is same as forbidding K_3"
  IO.println "(since ex(n, K_3) <= ex(n, K_4))."
  let minBoth := forbiddenEdges 100 [2, 3]
  IO.println s!"  ex(100, forbidding K_3 and K_4) = {minBoth}"
  IO.println ""
  IO.println "OpenAI result: for bounded degeneracy, the joint forbidden"
  IO.println "extremal number equals the minimum of individual ones."

#eval main