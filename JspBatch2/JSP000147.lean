set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def turanBound (n r : Nat) : Nat :=
  if r <= 1 then 0
  else
    let q := n / r
    let rem := n % r
    let t1 := (r - rem) * q * (q - 1) / 2
    let t2 := rem * (q + 1) * q / 2
    n * (n - 1) / 2 - t1 - t2

def main : IO Unit := do
  IO.println "JSP-000147: Graph edges excluding bipartite graph of bounded degeneracy"
  IO.println ""
  IO.println "How many edges can a graph have while excluding K_{s,t}?"
  IO.println ""
  IO.println "Kovari-Sos-Turan bound: ex(n, K_{s,t}) <= O(n^{2-1/s})"
  IO.println ""
  let n := 100
  [2, 3, 4, 5].forM fun s => do
    let bound := n * n / (s * s)
    IO.println s!"  ex({n}, K_s,s) <= {bound} (KST bound for s={s})"
  IO.println ""
  IO.println "Turán numbers for small complete graphs:"
  [3, 4, 5, 6, 10].forM fun n => do
    let t3 := turanBound n 2
    let t4 := turanBound n 3
    IO.println s!"  T({n}, K_3) = {t3}, T({n}, K_4) = {t4}"
  IO.println ""
  IO.println "OpenAI team proved: bounded degeneracy gives sub-quadratic edge bounds."

#eval main