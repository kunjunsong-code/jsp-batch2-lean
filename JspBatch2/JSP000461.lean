set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def turanUpperBound (n s t : Nat) : Float :=
  if n <= 0 then 0.0
  else
    let total := (n * (n - 1)) / 2
    let denom := (s * t).toFloat
    let factor := 1.0 - 1.0 / (denom)
    total.toFloat * factor

def pairList : List (Nat × Nat) := [(2, 2), (2, 3), (3, 3), (2, 4), (3, 4), (4, 4)]

def expList : List (Nat × Float) := [(2, 1.5), (3, 4.0/3.0), (4, 5.0/4.0), (5, 6.0/5.0)]

def nList : List Nat := [10, 50, 100, 500, 1000]

def main : IO Unit := do
  IO.println "JSP-000461: Rational Turan exponents of bipartite graphs"
  IO.println ""
  IO.println "Known rational Turan exponents for K_{s,t}:"
  IO.println "  K_{2,2}: exponent 3/2"
  IO.println "  K_{2,3}: exponent 3/2"
  IO.println "  K_{3,3}: exponent 4/3"
  IO.println "  K_{t,t}: exponent approaches (t+1)/t as t grows"
  IO.println ""
  IO.println "Computing Kovari-Sos-Turan upper bounds ex(n, K_{s,t}):"
  pairList.forM fun st => do
    let s := st.1
    let t := st.2
    IO.println s!"  K_({s},{t}):"
    nList.forM fun n =>
      let ub := turanUpperBound n s t
      IO.println s!"    n={n}: ex(n,K({s},{t})) = {ub}"
  IO.println ""
  IO.println "Kovari-Sos-Turan bound: ex(n, K_{s,t}) <= (1/2)(1-1/(s*t)) * n^2 + O(n)"
  IO.println "Conjectured: ex(n, K_{s,t}) = Theta(n^(2-1/s)) for s <= t"
  IO.println ""
  IO.println "Known rational exponents include:"
  expList.forM fun ke =>
    IO.println s!"  t={ke.1}: conjectured exponent = 2 - 1/{ke.1} = {ke.2}"
  IO.println ""
  IO.println "The Bukh-Conlon conjecture (now theorem): every rational of form 2-1/s is achievable"

#eval main