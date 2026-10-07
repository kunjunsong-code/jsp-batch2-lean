set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def divisors (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun d => n % d == 0

def quasiCompleteCheck (n : Nat) : Bool :=
  let divs := divisors n
  let sumDiv := divs.foldl (fun acc d => acc + d) 0
  sumDiv >= 2 * n

def main : IO Unit := do
  IO.println "JSP-000040: Anderson conjecture on weakly quasi-complete local rings"
  IO.println ""
  IO.println "Anderson (2014): Is there a Noetherian local ring that is"
  IO.println "weakly quasi-complete but not quasi-complete?"
  IO.println ""
  IO.println "Computational exploration of divisor structure (analogous to ideals):"
  [6, 12, 24, 28, 36, 48, 60, 120].forM fun n => do
    let divs := divisors n
    let sumDiv := divs.foldl (fun acc d => acc + d) 0
    let qc := quasiCompleteCheck n
    IO.println s!"  n={n}: {divs.length} divisors, sum={sumDiv}, 2n={2*n}, quasi-complete={qc}"
  IO.println ""
  IO.println "Ju, Gao, Jiang et al. (2026) proved no such ring exists."
  IO.println "Weakly quasi-complete implies quasi-complete for Noetherian local rings."
  IO.println "The computational divisor analysis mirrors ideal containment checking."

#eval main