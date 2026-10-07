set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def aSeq (n : Nat) : Nat := 2 ^ (2 ^ n)

def term (n : Nat) : Nat := aSeq n * aSeq (n + 1)

def recipTerm (n : Nat) : Float :=
  (1.0 : Float) / (term n : Nat).toFloat

def partialSums (count : Nat) : List (Nat × Float) :=
  let recs := (List.range' 0 count).map recipTerm
  let sums := recs.foldl (fun (acc : List Float) t =>
    let last := acc.getLast?.getD 0.0
    acc ++ [last + t]) [0.0]
  (List.range' 0 count).map fun i => (i, sums.getD (i + 1) 0.0)

def verifyGrowth : List (Nat × Bool) :=
  (List.range' 0 10).map fun n => (n, aSeq n >= 2 ^ (2 ^ n))

def verifyMono : List (Nat × Bool) :=
  (List.range' 0 8).map fun n => (n, aSeq n < aSeq (n + 1))

def firstTerms : List (Nat × Nat × Nat) :=
  (List.range' 0 8).map fun n => (n, aSeq n, term n)

def main : IO Unit := do
  IO.println "Sequence a(n) = 2^(2^n):"
  firstTerms.forM fun (n, a, t) =>
    IO.println s!"  n={n}, a(n)={a}, term(n)={t}"
  IO.println ""
  IO.println "Growth check: a(n) >= 2^(2^n)"
  verifyGrowth.forM fun (n, b) =>
    IO.println s!"  n={n}: {b}"
  IO.println ""
  IO.println "Monotonicity: a(n) < a(n+1)"
  verifyMono.forM fun (n, b) =>
    IO.println s!"  n={n}: {b}"
  IO.println ""
  IO.println "Partial sums of 1/(a(n)*a(n+1)):"
  let ps := partialSums 7
  ps.forM fun (n, s) =>
    IO.println s!"  S({n}) ~ {s}"

#eval main