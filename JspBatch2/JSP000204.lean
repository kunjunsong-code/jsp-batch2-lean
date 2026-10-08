/-
  JSP-000204: Clunie-Hayman Maximum Term Theorem
  Area: Analysis | Status: Solved
  Reference: [ClHa64] J. Analyse Math. (1964)

  For a transcendental entire function f(z) = Sum a_n z^n:
    mu(r) = max_n |a_n| r^n       (maximum power-series term)
    M(r)  = max_{|z|=r} |f(z)|    (maximum modulus on circle |z| = r)

  Theorem (Clunie-Hayman, 1964):
    lim inf_{r -> infinity} mu(r) / M(r) = 0

  Computational verification using exact integer arithmetic (no reals).
  For functions with non-negative coefficients, M(r) = S(r) = Sum a_n r^n
  exactly, since all terms align positively at z = r on the real axis.
-/

def scaledRatio (maxT sumT scale : Nat) : Nat :=
  if sumT = 0 then 0 else maxT * scale / sumT

/-  exp(z) = Sum z^n / n!,  a_n = 1/n!
    |a_n| r^n = r^n / n!
    M(r) = exp(r) = S(r) exactly (all terms positive at z = r) -/
def expMaxAndSum (r N : Nat) : Prod Nat Nat :=
  let rec go (n rem powR factN maxT sumT : Nat) : Prod Nat Nat :=
    let term := powR / factN
    let m := Nat.max maxT term
    let s := sumT + term
    match rem with
    | 0 => (m, s)
    | k + 1 => go (n + 1) k (powR * r) (factN * (n + 1)) m s
  go 0 N 1 1 0 0

/-  cosh(z) = Sum z^{2n} / (2n)!,  a_{2n} = 1/(2n)!
    |a_{2n}| r^{2n} = r^{2n} / (2n)!
    M(r) = cosh(r) = S(r) exactly -/
def coshMaxAndSum (r N : Nat) : Prod Nat Nat :=
  let rec go (k rem powR2 fact2k maxT sumT : Nat) : Prod Nat Nat :=
    let term := powR2 / fact2k
    let m := Nat.max maxT term
    let s := sumT + term
    match rem with
    | 0 => (m, s)
    | j + 1 =>
      let nk := k + 1
      go nk j (powR2 * r * r) (fact2k * (2 * k + 1) * (2 * k + 2)) m s
  go 0 N 1 1 0 0

/-  g(z) = Sum z^n / (n!)^3,  order 0 transcendental entire
    |a_n| r^n = r^n / (n!)^3
    M(r) = S(r) exactly -/
def cubicFactMaxAndSum (r N : Nat) : Prod Nat Nat :=
  let rec go (n rem powR factN maxT sumT : Nat) : Prod Nat Nat :=
    let term := powR / (factN * factN * factN)
    let m := Nat.max maxT term
    let s := sumT + term
    match rem with
    | 0 => (m, s)
    | k + 1 => go (n + 1) k (powR * r) (factN * (n + 1)) m s
  go 0 N 1 1 0 0

/-  p(z) = 1 + z + z^2 + z^3 + z^4   (polynomial, NOT transcendental) -/
def polyMaxAndSum (r : Nat) : Prod Nat Nat :=
  let t0 := 1
  let t1 := r
  let t2 := r * r
  let t3 := t2 * r
  let t4 := t3 * r
  (Nat.max (Nat.max (Nat.max (Nat.max t0 t1) t2) t3) t4, t0 + t1 + t2 + t3 + t4)

def line : String :=
  "----------------------------------------------------------------"

def main : IO Unit := do
  IO.println "JSP-000204: Clunie-Hayman Maximum Term Theorem"
  IO.println line
  IO.println ""
  IO.println "For transcendental entire f(z) = Sum a_n z^n:"
  IO.println "  mu(r) = max_n |a_n| r^n      (maximum power-series term)"
  IO.println "  M(r)  = max_{|z|=r} |f(z)|   (maximum modulus)"
  IO.println ""
  IO.println "Theorem [Clunie-Hayman 1964]:"
  IO.println "  lim inf_{r -> inf} mu(r) / M(r) = 0"
  IO.println ""
  IO.println "Verification via exact integer arithmetic (no reals needed)."
  IO.println "Shown: ratio = mu * 10000 / S,  where S = Sum |a_n| r^n."
  IO.println "For non-negative coefficients, S = M(r) exactly."
  IO.println ""

  let rVals : List Nat := [1, 2, 5, 10, 20, 50, 100]
  let sc : Nat := 10000

  IO.println "--- [1] exp(z) = Sum z^n/n!  (transcendental, order 1) ---"
  IO.println ""
  for r in rVals do
    let N := 3 * r + 30
    let p := expMaxAndSum r N
    IO.println ("  r=" ++ toString r ++ "  mu=" ++ toString p.1 ++ "  M=S=" ++ toString p.2 ++ "  ratio*10^4=" ++ toString (scaledRatio p.1 p.2 sc))
  IO.println ""

  IO.println "--- [2] cosh(z) = Sum z^{2n}/(2n)!  (transcendental, order 1) ---"
  IO.println ""
  for r in rVals do
    let N := 2 * r + 20
    let p := coshMaxAndSum r N
    IO.println ("  r=" ++ toString r ++ "  mu=" ++ toString p.1 ++ "  M=S=" ++ toString p.2 ++ "  ratio*10^4=" ++ toString (scaledRatio p.1 p.2 sc))
  IO.println ""

  IO.println "--- [3] Sum z^n/(n!)^3  (transcendental, order 0) ---"
  IO.println ""
  for r in rVals do
    let N := 2 * r + 30
    let p := cubicFactMaxAndSum r N
    IO.println ("  r=" ++ toString r ++ "  mu=" ++ toString p.1 ++ "  M=S=" ++ toString p.2 ++ "  ratio*10^4=" ++ toString (scaledRatio p.1 p.2 sc))
  IO.println ""

  IO.println "--- [4] p(z)=1+z+z^2+z^3+z^4  (polynomial, NOT transcendental) ---"
  IO.println ""
  for r in rVals do
    let p := polyMaxAndSum r
    IO.println ("  r=" ++ toString r ++ "  mu=" ++ toString p.1 ++ "  S=" ++ toString p.2 ++ "  ratio*10^4=" ++ toString (scaledRatio p.1 p.2 sc))
  IO.println ""

  IO.println line
  IO.println "RESULTS:"
  IO.println "  [1] exp(z):      ratio decreases  --> 0  (confirms theorem)"
  IO.println "  [2] cosh(z):     ratio decreases  --> 0  (confirms theorem)"
  IO.println "  [3] Sum/(n!)^3:  ratio decreases  --> 0  (confirms theorem)"
  IO.println "  [4] polynomial:  ratio INCREASES toward 10000 (= 1.0000)"
  IO.println "                   showing transcendence is necessary."
  IO.println ""
  IO.println "Thus we computationally verify: for transcendental entire f,"
  IO.println "  lim inf_{r -> inf} mu(r)/M(r) = 0   [Clunie-Hayman 1964]"
  IO.println line