/-
  JSP-000314: Largest Prime Factor Repetition in Consecutive Integer Products
  Reference: Ta26c, arXiv:2603.27990 (2026)
-/

partial def largestPrimeFactor (n : Nat) : Nat :=
  if n <= 1 then 1
  else
    let rec go (m d maxP : Nat) : Nat :=
      if d * d > m then
        if m > 1 then Nat.max m maxP else maxP
      else if m % d = 0 then
        go (m / d) d d
      else
        go m (d + 1) maxP
    go n 2 1

partial def prodConsecutive (n k : Nat) : Nat :=
  if k = 0 then 1
  else
    let rec go (i rem acc : Nat) : Nat :=
      if rem = 0 then acc
      else go (i + 1) (rem - 1) (acc * i)
    go n k 1

def hasRepeatingLPF (n k : Nat) : Bool :=
  let p1 := prodConsecutive n k
  let p2 := prodConsecutive (n + 1) k
  let lpf1 := largestPrimeFactor p1
  let lpf2 := largestPrimeFactor p2
  lpf1 = lpf2 && lpf1 > 1

partial def checkRange (k n N count : Nat) : Nat :=
  if n > N then count
  else
    let newCount := if hasRepeatingLPF n k then count + 1 else count
    checkRange k (n + 1) N newCount

def countRepeatingLPF (k N : Nat) : Nat :=
  checkRange k 1 N 0

def testKValue (k N : Nat) : IO Unit := do
  let count := countRepeatingLPF k N
  IO.println s!"  k={k}, N={N}: count={count}, density~={count}/{N}"

def main : IO Unit := do
  IO.println "JSP-000314: Largest Prime Factor Repetition in Consecutive Products"
  IO.println ""
  IO.println "Testing how often P(n,k) and P(n+1,k) share the same largest prime factor"
  IO.println "where P(n,k) = n(n+1)...(n+k-1)"
  IO.println ""

  let N := 200
  IO.println "Results for various k values (N=200):"
  IO.println (s!"  k=2, count=" ++ toString (countRepeatingLPF 2 N))
  IO.println (s!"  k=3, count=" ++ toString (countRepeatingLPF 3 N))
  IO.println (s!"  k=4, count=" ++ toString (countRepeatingLPF 4 N))
  IO.println (s!"  k=5, count=" ++ toString (countRepeatingLPF 5 N))
  IO.println (s!"  k=6, count=" ++ toString (countRepeatingLPF 6 N))
  IO.println (s!"  k=7, count=" ++ toString (countRepeatingLPF 7 N))
  IO.println (s!"  k=8, count=" ++ toString (countRepeatingLPF 8 N))

  IO.println ""
  IO.println "Sample computations for k=3:"
  let p1_1 := prodConsecutive 1 3
  let p2_1 := prodConsecutive 2 3
  let lpf1_1 := largestPrimeFactor p1_1
  let lpf2_1 := largestPrimeFactor p2_1
  IO.println (s!"  n=1: P(1,3)=" ++ toString p1_1 ++ ", P(2,3)=" ++ toString p2_1 ++ ", LPF=" ++ toString lpf1_1 ++ " vs " ++ toString lpf2_1)

  let p1_2 := prodConsecutive 2 3
  let p2_2 := prodConsecutive 3 3
  let lpf1_2 := largestPrimeFactor p1_2
  let lpf2_2 := largestPrimeFactor p2_2
  IO.println (s!"  n=2: P(2,3)=" ++ toString p1_2 ++ ", P(3,3)=" ++ toString p2_2 ++ ", LPF=" ++ toString lpf1_2 ++ " vs " ++ toString lpf2_2)

  let p1_3 := prodConsecutive 3 3
  let p2_3 := prodConsecutive 4 3
  let lpf1_3 := largestPrimeFactor p1_3
  let lpf2_3 := largestPrimeFactor p2_3
  IO.println (s!"  n=3: P(3,3)=" ++ toString p1_3 ++ ", P(4,3)=" ++ toString p2_3 ++ ", LPF=" ++ toString lpf1_3 ++ " vs " ++ toString lpf2_3)

  IO.println ""
  IO.println "Main Theorem (Ta26c, arXiv:2603.27990):"
  IO.println "  For fixed k >= 2, the density of starting points n where"
  IO.println "  P(n,k) and P(n+1,k) share the same largest prime factor"
  IO.println "  is positive and equals a constant c_k expressible via"
  IO.println "  harmonic sum differences and prime distribution."
  IO.println ""
  IO.println "  As k grows, c_k decreases but remains strictly positive."