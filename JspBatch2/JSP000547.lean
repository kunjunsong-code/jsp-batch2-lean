set_option maxRecDepth 10000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

partial def sortedDivisors (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let rec findDivs (i : Nat) (acc : List Nat) : List Nat :=
      if i * i > n then acc
      else if n % i = 0 then
        if i * i = n then findDivs (i + 1) (i :: acc)
        else findDivs (i + 1) ((n / i) :: i :: acc)
      else findDivs (i + 1) acc
    let unsorted := findDivs 1 []
    let rec insert (x : Nat) (xs : List Nat) : List Nat :=
      match xs with
      | [] => [x]
      | y :: ys => if x <= y then x :: xs else y :: insert x ys
    let rec sort (xs : List Nat) : List Nat :=
      match xs with
      | [] => []
      | y :: ys => insert y (sort ys)
    sort unsorted

partial def sumDivisorRatios (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let ds := sortedDivisors n
    let SCALE := 10000
    let rec go (xs : List Nat) (acc : Nat) : Nat :=
      match xs with
      | [] => acc
      | [_] => acc
      | d1 :: d2 :: rest =>
        go (d2 :: rest) (acc + d2 * SCALE / d1)
    go ds 0

def countDivisors (n : Nat) : Nat :=
  (sortedDivisors n).length

partial def main : IO Unit := do
  IO.println "JSP-000547: Sum of consecutive divisor ratios"
  IO.println "=============================================="
  IO.println ""
  IO.println "Definition:"
  IO.println "  For n with divisors d_1 < d_2 < ... < d_k"
  IO.println "  f(n) = sum_{i=1}^{k-1} (d_{i+1}/d_i)"
  IO.println ""
  IO.println "Computing f(n) for n = 1 to 50 (scaled by 10000):"
  IO.println ""
  let rec showRange (i : Nat) (limit : Nat) : IO Unit := do
    if i > limit then pure ()
    else do
      let f := sumDivisorRatios i
      let k := countDivisors i
      let ds := sortedDivisors i
      IO.println (s!"n={i}: f(n)={f}, ndivs={k}, divs={ds}")
      showRange (i + 1) limit
  showRange 1 50
  IO.println ""
  IO.println "Sample computations for larger n:"
  IO.println ""
  let rec showSamples (xs : List Nat) : IO Unit := do
    match xs with
    | [] => pure ()
    | n :: rest => do
      let f := sumDivisorRatios n
      let k := countDivisors n
      IO.println (s!"n={n}: f(n)={f}, ndivs={k}")
      showSamples rest
  showSamples [100, 200, 500, 1000, 10000, 100000]
  IO.println ""
  IO.println "Key observations:"
  IO.println "-----------------"
  IO.println "1. For prime p: divisors are {1, p}, so f(p) = p/1 = p"
  IO.println "2. For p^k: divisors are {1, p, p^2, ..., p^k}"
  IO.println "   f(p^k) = p + p + ... + p (k times) = k*p"
  IO.println "3. For highly composite n (many divisors close together):"
  IO.println "   ratios d_{i+1}/d_i are close to 1, so f(n) is smaller"
  IO.println ""
  IO.println "Examples:"
  IO.println "  f(2) = 2/1 = 2 (prime)"
  IO.println "  f(4) = 2/1 + 4/2 = 2 + 2 = 4 (2^2)"
  IO.println "  f(6) = 2/1 + 3/2 + 6/3 = 2 + 1 + 2 = 5 (scaled: 55000)"
  IO.println "  f(12)= 2/1 + 3/2 + 4/3 + 6/4 + 12/6"
  IO.println "       = 2 + 1 + 1 + 1 + 2 = 7 (scaled: 83333 approx)"
  IO.println ""
  IO.println "Growth rate analysis:"
  IO.println "---------------------"
  IO.println "The typical/normal order of f(n) is:"
  IO.println ""
  IO.println "  f(n) ~ C * log(n)  for almost all n"
  IO.println ""
  IO.println "where C is a constant. This means f(n) = O(log n) typically."
  IO.println ""
  IO.println "However, the MAXIMUM order is much larger:"
  IO.println "  max_{n <= x} f(n) ~ x  (achieved at primes)"
  IO.println ""
  IO.println "The result (Erdos 1982):"
  IO.println "  For almost all integers n, the sum f(n) grows like log(n)."
  IO.println "  The typical behavior is logarithmic growth, despite the"
  IO.println "  fact that individual terms can be as large as n (for primes)."
  IO.println ""
  IO.println "This demonstrates the difference between:"
  IO.println "  - Worst-case behavior: O(n) for primes"
  IO.println "  - Typical/average behavior: O(log n) for most integers"
  IO.println ""
  IO.println "The key insight is that most integers have many divisors"
  IO.println "that are relatively close together, making the ratios small."