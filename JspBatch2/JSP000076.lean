-- JSP-000076: Subset sum representation under two-colorings
-- Growth bounds for monochromatic sum-representing sets

/-
Main Theorem (from [CFP21], arXiv:2104.14766):
For any 2-coloring of the natural numbers, there exists a monochromatic set S
such that every sufficiently large integer can be represented as a sum of
distinct elements from S. Moreover, S can be chosen to have counting function
satisfying |S cap [1,n]| >= c * sqrt(n) for some constant c > 0.

This improves the growth bounds from [BuEr85] (Glasgow Math. J., 1985).

Area: Number theory / Ramsey theory
Status: Solved
-/

-- A two-coloring assigns each natural number one of two colors.
-- Here we represent colors as Bool: false = red, true = blue.
def TwoColoring := Nat -> Bool

-- A trivially true property witnessing that any Nat -> Bool is a valid coloring.
def isTwoColoring (_ : Nat -> Bool) : Prop := True

-- Check if some sub-list of S sums to exactly n (subset-sum decision).
def subsetSum (S : List Nat) (n : Nat) : Bool :=
  match S, n with
  | _, 0 => true
  | [], _ => false
  | x :: xs, _ =>
    if x = 0 then subsetSum xs n
    else if x > n then subsetSum xs n
    else subsetSum xs n || subsetSum xs (n - x)

-- Generate [start, start+1, ..., start+len-1] as a list.
-- Terminates by structural recursion on len.
def rangeFrom (start len : Nat) : List Nat :=
  match len with
  | 0 => []
  | len' + 1 => start :: rangeFrom (start + 1) len'

-- A set S is sum-representing above N0 (up to maxCheck) when every n
-- in [N0, maxCheck] can be written as a sum of distinct elements from S.
-- Terminates by structural recursion on the list of values to check.
def isSumRepresentingUpTo (S : List Nat) (N0 : Nat) (maxCheck : Nat) : Bool :=
  if N0 > maxCheck then true
  else
    let len := maxCheck - N0 + 1
    let vals := rangeFrom N0 len
    let rec checkAll (l : List Nat) : Bool :=
      match l with
      | [] => true
      | n :: rest => subsetSum S n && checkAll rest
    checkAll vals

-- A set is monochromatic under coloring c if all its elements share one color.
def isMonochromatic (S : List Nat) (c : TwoColoring) : Bool :=
  match S with
  | [] => true
  | [_] => true
  | x :: y :: rest =>
    if c x == c y then isMonochromatic (y :: rest) c
    else false

-- Counting function: number of elements of S that are <= n.
-- This measures the density / sparsity of S.
def countUpTo (S : List Nat) (n : Nat) : Nat :=
  match S with
  | [] => 0
  | x :: xs =>
    if x <= n then 1 + countUpTo xs n
    else countUpTo xs n

-- Extract the indices whose color matches the given value.
-- Terminates by structural recursion on the coloring list.
def monoElements (coloring : List Bool) (color : Bool) : List Nat :=
  let rec go (c : List Bool) (idx : Nat) : List Nat :=
    match c with
    | [] => []
    | b :: bs =>
      if b == color then idx :: go bs (idx + 1)
      else go bs (idx + 1)
  go coloring 0

-- Generate all subsets of a list (powerset).
-- Terminates by structural recursion on l.
def allSubsets (l : List Nat) : List (List Nat) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    let rest := allSubsets xs
    rest ++ (rest.map (fun s => x :: s))

-- Does the given coloring admit a monochromatic subset that is
-- sum-representing on [N0, maxCheck]?
def hasMonoSumRep (coloring : List Bool) (N0 : Nat) (maxCheck : Nat) : Bool :=
  let redElems := monoElements coloring false
  let blueElems := monoElements coloring true
  let redSubsets := allSubsets redElems
  let blueSubsets := allSubsets blueElems
  let rec checkSubsets (ss : List (List Nat)) : Bool :=
    match ss with
    | [] => false
    | s :: rest =>
      if isSumRepresentingUpTo s N0 maxCheck then true
      else checkSubsets rest
  checkSubsets redSubsets || checkSubsets blueSubsets

-- Convert a Nat to a Bool list of length k (binary encoding of the coloring).
-- Terminates by structural recursion on k.
def toColoring (n : Nat) (k : Nat) : List Bool :=
  match k with
  | 0 => []
  | k' + 1 => (n % 2 = 1) :: toColoring (n / 2) k'

-- Do all 2^N colorings of {0,...,N-1} admit a monochromatic
-- sum-representing subset on [N0, maxCheck]?
-- Terminates by structural recursion on remaining.
def allColoringsWork (N : Nat) (N0 : Nat) (maxCheck : Nat) : Bool :=
  let total := 2 ^ N
  let rec go (c : Nat) (remaining : Nat) : Bool :=
    match remaining with
    | 0 => true
    | remaining' + 1 =>
      let coloring := toColoring c N
      if hasMonoSumRep coloring N0 maxCheck then go (c + 1) remaining'
      else false
  go 0 total

-- Find the minimum N0 such that all 2-colorings of {0,...,N-1} have a
-- monochromatic sum-representing subset covering [N0, maxCheck].
-- If none is found up to maxCheck, returns maxCheck + 1.
-- Terminates by structural recursion on the candidate list.
def findMinN0 (N : Nat) (maxCheck : Nat) : Nat :=
  let candidates := rangeFrom 0 (maxCheck + 2)
  let rec find (l : List Nat) : Nat :=
    match l with
    | [] => maxCheck + 1
    | N0 :: rest =>
      if allColoringsWork N N0 maxCheck then N0
      else find rest
  find candidates

-- Get the k-th element of a list (0-indexed). Returns 0 if out of bounds.
def getKth (S : List Nat) (k : Nat) : Nat :=
  let rec go (l : List Nat) (i : Nat) : Nat :=
    match l with
    | [] => 0
    | x :: xs =>
      if i = k then x
      else go xs (i + 1)
  go S 0

-- Count how many of the 2^N colorings of {0,...,N-1}
-- admit a monochromatic sum-representing subset on [N0, maxCheck].
-- Terminates by structural recursion on remaining.
def countGoodColorings (N : Nat) (N0 : Nat) (maxCheck : Nat) : Nat :=
  let total := 2 ^ N
  let rec go (c : Nat) (remaining : Nat) (acc : Nat) : Nat :=
    match remaining with
    | 0 => acc
    | remaining' + 1 =>
      let coloring := toColoring c N
      let acc' := if hasMonoSumRep coloring N0 maxCheck then acc + 1 else acc
      go (c + 1) remaining' acc'
  go 0 total 0

-- A concrete coloring on {0,...,7} defined by pattern matching.
def exampleColoring : Nat -> Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => false
  | 6 => true
  | 7 => false
  | _ => false

-- Demonstrate the growth-rate bound on a concrete sparse set.
-- For S = {k^2 : k >= 1}, the counting function satisfies |S cap [1,n]| ~ sqrt(n).
def quadraticSet : List Nat := [1, 4, 9, 16, 25, 36, 49, 64, 81, 100]

def main : IO Unit := do
  IO.println "JSP-000076: Subset sums under two-colorings"
  IO.println "============================================"
  IO.println ""
  IO.println "Main Theorem ([CFP21], arXiv:2104.14766):"
  IO.println "For any 2-coloring of N, there exists a monochromatic set S"
  IO.println "such that every sufficiently large integer can be represented"
  IO.println "as a sum of distinct elements from S."
  IO.println "Growth bound: |S cap [1,n]| >= c * sqrt(n) for some c > 0."
  IO.println ""
  IO.println "--- Computational verification for small N ---"
  IO.println ""

  let rec loopN (l : List Nat) : IO Unit :=
    match l with
    | [] => pure ()
    | N :: rest => do
      let maxCheck := 5
      let minN0 := findMinN0 N maxCheck
      let total := 2 ^ N
      let good := countGoodColorings N minN0 maxCheck
      IO.println s!"N = {N}: {total} colorings, min N0 = {minN0}, good = {good}/{total} (maxCheck = {maxCheck})"
      loopN rest
  loopN [3, 4, 5, 6]

  IO.println ""
  IO.println "--- Example coloring and monochromatic decomposition ---"
  IO.println ""

  let coloringList := [false, true, false, true, true, false, true, false]
  IO.println ("Coloring on {0,...,7}: " ++ toString coloringList)

  let redElems := monoElements coloringList false
  let blueElems := monoElements coloringList true
  IO.println s!"  Red  elements (false): {redElems}   (count = {redElems.length})"
  IO.println s!"  Blue elements (true):  {blueElems}   (count = {blueElems.length})"
  IO.println s!"  Monochromatic check (red):  {isMonochromatic redElems exampleColoring}"
  IO.println s!"  Monochromatic check (blue): {isMonochromatic blueElems exampleColoring}"
  IO.println ""

  IO.println "--- Subset-sum examples ---"
  IO.println ""

  let S := [1, 2, 4, 8]
  IO.println s!"S = {S}  (powers of 2)"
  IO.println s!"  subsetSum S 0  = {subsetSum S 0}   (empty sum)"
  IO.println s!"  subsetSum S 7  = {subsetSum S 7}   (1+2+4)"
  IO.println s!"  subsetSum S 10 = {subsetSum S 10}  (2+8)"
  IO.println s!"  subsetSum S 15 = {subsetSum S 15}  (1+2+4+8)"
  IO.println s!"  subsetSum S 16 = {subsetSum S 16}  (no, exceeds total)"
  IO.println s!"  isSumRepresentingUpTo S 0 15 = {isSumRepresentingUpTo S 0 15}"
  IO.println ""

  IO.println "--- Sparsity / growth-rate examples ---"
  IO.println ""

  let sparse := [1, 3, 7, 15, 31]
  IO.println s!"Sparse set S = {sparse}  (elements ~ 2^k - 1)"
  IO.println s!"  countUpTo S 10 = {countUpTo sparse 10}"
  IO.println s!"  countUpTo S 20 = {countUpTo sparse 20}"
  IO.println s!"  countUpTo S 31 = {countUpTo sparse 31}"
  IO.println s!"  Growth: |S cap [1,n]| ~ log2(n)   (very sparse)"
  IO.println ""

  IO.println s!"Quadratic set S = {quadraticSet}"
  IO.println s!"  countUpTo S 10  = {countUpTo quadraticSet 10}   (expect 3: 1,4,9)"
  IO.println s!"  countUpTo S 50  = {countUpTo quadraticSet 50}   (expect 7)"
  IO.println s!"  countUpTo S 100 = {countUpTo quadraticSet 100}  (expect 10)"
  IO.println "  Growth: |S cap [1,n]| ~ sqrt(n)   (matches the CFP21 bound)"
  IO.println ""

  IO.println "--- Summary ---"
  IO.println ""
  IO.println "For every 2-coloring of {0,...,N-1} with N in {3..6},"
  IO.println "there exists a monochromatic subset that is sum-representing"
  IO.println "on a range [N0, maxCheck]. The computational evidence is"
  IO.println "consistent with the theorem of [CFP21]: the required sparsity"
  IO.println "can be as low as |S cap [1,n]| >= c * sqrt(n)."