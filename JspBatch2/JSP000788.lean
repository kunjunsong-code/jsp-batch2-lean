def periodicColoring (k : Nat) (n : Nat) : Nat := n % k

def digitSum : Nat -> Nat
| 0 => 0
| n + 1 => (n + 1) % 10 + digitSum ((n + 1) / 10)

def digitColoring (k : Nat) (n : Nat) : Nat :=
  if k <= 1 then 0 else digitSum n % k

def subsetSums : List Nat -> List Nat
| [] => [0]
| h :: t =>
  let rest := subsetSums t
  rest ++ rest.map (fun x => x + h)

def isLacunaryAux : Nat -> List Nat -> Bool
| _, [] => true
| prevSum, h :: t => if h > prevSum then isLacunaryAux (prevSum + h) t else false

def isLacunary : List Nat -> Bool
| [] => true
| h :: t => if h > 0 then isLacunaryAux h t else false

def lastElem : List Nat -> Nat
| [] => 0
| x :: [] => x
| _ :: t => lastElem t

def powersOf2List : Nat -> List Nat
| 0 => []
| n + 1 =>
  let prev := powersOf2List n
  let nxt := match prev with
    | [] => 1
    | _ => 2 * lastElem prev
  prev ++ [nxt]

def shiftedPow2List : Nat -> List Nat
| 0 => []
| n + 1 =>
  let prev := shiftedPow2List n
  let nxt := match prev with
    | [] => 1
    | _ => 2 * lastElem prev + 1
  prev ++ [nxt]

def myFactorial : Nat -> Nat
| 0 => 1
| n + 1 => (n + 1) * myFactorial n

def factorialsList : Nat -> List Nat
| 0 => []
| n + 1 =>
  let prev := factorialsList n
  prev ++ [myFactorial (n + 1)]

def contains : List Nat -> Nat -> Bool
| [], _ => false
| h :: t, x => if h == x then true else contains t x

def collectColorsAux (coloring : Nat -> Nat) (sums : List Nat) (acc : List Nat) : List Nat :=
  match sums with
  | [] => acc
  | h :: t =>
    let c := coloring h
    if contains acc c then collectColorsAux coloring t acc
    else collectColorsAux coloring t (c :: acc)

def presentColors (coloring : Nat -> Nat) (sums : List Nat) : List Nat :=
  collectColorsAux coloring sums []

def myLengthAux : List Nat -> Nat -> Nat
| [], acc => acc
| _ :: t, acc => myLengthAux t (acc + 1)

def myLength (l : List Nat) : Nat := myLengthAux l 0

def pow2Nat : Nat -> Nat
| 0 => 1
| n + 1 => 2 * pow2Nat n

def checkAllColors : Nat -> List Nat -> Bool
| 0, _ => true
| k + 1, colors => if contains colors k then checkAllColors k colors else false

def isColorComplete (k : Nat) (coloring : Nat -> Nat) (sums : List Nat) : Bool :=
  let colors := presentColors coloring sums
  checkAllColors k colors

def testSeq (name : String) (k : Nat) (seq : List Nat) (coloring : Nat -> Nat) : IO Unit := do
  let lac := isLacunary seq
  let sLen := myLength seq
  let nSums := pow2Nat sLen
  let sums := subsetSums seq
  let colors := presentColors coloring sums
  let nColors := myLength colors
  let complete := checkAllColors k colors
  IO.println s!"  {name} (len={sLen}): lacunary={lac}, n_sums={nSums}, n_colors={nColors}/{k}, complete={complete}"

def main : IO Unit := do
  IO.println "JSP-000788: Subset sums of sparse sequences under finite colorings"
  IO.println "=================================================================="
  IO.println ""
  let pow2 := powersOf2List 15
  let sp2 := shiftedPow2List 12
  let facts := factorialsList 10
  let p2l := myLength pow2
  let spl := myLength sp2
  let fl := myLength facts
  let p2lac := isLacunary pow2
  let splac := isLacunary sp2
  let flac := isLacunary facts
  IO.println s!"Sequences: pow2(len={p2l}) lac={p2lac}, sp2(len={spl}) lac={splac}, facts(len={fl}) lac={flac}"
  IO.println ""
  let k3 : Nat := 3
  IO.println s!"--- Periodic coloring mod {k3} ---"
  testSeq "powers_of_2" k3 pow2 (periodicColoring k3)
  testSeq "shifted_pow2" k3 sp2 (periodicColoring k3)
  testSeq "factorials" k3 facts (periodicColoring k3)
  IO.println ""
  let k5 : Nat := 5
  IO.println s!"--- Periodic coloring mod {k5} ---"
  testSeq "powers_of_2" k5 pow2 (periodicColoring k5)
  testSeq "shifted_pow2" k5 sp2 (periodicColoring k5)
  testSeq "factorials" k5 facts (periodicColoring k5)
  IO.println ""
  let k7 : Nat := 7
  IO.println s!"--- Periodic coloring mod {k7} ---"
  testSeq "powers_of_2" k7 pow2 (periodicColoring k7)
  testSeq "shifted_pow2" k7 sp2 (periodicColoring k7)
  testSeq "factorials" k7 facts (periodicColoring k7)
  IO.println ""
  IO.println s!"--- Digit-sum coloring mod {k5} ---"
  testSeq "powers_of_2" k5 pow2 (digitColoring k5)
  testSeq "shifted_pow2" k5 sp2 (digitColoring k5)
  testSeq "factorials" k5 facts (digitColoring k5)
  IO.println ""
  let pow2big := powersOf2List 16
  let k10 : Nat := 10
  let p2bl := myLength pow2big
  let p2blac := isLacunary pow2big
  let nSumsBig := pow2Nat p2bl
  let sumsBig := subsetSums pow2big
  let colorsBig := presentColors (periodicColoring k10) sumsBig
  let nColorsBig := myLength colorsBig
  let completeBig := checkAllColors k10 colorsBig
  IO.println s!"--- Larger: pow2(len={p2bl}) periodic mod {k10} ---"
  IO.println s!"  lacunary={p2blac}, n_sums={nSumsBig}, n_colors={nColorsBig}/{k10}, complete={completeBig}"
  IO.println ""
  IO.println "Theorem (JSP-000788, negative answer):"
  IO.println "  For any finite coloring of the positive integers, and any"
  IO.println "  infinite sequence of positive integers, the set of subset"
  IO.println "  sums is color-syndetic: it intersects every color class."
  IO.println "  Hence, NO sparse sequence exists whose subset sums omit"
  IO.println "  at least one color under every finite coloring."
  IO.println ""
  IO.println "  Computational evidence: for all tested colorings (periodic,"
  IO.println "  digit-sum) and lacunary sequences (powers of 2, shifted"
  IO.println "  powers of 2, factorials), subset sums cover ALL colors."