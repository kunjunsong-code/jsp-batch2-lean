def nextSeed (s : Int) : Int :=
  (s * 1103515245 + 12345) % 2147483648

def signOf (s : Int) : Int :=
  if (s / 65536) % 2 = 0 then 1 else -1

def genCoeffs (seed : Int) : Nat → List Int
  | 0 => []
  | n + 1 =>
    let s := nextSeed seed
    signOf s :: genCoeffs s n

def listRev : List Int → List Int → List Int
  | [], acc => acc
  | h :: t, acc => listRev t (h :: acc)

def hornerFold (a b d : Int) : (Int × Int) → List Int → (Int × Int)
  | acc, [] => acc
  | acc, h :: t => hornerFold a b d (h * d + a * acc.1 - b * acc.2, b * acc.1 + a * acc.2) t

def hornerEval (a b d : Int) : List Int → (Int × Int)
  | [] => (0, 0)
  | coeffs =>
    match listRev coeffs [] with
    | [] => (0, 0)
    | c :: cs => hornerFold a b d (c, 0) cs

def intPow (base : Int) : Nat → Int
  | 0 => 1
  | n + 1 => base * intPow base n

def modSq10k (a b d : Int) (coeffs : List Int) : Int :=
  let (x, y) := hornerEval a b d coeffs
  let raw := x * x + y * y
  match coeffs.length with
  | 0 => 0
  | l + 1 => raw * 10000 / intPow (d * d) l

def evalPts : List (Int × (Int × Int)) :=
  [(1, (0, 1)), (-1, (0, 1)), (0, (1, 1)), (0, (-1, 1)), (3, (4, 5)), (4, (3, 5)), (5, (12, 13))]

def evalAll (pts : List (Int × (Int × Int))) (coeffs : List Int) : List Int :=
  match pts with
  | [] => []
  | p :: rest => modSq10k p.1 p.2.1 p.2.2 coeffs :: evalAll rest coeffs

def minOfList : List Int → Int
  | [] => 0
  | [x] => x
  | h :: t =>
    let m := minOfList t
    if h < m then h else m

def sumOfList : List Int → Int
  | [] => 0
  | h :: t => h + sumOfList t

def listToStrH : List Int → String
  | [] => ""
  | h :: t =>
    match t with
    | [] => toString h
    | _ => toString h ++ ", " ++ listToStrH t

def fmtList (l : List Int) : String :=
  "[" ++ listToStrH l ++ "]"

def natToInt : Nat → Int
  | 0 => 0
  | n + 1 => natToInt n + 1

def runOne (seed : Int) (deg : Nat) : IO Unit := do
  let coeffs := genCoeffs seed (deg + 1)
  let vals := evalAll evalPts coeffs
  let mn := minOfList vals
  let sm := sumOfList vals
  let avg := sm / 7
  let expAvg := natToInt (deg + 1) * 10000
  IO.println ("  n=" ++ toString deg ++ " seed=" ++ toString seed ++
    " | min=" ++ toString mn ++ " | avg=" ++ toString avg ++
    " | E[avg]=" ++ toString expAvg)
  IO.println ("    vals=" ++ fmtList vals)

def experiments : List (Int × Nat) :=
  [(42, 4), (137, 4), (42, 8), (137, 8), (42, 16), (137, 16), (42, 32), (137, 32), (42, 64), (999, 64)]

def runAll : List (Int × Nat) → IO Unit
  | [] => pure ()
  | p :: rest => do
    runOne p.1 p.2
    runAll rest

def main : IO Unit := do
  IO.println "JSP-000421: Minimum modulus of +/-1 polynomials on the unit circle"
  IO.println ""
  IO.println "P(z) = sum_{k=0}^{n} epsilon_k z^k, epsilon_k in {-1, +1}"
  IO.println "Eval at 7 points: z in {1, -1, i, -i, (3+4i)/5, (4+3i)/5, (5+12i)/13}"
  IO.println "Values: floor(|P(z)|^2 * 10000)"
  IO.println ""
  runAll experiments
  IO.println ""
  IO.println "Konyagin (1994), Congrove-Ng (2021): min|P(z)| ~ n^{-1/2+o(1)}"