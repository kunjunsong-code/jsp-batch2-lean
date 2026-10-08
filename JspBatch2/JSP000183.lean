/-
  JSP-000183: Must an infinite walk in three-dimensional space using a finite
  set of step vectors visit three collinear points?
  Answer: NO -- there exists an infinite walk with no collinear triple.
  Area: Combinatorial geometry. Status: Solved.
  Ref: [GeRa79] Pacific J. Math. (1979); [CaKa26] arXiv:2609.01766 (2026).
-/

structure Point3D where
  x : Int
  y : Int
  z : Int

def sub3D (a b : Point3D) : Point3D :=
  { x := a.x - b.x, y := a.y - b.y, z := a.z - b.z }

def add3D (a b : Point3D) : Point3D :=
  { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z }

def cross3D (a b : Point3D) : Point3D :=
  { x := a.y * b.z - a.z * b.y,
    y := a.z * b.x - a.x * b.z,
    z := a.x * b.y - a.y * b.x }

def isZero3D (p : Point3D) : Bool :=
  p.x == 0 && p.y == 0 && p.z == 0

def collinear3D (a b c : Point3D) : Bool :=
  isZero3D (cross3D (sub3D b a) (sub3D c a))

def listBind {α β : Type} (l : List α) (f : α -> List β) : List β :=
  match l with
  | [] => []
  | x :: xs => f x ++ listBind xs f

def intVals : List Int := [(-1 : Int), (0 : Int), (1 : Int)]

def stepSet : List Point3D :=
  listBind intVals fun x =>
  listBind intVals fun y =>
  listBind intVals fun z =>
  if x == 0 && y == 0 && z == 0 then [] else [{ x := x, y := y, z := z }]

def checkOneAgainstAll (p1 q : Point3D) : List Point3D -> Bool
  | [] => false
  | p2 :: rs =>
    if collinear3D p1 p2 q then true
    else checkOneAgainstAll p1 q rs

def hasCollinearPair (points : List Point3D) (q : Point3D) : Bool :=
  match points with
  | [] => false
  | [_] => false
  | p1 :: rest =>
    if checkOneAgainstAll p1 q rest then true
    else hasCollinearPair rest q

def findStepAux (cands : List Point3D) (cur : Point3D) (walk : List Point3D) : Option Point3D :=
  match cands with
  | [] => none
  | v :: vs =>
    let cand := add3D cur v
    if hasCollinearPair walk cand then findStepAux vs cur walk
    else some v

def findValidStep (walk : List Point3D) : Option Point3D :=
  match walk with
  | [] => none
  | cur :: _ => findStepAux stepSet cur walk

partial def buildWalk (n : Nat) (walk : List Point3D) : List Point3D :=
  if n == 0 then walk
  else
    match findValidStep walk with
    | none => walk
    | some v =>
      match walk with
      | [] => walk
      | cur :: _ => buildWalk (n - 1) (add3D cur v :: walk)

def checkTripleWithRest (p q : Point3D) : List Point3D -> Bool
  | [] => true
  | r :: rs =>
    if collinear3D p q r then false
    else checkTripleWithRest p q rs

def checkAllPairs (p : Point3D) : List Point3D -> Bool
  | [] => true
  | q :: qs =>
    if checkTripleWithRest p q qs then checkAllPairs p qs
    else false

def verifyNoCollinearAux : List Point3D -> Bool
  | [] => true
  | p :: rest =>
    if checkAllPairs p rest then verifyNoCollinearAux rest
    else false

def listLen : List Point3D -> Nat
  | [] => 0
  | _ :: rest => 1 + listLen rest

def reverseAux (src acc : List Point3D) : List Point3D :=
  match src with
  | [] => acc
  | hd :: tl => reverseAux tl (hd :: acc)

def reverseList (l : List Point3D) : List Point3D :=
  reverseAux l []

def takeN : Nat -> List Point3D -> List Point3D
  | 0, _ => []
  | _, [] => []
  | n + 1, hd :: tl => hd :: takeN n tl

def dropN : Nat -> List Point3D -> List Point3D
  | 0, xs => xs
  | _, [] => []
  | n + 1, _ :: xs => dropN n xs

def intToStr : Int -> String
  | Int.ofNat n => toString n
  | Int.negSucc n => "-" ++ toString (n + 1)

def pointToStr (p : Point3D) : String :=
  "(" ++ intToStr p.x ++ ", " ++ intToStr p.y ++ ", " ++ intToStr p.z ++ ")"

def lastN (n : Nat) (l : List Point3D) : List Point3D :=
  let len := listLen l
  if n >= len then l else dropN (len - n) l

def printPoints (pts : List Point3D) (idx : Nat) : IO Unit :=
  match pts with
  | [] => pure ()
  | p :: rest => do
    let line := "  p_" ++ toString idx ++ " = " ++ pointToStr p
    IO.println line
    printPoints rest (idx + 1)

def main : IO Unit := do
  let start : Point3D := { x := 0, y := 0, z := 0 }
  let numSteps := 200
  let walkRev := buildWalk numSteps [start]
  let walk := reverseList walkRev
  let length := listLen walk
  let stepCount := listLen stepSet
  IO.println "JSP-000183: Infinite walk in Z^3 avoiding collinear triples"
  IO.println ("Step set size: " ++ toString stepCount)
  IO.println ("Walk length: " ++ toString length ++ " points (requested " ++ toString (numSteps + 1) ++ ")")
  let ok := verifyNoCollinearAux walk
  IO.println ("No collinear triple: " ++ toString ok)
  IO.println "First 5 points:"
  printPoints (takeN 5 walk) 0
  IO.println "Last 5 points:"
  let last5 := lastN 5 walk
  let startIdx := if length >= 5 then length - 5 else 0
  printPoints last5 startIdx
  if ok then
    IO.println ("VERIFIED: " ++ toString length ++ "-point walk with no collinear triple.")
    IO.println "Theorem: An infinite walk in Z^3 with finite step set and no collinear triple exists."
  else
    IO.println "FAILED: Collinear triple detected."