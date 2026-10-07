set_option maxRecDepth 10000000
set_option maxHeartbeats 0

partial def extractDigits (n b : Nat) : List Nat :=
  if n == 0 then [0]
  else
    let rec go (x : Nat) (acc : List Nat) : List Nat :=
      if x == 0 then acc
      else go (x / b) ((x % b) :: acc)
    go n []

def hasOnlyDigits01 (n b : Nat) : Bool :=
  (extractDigits n b).all fun d => d <= 1

def setWithDigits01 (limit b : Nat) : List Nat :=
  (List.range' 1 limit).filter fun n => hasOnlyDigits01 n b

def sumset (A B : List Nat) : List Nat :=
  let sums := A.flatMap fun a => B.map fun b => a + b
  sums.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def main : IO Unit := do
  IO.println "JSP-000132: Sumset density of {0,1}-digits in base 3 and base 4"
  IO.println ""
  let limit := 82
  let A := setWithDigits01 limit 3
  let B := setWithDigits01 limit 4
  IO.println s!"Set A (digits 0,1 in base 3, up to {limit}): |A| = {A.length}"
  IO.println s!"  elements: {A}"
  IO.println s!"Set B (digits 0,1 in base 4, up to {limit}): |B| = {B.length}"
  IO.println s!"  elements: {B}"
  IO.println ""
  let S := sumset A B
  IO.println s!"|A + B| = {S.length}"
  IO.println ""
  IO.println "Sumset density in [1, N]:"
  [10, 20, 30, 40, 50, 60, 70, 80].forM fun N =>
    let count := (List.range' 1 N).filter fun n => S.contains n
    let d := count.length.toFloat / (N.toFloat)
    IO.println s!"  N={N}: density = {d}"

#eval main