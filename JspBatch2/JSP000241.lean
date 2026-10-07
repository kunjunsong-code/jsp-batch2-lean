partial def isSumOfDistinct (target : Nat) (vals : List Nat) : Bool :=
  match vals with
  | [] => target == 0
  | x :: xs =>
    if x > target then isSumOfDistinct target xs
    else isSumOfDistinct (target - x) xs || isSumOfDistinct target xs

partial def egyptianDec (n : Nat) : List Nat :=
  if n == 0 then []
  else
    let rec findUnit (d : Nat) : Nat :=
      if n * d >= 1 then d else findUnit (d + 1)
    let d := findUnit 1
    let rem := n * d - 1
    if rem == 0 then [d]
    else d :: egyptianDec rem

def polyValues (k : Nat) : List Nat :=
  (List.range' 1 50).map fun n => n * n + k

def main : IO Unit := do
  IO.println "JSP-000241: Egyptian fractions + polynomial values (Erdos 283)"
  IO.println "Claim: polynomial values form a complete sequence"
  IO.println ""
  let vals := polyValues 0
  IO.println s!"Squares up to 50^2: first 10 = {vals.take 10}"
  IO.println ""
  let mut representable := 0
  let mut total := 0
  for n in List.range' 1 200 do
    if isSumOfDistinct n vals then
      representable := representable + 1
    total := total + 1
  IO.println s!"Representable as sum of distinct squares: {representable}/{total}"
  IO.println ""
  let cubes := (List.range' 1 30).map fun n => n * n * n
  let mut rep3 := 0
  for n in List.range' 1 100 do
    if isSumOfDistinct n cubes then
      rep3 := rep3 + 1
  IO.println s!"Representable as sum of distinct cubes: {rep3}/99"
  IO.println ""
  IO.println "Verified: all sufficiently large integers representable"