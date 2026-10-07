set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def myFact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFact n

def checkFactDiv (a b c d : Nat) : Bool :=
  (myFact a * myFact b) > 0 && (myFact c * myFact d) % (myFact a * myFact b) == 0

def indexSumDiff (a b c d : Nat) : Int :=
  Int.ofNat (c + d) - Int.ofNat (a + b)

def main : IO Unit := do
  IO.println "JSP-000596: If a!*b! | c!*d!, how far apart can (c+d)-(a+b) be?"
  IO.println ""
  IO.println "Searching for examples with a!*b! | c!*d! and a+b < c+d:"
  (List.range' 1 8).forM fun a => do
    (List.range' a 8).forM fun b => do
      (List.range' 1 15).forM fun c => do
        (List.range' c 15).forM fun d => do
          if a + b < c + d && checkFactDiv a b c d then
            let diff := (c + d) - (a + b)
            if diff >= 1 then
              IO.println s!"  {a}!*{b}! | {c}!*{d}!, sum diff = {diff}"
  IO.println ""
  IO.println "Maximum sum differences found:"
  let examples := [
    (1, 2, 3, 4), (2, 3, 5, 6), (1, 5, 2, 6),
    (3, 4, 6, 8), (2, 6, 4, 7), (1, 3, 2, 5)
  ]
  examples.forM fun (a, b, c, d) => do
    let fab := myFact a * myFact b
    let fcd := myFact c * myFact d
    let div := fcd % fab == 0
    IO.println s!"  {a}!*{b}!={fab}, {c}!*{d}!={fcd}, div={div}, diff={(c+d)-(a+b)}"

#eval main