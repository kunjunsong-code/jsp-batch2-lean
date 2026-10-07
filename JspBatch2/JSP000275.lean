set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def canRepresent2 (S : List Nat) (n : Nat) : Bool :=
  S.any fun a => (n >= a) && (S.contains (n - a))

def coverage (S : List Nat) (lo hi : Nat) : Nat :=
  let xs := (List.range' lo (hi - lo))
  let filtered := xs.filter fun n => canRepresent2 S n
  filtered.length

def isBasisOfOrder2 (S : List Nat) (lo hi : Nat) : Bool :=
  let xs := (List.range' lo (hi - lo))
  xs.all fun n => canRepresent2 S n

def main : IO Unit := do
  IO.println "JSP-000275: Minimal asymptotic additive basis"
  IO.println ""
  let squares := (List.range' 0 32).map fun n => n * n
  IO.println s!"Perfect squares up to 961: {squares.length} elements"
  let cov := coverage squares 1 100
  IO.println s!"Coverage of squares for [1,100] via a+a': {cov}/100"
  let isB := isBasisOfOrder2 squares 1 100
  IO.println s!"Squares form additive basis of order 2 for [1,100]: {isB}"
  IO.println ""
  IO.println "Checking minimality - removing each element:"
  let lo := 50
  let hi := 100
  squares.forM fun s =>
    let Sminus := squares.filter fun x => x != s
    let c := coverage Sminus lo hi
    if c < (hi - lo) then
      IO.println s!"  Removing {s}: coverage drops to {c}/{hi-lo} (essential element)"
    else pure ()
  IO.println ""
  let tri := (List.range' 0 45).map fun n => n * (n + 1) / 2
  IO.println s!"Triangular numbers up to 990: {tri.length} elements"
  let covT := coverage tri 1 100
  IO.println s!"Coverage of triangulars for [1,100]: {covT}/100"
  IO.println ""
  IO.println "Lagrange-type: every n = a^2 + b^2 + c^2 + d^2"
  let check4 := (List.range' 1 51).all fun n =>
    squares.any fun a =>
      (n >= a) && squares.any fun b =>
        (n - a >= b) && squares.any fun c =>
          (n - a - b >= c) && squares.contains (n - a - b - c)
  IO.println s!"Every n in [1,50] is sum of 4 squares: {check4}"
  IO.println ""
  IO.println "An asymptotic basis B of order h covers all sufficiently large n."
  IO.println "Minimal means removing any element breaks the basis property."

#eval main