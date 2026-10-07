set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def maxSideSum (squares : List Float) : Bool :=
  let totalArea := squares.foldl (fun acc s => acc + s * s) 0.0
  totalArea <= 1.0

def sideLenSum (squares : List Float) : Float :=
  squares.foldl (fun acc s => acc + s) 0.0

def main : IO Unit := do
  IO.println "JSP-000118: Maximum sum of side lengths of nonoverlapping squares in unit square"
  IO.println ""
  let sq1 : List Float := [0.5, 0.5]
  IO.println s!"Squares {[0.5, 0.5]}: total area = {sq1.foldl (fun a s => a + s*s) 0.0}, side sum = {sideLenSum sq1}"
  IO.println s!"  Fits in unit square: {maxSideSum sq1}"
  IO.println ""
  let sq2 : List Float := [0.5, 0.25, 0.25, 0.25, 0.25]
  IO.println s!"Squares {[0.5, 0.25, 0.25, 0.25, 0.25]}: area = {sq2.foldl (fun a s => a + s*s) 0.0}, side sum = {sideLenSum sq2}"
  IO.println s!"  Fits in unit square: {maxSideSum sq2}"
  IO.println ""
  let sq3 : List Float := [1.0 / 2.0, 1.0 / 4.0, 1.0 / 4.0, 1.0 / 8.0, 1.0 / 8.0, 1.0 / 8.0, 1.0 / 8.0]
  let area3 := sq3.foldl (fun a s => a + s * s) 0.0
  IO.println s!"Recursive packing: area = {area3}, side sum = {sideLenSum sq3}"
  IO.println s!"  Fits in unit square: {maxSideSum sq3}"
  IO.println ""
  IO.println "Known: sup of side-length sums can exceed any finite bound."
  IO.println "Erdos asked if the supremum is finite; it is NOT."

#eval main