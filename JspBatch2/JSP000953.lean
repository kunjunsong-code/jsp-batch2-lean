set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def isqrt (n : Nat) : Nat :=
  let cands := (List.range' 0 (n + 1)).filter (fun x => x * x <= n)
  match List.getLast? cands with
  | some v => v
  | none => 0

def isSquare (n : Nat) : Bool :=
  let s := isqrt n
  s * s == n

def hasTriple (n : Nat) : Bool :=
  let lim := isqrt n + 1
  let xs := List.range' 0 (lim + 1)
  xs.any fun a =>
    xs.any fun b =>
      let aa := a * a
      let bb := b * b
      aa + bb >= n && isSquare (aa + bb - n) && aa <= n + bb

def main : IO Unit := do
  let failures := (List.range' 1 501).filter (fun n => !hasTriple n)
  IO.println s!"Failures up to 500: {failures}"

#eval main

#eval (List.range' 1 30).map (fun n => (n, hasTriple n))