set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def chainForN (n : Nat) : List (Nat × Nat) :=
  let divs := (List.range' 1 n).filter (fun d => n % d == 0)
  divs.foldl (fun (tbl : List (Nat × Nat)) (d : Nat) =>
    let best := tbl.filter (fun (prev, _) => prev < d && d % prev == 1)
      |>.map (fun (_, v) => v) |>.max? |>.getD 0
    tbl ++ [(d, 1 + best)]) ([] : List (Nat × Nat))

def main : IO Unit := do
  IO.println "Divisor chains where d_{i+1} = 1 mod d_i, all d_i | n:"
  [2, 6, 12, 24, 30, 60, 120, 180, 240, 360, 720, 840, 2520, 5040, 7200, 10080].forM fun n => do
    let chain := chainForN n
    let mx := chain.map (fun (_, v) => v) |>.max? |>.getD 0
    let divs := chain.map (fun (d, _) => d)
    IO.println s!"  n={n}, divs={divs}, maxChain={mx}"

#eval main