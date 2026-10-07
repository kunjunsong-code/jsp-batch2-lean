set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def eulerTotient (n : Nat) : Nat :=
  ((List.range' 1 n).filter fun k => Nat.gcd k n == 1).length

def main : IO Unit := do
  IO.println "JSP-000565: Ratio of largest to smallest integer with common totient value"
  IO.println ""
  IO.println "Euler totient values for small n:"
  (List.range' 1 21).forM fun n =>
    IO.println s!"  phi({n}) = {eulerTotient n}"
  IO.println ""
  IO.println "Totient fibers and max ratios (n up to 200):"
  let vals := (List.range' 1 201).map fun n => (n, eulerTotient n)
  let allTotients := vals.map fun p => p.2
  let uniqueTotients := allTotients.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  uniqueTotients.forM fun t =>
    let fiber := (vals.filter fun p => p.2 == t).map fun p => p.1
    if fiber.length >= 2 then
      let mn := fiber.foldl (fun acc x => if x < acc then x else acc) (fiber.getD 0 999999)
      let mx := fiber.foldl (fun acc x => if x > acc then x else acc) 0
      if mn > 0 then
        IO.println s!"  phi={t}: min={mn}, max={mx}, ratio={mx.toFloat / mn.toFloat}"
      else pure ()
    else pure ()

#eval main