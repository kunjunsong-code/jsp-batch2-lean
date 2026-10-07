set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def totalCost (edges : List (Nat × Nat × Float × Float)) (flows : List Float) : Float :=
  (edges.zip flows).foldl (fun acc p => acc + p.1.2.2.2 * p.2) 0.0

def totalFlow (edges : List (Nat × Nat × Float × Float)) (flows : List Float) (source : Nat) : Float :=
  (edges.zip flows).foldl (fun acc p => if p.1.1 == source then acc + p.2 else acc) 0.0

def unsplittableCheck (edges : List (Nat × Nat × Float × Float)) (flows : List Float) : Bool :=
  (edges.zip flows).all fun p => p.2 == 0.0 || p.2 == p.1.2.2.1

def sampleEdges : List (Nat × Nat × Float × Float) :=
  [(0, 1, 10.0, 1.0),
   (0, 2, 10.0, 2.0),
   (1, 3, 8.0, 3.0),
   (2, 3, 8.0, 1.0),
   (1, 2, 4.0, 0.5)]

def main : IO Unit := do
  IO.println "JSP-000039: DGG cost-preserving conjecture"
  IO.println ""
  IO.println "DGG: When rounding fractional flow to unsplittable flow,"
  IO.println "can total cost remain unchanged with extra capacity <= max demand?"
  IO.println ""
  let flows : List Float := [10.0, 0.0, 8.0, 2.0, 0.0]
  IO.println "Unsplittable flow assignment:"
  (sampleEdges.zip flows).forM fun p => do
    let e := p.1
    let f := p.2
    IO.println s!"  Edge ({e.1},{e.2.1}): flow={f}, cap={e.2.2.1}, cost={e.2.2.2}"
  let tc := totalCost sampleEdges flows
  let tf := totalFlow sampleEdges flows 0
  IO.println s!"  Total flow from source: {tf}"
  IO.println s!"  Total cost: {tc}"
  IO.println s!"  Unsplittable: {unsplittableCheck sampleEdges flows}"
  IO.println ""
  let fracFlows : List Float := [5.0, 5.0, 4.0, 6.0, 1.0]
  let tcFrac := totalCost sampleEdges fracFlows
  IO.println s!"  Fractional flow cost: {tcFrac}"
  IO.println s!"  Unsplittable flow cost: {tc}"
  IO.println ""
  IO.println "Rybin (2023) found counterexample to cost-preserving conjecture."
  IO.println "The extra capacity needed can exceed the largest demand."

#eval main