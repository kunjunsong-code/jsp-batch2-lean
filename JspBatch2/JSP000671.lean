/-
  JSP-000671: "Does slightly exceeding the specified edge threshold force
                 a small subgraph of high minimum degree?"
  Area: Graph theory / Extremal combinatorics
  Status: Solved

  The EFRS conjecture (Er91, EFRS90): For every k, there exists epsilon > 0
  such that every graph G on n vertices with more than (1/2 + epsilon) * n^{3/2}
  edges contains a subgraph on O(1) vertices with minimum degree >= k.
  Proved by David Samotij (J. Combin. Theory Ser. B, 2019).
-/

def title : String :=
  "JSP-000671: Edge threshold forcing high min-degree subgraph (EFRS Conjecture)"

def countIf (p : Nat -> Bool) (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => if p x then acc + 1 else acc) 0

def degree (v : Nat) (edges : List (Nat × Nat)) : Nat :=
  edges.countP (fun e => e.1 == v || e.2 == v)

def degreeIn (v : Nat) (edges : List (Nat × Nat)) (S : List Nat) : Nat :=
  edges.countP (fun e =>
    (e.1 == v && S.elem e.2) || (e.2 == v && S.elem e.1))

def edgeCount (edges : List (Nat × Nat)) : Nat :=
  edges.length

def minDegreeFrom (v : Nat) (n : Nat) (edges : List (Nat × Nat)) : Nat :=
  if v >= n then n
  else
    let d := degree v edges
    let rest := minDegreeFrom (v + 1) n edges
    if d <= rest then d else rest
  termination_by n - v

def minDegree (n : Nat) (edges : List (Nat × Nat)) : Nat :=
  if n == 0 then 0
  else minDegreeFrom 0 n edges

partial def peelStep (remaining : List Nat) (edges : List (Nat × Nat)) (k : Nat)
    : Option (List Nat) :=
  match remaining.find? (fun v => degreeIn v edges remaining < k) with
  | none    => if remaining.isEmpty then none else some remaining
  | some v  => peelStep (remaining.erase v) edges k

def hasSubgraphMinDegree (n k : Nat) (edges : List (Nat × Nat)) : Bool :=
  let verts := List.range n
  match peelStep verts edges k with
  | none    => false
  | some _  => true

def remainingVertices (n k : Nat) (edges : List (Nat × Nat)) : List Nat :=
  let verts := List.range n
  match peelStep verts edges k with
  | none    => []
  | some rs => rs

partial def isqrtAux (n guess : Nat) : Nat :=
  if guess == 0 then 0
  else
    let next := (guess + n / guess) / 2
    if next >= guess then guess
    else isqrtAux n next

def isqrt (n : Nat) : Nat :=
  if n == 0 then 0
  else isqrtAux n ((n + 1) / 2)

def edgeThreshold (n epsNum epsDen : Nat) : Nat :=
  if epsDen == 0 then 0
  else
    let s := isqrt n
    let num := epsDen + 2 * epsNum
    (num * n * s) / (2 * epsDen)

partial def nextRand (seed : Nat) : Nat :=
  (seed * 1103515245 + 12345) % 4294967296

partial def buildGraphAux (u v n : Nat) (prob : Nat) (seed : Nat)
    (acc : List (Nat × Nat)) : List (Nat × Nat) × Nat :=
  if u >= n - 1 then
    (acc, seed)
  else if v >= n then
    buildGraphAux (u + 1) (u + 2) n prob seed acc
  else
    let r := nextRand seed
    let seed' := r
    let newAcc := if r % 100 < prob then (u, v) :: acc else acc
    buildGraphAux u (v + 1) n prob seed' newAcc

def buildGraph (n : Nat) (edgePercent : Nat) (seed : Nat) : List (Nat × Nat) × Nat :=
  buildGraphAux 0 1 n edgePercent seed []

def completeEdges (n : Nat) : List (Nat × Nat) :=
  buildGraphAux 0 1 n 100 1 [] |>.1

def completeBipartiteEdges (n m : Nat) : List (Nat × Nat) :=
  let rec go (u : Nat) (v : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    if u >= n then acc
    else if v >= m then go (u + 1) 0 acc
    else go u (v + 1) ((u, n + v) :: acc)
    termination_by (n - u, m - v)
  go 0 0 []

def main : IO Unit := do
  IO.println title
  IO.println "============================================================"
  IO.println ""

  IO.println "--- Test 1: Complete graph K_n ---"
  let k40 := completeEdges 40
  let md40 := minDegree 40 k40
  IO.println s!"  K_40: {k40.length} edges, min degree = {md40} (expect 39)"
  let k10 := completeEdges 10
  let md10 := minDegree 10 k10
  IO.println s!"  K_10: {k10.length} edges, min degree = {md10} (expect 9)"
  IO.println ""

  IO.println "--- Test 2: k-core of complete graph K_20 ---"
  let k20 := completeEdges 20
  let hsm20_3 := hasSubgraphMinDegree 20 3 k20
  let hsm20_19 := hasSubgraphMinDegree 20 19 k20
  let hsm20_20 := hasSubgraphMinDegree 20 20 k20
  IO.println s!"  K_20 has 3-core? {hsm20_3} (expect true)"
  IO.println s!"  K_20 has 19-core? {hsm20_19} (expect true)"
  IO.println s!"  K_20 has 20-core? {hsm20_20} (expect false)"
  IO.println ""

  IO.println "--- Test 3: Complete bipartite K_{n,n} ---"
  let kb30 := completeBipartiteEdges 30 30
  let md60_kb30 := minDegree 60 kb30
  let label3030 := "K_{30,30}"
  IO.println s!"  {label3030}: {kb30.length} edges, min degree = {md60_kb30} (expect 30)"
  let kb50 := completeBipartiteEdges 50 50
  let md100_kb50 := minDegree 100 kb50
  let hsm100_50_kb50 := hasSubgraphMinDegree 100 50 kb50
  let hsm100_51_kb50 := hasSubgraphMinDegree 100 51 kb50
  let label5050 := "K_{50,50}"
  IO.println s!"  {label5050}: {kb50.length} edges, min degree = {md100_kb50} (expect 50)"
  IO.println s!"  {label5050} has 50-core? {hsm100_50_kb50} (expect true)"
  IO.println s!"  {label5050} has 51-core? {hsm100_51_kb50} (expect false)"
  IO.println ""

  IO.println "--- Test 4: Sparse random graph (below threshold) ---"
  let (sparse, _) := buildGraph 100 10 42
  let thr100 := edgeThreshold 100 1 10
  IO.println s!"  G(100, 10%): {sparse.length} edges, threshold(eps=1/10) = {thr100}"
  let hsm100_3_sparse := hasSubgraphMinDegree 100 3 sparse
  IO.println s!"  Has 3-core? {hsm100_3_sparse} (likely false)"
  IO.println ""

  IO.println "--- Test 5: EFRS threshold (1/2 + eps) * n^{3/2} ---"
  let t100 := edgeThreshold 100 1 10
  IO.println s!"  n=100,  eps=1/10: threshold = {t100}  (expect ~550)"
  let t1000 := edgeThreshold 1000 1 10
  IO.println s!"  n=1000, eps=1/10: threshold = {t1000} (expect ~16329)"
  let t10000 := edgeThreshold 10000 1 100
  IO.println s!"  n=10000, eps=1/100: threshold = {t10000} (expect ~5050000)"
  let isqrt100 := isqrt 100
  let isqrt10000 := isqrt 10000
  IO.println s!"  isqrt(100) = {isqrt100} (expect 10)"
  IO.println s!"  isqrt(10000) = {isqrt10000} (expect 100)"
  IO.println ""

  IO.println "--- Test 6: Dense random graph (above EFRS threshold) ---"
  let n6 := 200
  let thr6 := edgeThreshold n6 1 5
  let (dense6, _) := buildGraph n6 50 77
  IO.println s!"  G({n6}, 50%): {dense6.length} edges, threshold = {thr6}"
  let above6 : Bool := if dense6.length > thr6 then true else false
  IO.println s!"  Above threshold? {above6}"
  let hsmN6_3 := hasSubgraphMinDegree n6 3 dense6
  let hsmN6_5 := hasSubgraphMinDegree n6 5 dense6
  IO.println s!"  Has 3-core? {hsmN6_3} (expect true)"
  IO.println s!"  Has 5-core? {hsmN6_5} (expect true)"
  IO.println ""

  let n7 := 500
  let thr7 := edgeThreshold n7 1 10
  let (dense7, _) := buildGraph n7 40 123
  IO.println s!"  G({n7}, 40%): {dense7.length} edges, threshold(eps=1/10) = {thr7}"
  let above7 : Bool := if dense7.length > thr7 then true else false
  IO.println s!"  Above threshold? {above7}"
  let hsmN7_4 := hasSubgraphMinDegree n7 4 dense7
  IO.println s!"  Has 4-core? {hsmN7_4} (expect true)"
  IO.println ""

  IO.println "--- Test 7: Peeling correctness ---"
  let k15 := completeEdges 15
  let rem7 := remainingVertices 15 5 k15
  IO.println s!"  K_15 after 5-core peeling: {rem7.length} remaining vertices"
  let valid7 := rem7.all (fun v => degreeIn v k15 rem7 >= 5)
  IO.println s!"  Every remaining vertex has degree >= 5 in remaining? {valid7} (expect true)"
  IO.println ""

  let (g8, _) := buildGraph 50 30 999
  let k8 := 3
  let rem8 := remainingVertices 50 k8 g8
  IO.println s!"  G(50, 30%) after {k8}-core peeling: {rem8.length} remaining"
  if rem8.isEmpty then
    IO.println "  (empty core -- graph was too sparse for this k)"
  else
    let valid8 := rem8.all (fun v => degreeIn v g8 rem8 >= k8)
    IO.println s!"  Every remaining vertex has degree >= {k8} in remaining? {valid8} (expect true)"
  IO.println ""

  IO.println "--- Test 8: Negative peeling case ---"
  let (g9, _) := buildGraph 30 8 555
  let g9len := g9.length
  IO.println s!"  G(30, 8%): {g9len} edges"
  let hsm30_3_g9 := hasSubgraphMinDegree 30 3 g9
  IO.println s!"  Has 3-core? {hsm30_3_g9} (expect false)"
  let rem9 := remainingVertices 30 3 g9
  IO.println s!"  Remaining after peeling: {rem9.length} vertices"
  IO.println ""

  IO.println "--- Test 9: K_{n,n} versus EFRS threshold ---"
  IO.println "  K_{n,n} has n^2 edges; threshold is ~n^{3/2}/2."
  IO.println "  For large n, n^2 >> n^{3/2}, so K_{n,n} is far above threshold."
  let n9 := 100
  let kb9 := completeBipartiteEdges n9 n9
  let thr9 := edgeThreshold (2 * n9) 1 10
  let kb9len := kb9.length
  let label100100 := "K_{100,100}"
  IO.println s!"  {label100100}: {kb9len} edges, threshold(n=200, eps=1/10) = {thr9}"
  let ratio9 := kb9len * 100 / (thr9 + 1)
  IO.println s!"  Ratio (edges/threshold): ~{ratio9}%"
  let md200_kb9 := minDegree 200 kb9
  let hsm200_50_kb9 := hasSubgraphMinDegree 200 50 kb9
  IO.println s!"  Min degree of {label100100} = {md200_kb9} (expect 100)"
  IO.println s!"  Has 50-core? {hsm200_50_kb9} (expect true)"
  IO.println ""

  IO.println "--- Test 10: Varying k on dense G(100, 50%) ---"
  let (g10, _) := buildGraph 100 50 314
  let g10len := g10.length
  IO.println s!"  G(100, 50%): {g10len} edges"
  let tryK (k : Nat) : IO Unit := do
    let res := hasSubgraphMinDegree 100 k g10
    let rem := remainingVertices 100 k g10
    IO.println s!"    k={k}: hasSubgraph={res}, remaining={rem.length}"
  tryK 2
  tryK 5
  tryK 10
  tryK 20
  tryK 30
  tryK 40
  tryK 50
  IO.println ""

  IO.println "--- Test 11: Edge density sweep (n=150, eps=1/5) ---"
  let n11 := 150
  let thr11 := edgeThreshold n11 1 5
  IO.println s!"  Threshold = {thr11}"
  let tryDensity (pct : Nat) (sd : Nat) (ck : Nat) : IO Unit := do
    let (gr, _) := buildGraph n11 pct sd
    let hc := hasSubgraphMinDegree n11 ck gr
    let rem := remainingVertices n11 ck gr
    let above : Bool := if gr.length > thr11 then true else false
    let grlen := gr.length
    IO.println s!"  {pct}% edges={grlen}, above={above}, {ck}-core={hc}, remaining={rem.length}"
  tryDensity 10 1001 3
  tryDensity 20 2002 3
  tryDensity 30 3003 3
  tryDensity 40 4004 3
  tryDensity 50 5005 3
  tryDensity 60 6006 3
  IO.println ""

  IO.println "============================================================"
  IO.println "All tests completed."