abbrev Vertex := Nat

abbrev Edge := Vertex × Vertex

abbrev Graph := List Edge

abbrev Coloring := List (Edge × Nat)

def listAny {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => false
  | x :: rest => p x || listAny rest p

def listAll {α : Type} (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => true
  | x :: rest => p x && listAll rest p

def listLen {α : Type} (l : List α) : Nat :=
  match l with
  | [] => 0
  | _ :: rest => 1 + listLen rest

def listAppend {α : Type} (l1 l2 : List α) : List α :=
  match l1 with
  | [] => l2
  | x :: rest => x :: listAppend rest l2

def listFilter {α : Type} (l : List α) (p : α → Bool) : List α :=
  match l with
  | [] => []
  | x :: rest => if p x then x :: listFilter rest p else listFilter rest p

def listMap {α β : Type} (l : List α) (f : α → β) : List β :=
  match l with
  | [] => []
  | x :: rest => f x :: listMap rest f

def edgeMatches (e : Edge) (u v : Nat) : Bool :=
  (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

def hasEdge (g : Graph) (u v : Nat) : Bool :=
  listAny g (fun e => edgeMatches e u v)

partial def getColor (c : Coloring) (u v : Nat) : Nat :=
  match c with
  | [] => 0
  | (e, col) :: rest =>
    if edgeMatches e u v then col
    else getColor rest u v

def edgesOfColor (col : Coloring) (c : Nat) : Graph :=
  listMap (listFilter col (fun pair => pair.2 == c)) (fun pair => pair.1)

def isTriangleInGraph (g : Graph) (a b c : Nat) : Bool :=
  hasEdge g a b && hasEdge g b c && hasEdge g a c

def isMonoTriangle (g : Graph) (col : Coloring) (a b c : Nat) : Bool :=
  if hasEdge g a b && hasEdge g b c && hasEdge g a c then
    let c1 := getColor col a b
    let c2 := getColor col b c
    let c3 := getColor col a c
    c1 == c2 && c2 == c3
  else
    false

partial def checkMonoPairs (g : Graph) (col : Coloring) (a b : Nat) (rest : List Nat) : Bool :=
  match rest with
  | [] => false
  | c :: cs =>
    isMonoTriangle g col a b c || checkMonoPairs g col a b cs

partial def checkMonoTriples (g : Graph) (col : Coloring) (a : Nat) (rest : List Nat) : Bool :=
  match rest with
  | [] => false
  | b :: bs =>
    checkMonoPairs g col a b bs || checkMonoTriples g col a bs

partial def hasMonoTriangle (g : Graph) (col : Coloring) (verts : List Nat) : Bool :=
  match verts with
  | [] => false
  | a :: rest =>
    checkMonoTriples g col a rest || hasMonoTriangle g col rest

partial def checkPlainPairs (g : Graph) (a b : Nat) (rest : List Nat) : Bool :=
  match rest with
  | [] => false
  | c :: cs =>
    isTriangleInGraph g a b c || checkPlainPairs g a b cs

partial def checkPlainTriples (g : Graph) (a : Nat) (rest : List Nat) : Bool :=
  match rest with
  | [] => false
  | b :: bs =>
    checkPlainPairs g a b bs || checkPlainTriples g a bs

partial def hasTriangle (g : Graph) (verts : List Nat) : Bool :=
  match verts with
  | [] => false
  | a :: rest =>
    checkPlainTriples g a rest || hasTriangle g rest

partial def greedyIndepHelper (g : Graph) (verts : List Nat) (acc : List Nat) : List Nat :=
  match verts with
  | [] => acc
  | v :: rest =>
    let canAdd := listAll acc (fun u => !(hasEdge g v u))
    if canAdd then greedyIndepHelper g rest (v :: acc)
    else greedyIndepHelper g rest acc

def greedyIndepSet (g : Graph) (verts : List Nat) : List Nat :=
  greedyIndepHelper g verts []

def isIndependentSet (g : Graph) (s : List Nat) : Bool :=
  match s with
  | [] => true
  | v :: rest =>
    listAll rest (fun u => !(hasEdge g v u)) && isIndependentSet g rest

partial def completeGraphGo (n i j : Nat) : Graph :=
  if i >= n then []
  else if j >= n then completeGraphGo n (i + 1) (i + 2)
  else (i, j) :: completeGraphGo n i (j + 1)

def completeGraph (n : Nat) : Graph :=
  completeGraphGo n 0 1

partial def vertsFrom (start n : Nat) : List Nat :=
  if start >= n then []
  else start :: vertsFrom (start + 1) n

def vertsList (n : Nat) : List Nat :=
  vertsFrom 0 n

partial def bipartiteGo (m n i j : Nat) : Graph :=
  if i >= m then []
  else if j >= n then bipartiteGo m n (i + 1) 0
  else (i, m + j) :: bipartiteGo m n i (j + 1)

def bipartiteGraph (m n : Nat) : Graph :=
  bipartiteGo m n 0 0

partial def cycleGo (n i : Nat) : Graph :=
  if i >= n then []
  else if i + 1 >= n then [(i, 0)]
  else (i, i + 1) :: cycleGo n (i + 1)

def cycleGraph (n : Nat) : Graph :=
  if n < 3 then []
  else cycleGo n 0

def k5Coloring2 : Coloring :=
  [((0, 1), 0), ((1, 2), 0), ((2, 3), 0), ((3, 4), 0), ((0, 4), 0),
   ((0, 2), 1), ((0, 3), 1), ((1, 3), 1), ((1, 4), 1), ((2, 4), 1)]

def k6Coloring2 : Coloring :=
  [((0, 1), 1), ((0, 2), 0), ((0, 3), 1), ((0, 4), 0), ((0, 5), 1),
   ((1, 2), 1), ((1, 3), 0), ((1, 4), 1), ((1, 5), 0),
   ((2, 3), 1), ((2, 4), 0), ((2, 5), 1),
   ((3, 4), 1), ((3, 5), 0),
   ((4, 5), 1)]

def k5Coloring3 : Coloring :=
  [((0, 1), 1), ((0, 2), 2), ((0, 3), 0), ((0, 4), 1),
   ((1, 2), 0), ((1, 3), 1), ((1, 4), 2),
   ((2, 3), 2), ((2, 4), 0),
   ((3, 4), 1)]

def k55Coloring1 : Coloring :=
  listMap (bipartiteGraph 5 5) (fun e => (e, 0))

partial def k10Coloring3Go (i j : Nat) (acc : Coloring) : Coloring :=
  if i >= 10 then acc
  else if j >= 10 then k10Coloring3Go (i + 1) (i + 2) acc
  else if i >= j then k10Coloring3Go i (j + 1) acc
  else k10Coloring3Go i (j + 1) (((i, j), (i + j) % 3) :: acc)

def k10Coloring3 : Coloring :=
  k10Coloring3Go 0 1 []

def main : IO Unit := do
  IO.println "=== JSP-000768: Ramsey-Free Colorings and Independent Sets ==="
  IO.println ""
  IO.println "Question: If edges of G can be k-colored with no monochromatic"
  IO.println "triangle, must G have a sufficiently large independent set?"
  IO.println ""
  IO.println "--- Test 1: K_6 with 2-coloring ---"
  let g6 := completeGraph 6
  let v6 := vertsList 6
  let c6 := k6Coloring2
  let hasMono6 := hasMonoTriangle g6 c6 v6
  let indep6 := greedyIndepSet g6 v6
  let indepSz6 := listLen indep6
  let edgeSz6 := listLen g6
  let msg1a := s!"Vertices: 6, Edges: {edgeSz6}, Colors: 2"
  IO.println msg1a
  IO.println "Coloring: edge (i,j) gets color (i+j) mod 2"
  let msg1b := s!"Has monochromatic triangle: {hasMono6}"
  IO.println msg1b
  IO.println "Expected: true (since R(3,3) = 6)"
  let msg1c := s!"Greedy independent set size: {indepSz6}"
  IO.println msg1c
  IO.println ""
  IO.println "--- Test 2: K_5 with 2-coloring (pentagon construction) ---"
  let g5 := completeGraph 5
  let v5 := vertsList 5
  let c5 := k5Coloring2
  let hasMono5 := hasMonoTriangle g5 c5 v5
  let edgeSz5 := listLen g5
  let msg2a := s!"Vertices: 5, Edges: {edgeSz5}, Colors: 2"
  IO.println msg2a
  IO.println "Color 0: 5-cycle (0-1-2-3-4-0)"
  IO.println "Color 1: complementary 5-cycle (0-2-4-1-3-0)"
  let msg2b := s!"Has monochromatic triangle: {hasMono5}"
  IO.println msg2b
  IO.println "Expected: false (since R(3,3) = 6 > 5)"
  IO.println ""
  IO.println "--- Test 3: Color classes of K_5 2-coloring ---"
  let cc0 := edgesOfColor c5 0
  let cc1 := edgesOfColor c5 1
  let hasTriC0 := hasTriangle cc0 v5
  let hasTriC1 := hasTriangle cc1 v5
  let indepC0 := greedyIndepSet cc0 v5
  let indepC1 := greedyIndepSet cc1 v5
  let szC0 := listLen cc0
  let szC1 := listLen cc1
  let iSzC0 := listLen indepC0
  let iSzC1 := listLen indepC1
  let valC0 := isIndependentSet cc0 indepC0
  let valC1 := isIndependentSet cc1 indepC1
  let msg3a := s!"Color 0 edges: {szC0}, Color 1 edges: {szC1}"
  IO.println msg3a
  let msg3b := s!"Color 0 has triangle: {hasTriC0}"
  IO.println msg3b
  let msg3c := s!"Color 0 greedy indep set size: {iSzC0}, valid: {valC0}"
  IO.println msg3c
  let msg3d := s!"Color 1 has triangle: {hasTriC1}"
  IO.println msg3d
  let msg3e := s!"Color 1 greedy indep set size: {iSzC1}, valid: {valC1}"
  IO.println msg3e
  IO.println ""
  IO.println "--- Test 4: K_5 with 3-coloring ---"
  let c53 := k5Coloring3
  let hasMono53 := hasMonoTriangle g5 c53 v5
  let cc30 := edgesOfColor c53 0
  let cc31 := edgesOfColor c53 1
  let cc32 := edgesOfColor c53 2
  let hasTri30 := hasTriangle cc30 v5
  let hasTri31 := hasTriangle cc31 v5
  let hasTri32 := hasTriangle cc32 v5
  let indep30 := greedyIndepSet cc30 v5
  let indep31 := greedyIndepSet cc31 v5
  let indep32 := greedyIndepSet cc32 v5
  let sz30 := listLen cc30
  let sz31 := listLen cc31
  let sz32 := listLen cc32
  let iSz30 := listLen indep30
  let iSz31 := listLen indep31
  let iSz32 := listLen indep32
  IO.println "Coloring: edge (i,j) gets color (i+j) mod 3"
  let msg4a := s!"Has monochromatic triangle: {hasMono53}"
  IO.println msg4a
  IO.println "Expected: false (since R(3,3,3) = 17 > 5)"
  let msg4b := s!"Color 0: {sz30} edges, triangle: {hasTri30}, indep size: {iSz30}"
  IO.println msg4b
  let msg4c := s!"Color 1: {sz31} edges, triangle: {hasTri31}, indep size: {iSz31}"
  IO.println msg4c
  let msg4d := s!"Color 2: {sz32} edges, triangle: {hasTri32}, indep size: {iSz32}"
  IO.println msg4d
  IO.println ""
  IO.println "--- Test 5: K_{5,5} bipartite graph ---"
  let g55 := bipartiteGraph 5 5
  let v55 := vertsList 10
  let c55 := k55Coloring1
  let hasMono55 := hasMonoTriangle g55 c55 v55
  let hasTri55 := hasTriangle g55 v55
  let indep55 := greedyIndepSet g55 v55
  let iSz55 := listLen indep55
  let edgeSz55 := listLen g55
  let val55 := isIndependentSet g55 indep55
  let msg5a := s!"Vertices: 10, Edges: {edgeSz55}, Colors: 1"
  IO.println msg5a
  let msg5b := s!"Has triangle: {hasTri55}"
  IO.println msg5b
  let msg5c := s!"Has monochromatic triangle: {hasMono55}"
  IO.println msg5c
  let msg5d := s!"Greedy independent set size: {iSz55}, valid: {val55}"
  IO.println msg5d
  IO.println ""
  IO.println "--- Test 6: K_10 with 3-coloring ---"
  let g10 := completeGraph 10
  let v10 := vertsList 10
  let c10 := k10Coloring3
  let hasMono10 := hasMonoTriangle g10 c10 v10
  let edgeSz10 := listLen g10
  let msg6a := s!"Vertices: 10, Edges: {edgeSz10}, Colors: 3"
  IO.println msg6a
  IO.println "Coloring: edge (i,j) gets color (i+j) mod 3"
  let msg6b := s!"Has monochromatic triangle: {hasMono10}"
  IO.println msg6b
  IO.println "Expected: true (this simple coloring is not optimal for K_10)"
  let cc100 := edgesOfColor c10 0
  let cc101 := edgesOfColor c10 1
  let cc102 := edgesOfColor c10 2
  let hasTri100 := hasTriangle cc100 v10
  let hasTri101 := hasTriangle cc101 v10
  let hasTri102 := hasTriangle cc102 v10
  let indep100 := greedyIndepSet cc100 v10
  let indep101 := greedyIndepSet cc101 v10
  let indep102 := greedyIndepSet cc102 v10
  let sz100 := listLen cc100
  let sz101 := listLen cc101
  let sz102 := listLen cc102
  let iSz100 := listLen indep100
  let iSz101 := listLen indep101
  let iSz102 := listLen indep102
  let msg6c := s!"Color 0: {sz100} edges, triangle: {hasTri100}, indep size: {iSz100}"
  IO.println msg6c
  let msg6d := s!"Color 1: {sz101} edges, triangle: {hasTri101}, indep size: {iSz101}"
  IO.println msg6d
  let msg6e := s!"Color 2: {sz102} edges, triangle: {hasTri102}, indep size: {iSz102}"
  IO.println msg6e
  IO.println ""
  IO.println "--- Test 7: C_5 cycle graph (triangle-free) ---"
  let gc5 := cycleGraph 5
  let vc5 := vertsList 5
  let cc5 := listMap gc5 (fun e => (e, 0))
  let hasMonoC5 := hasMonoTriangle gc5 cc5 vc5
  let hasTriC5 := hasTriangle gc5 vc5
  let indepC5 := greedyIndepSet gc5 vc5
  let iSzC5 := listLen indepC5
  let edgeSzC5 := listLen gc5
  let valC5 := isIndependentSet gc5 indepC5
  let msg7a := s!"Vertices: 5, Edges: {edgeSzC5}, Colors: 1"
  IO.println msg7a
  let msg7b := s!"Has triangle: {hasTriC5}"
  IO.println msg7b
  let msg7c := s!"Has monochromatic triangle: {hasMonoC5}"
  IO.println msg7c
  let msg7d := s!"Greedy independent set size: {iSzC5}, valid: {valC5}"
  IO.println msg7d
  IO.println ""
  IO.println "=== Summary ==="
  IO.println "1. K_6 cannot be 2-colored without monochromatic triangle (R(3,3)=6)."
  IO.println "2. K_5 CAN be 2-colored without monochromatic triangle."
  IO.println "3. Each triangle-free color class on 5 vertices has indep set >= 2."
  IO.println "4. With 3 colors on K_5, color classes have indep set >= 3."
  IO.println "5. Bipartite K_{5,5} is triangle-free with indep set of size 5."
  IO.println "6. K_10 with (i+j) mod 3 coloring has mono triangles (not optimal)."
  IO.println "7. C_5 is triangle-free with indep set of size 2."
  IO.println ""
  IO.println "Key insight: The Ramsey number R(3,...,3) with k colors bounds the"
  IO.println "order of complete graphs that admit k-colorings without monochromatic"
  IO.println "triangles. When such a coloring exists, each color class is triangle-free."
  IO.println "By Ramsey theory (R(3,t) grows as t^2/log t), every triangle-free graph"
  IO.println "on n vertices has independence number at least proportional to sqrt(n)."
  IO.println "Thus Ramsey-free colorings guarantee large independent sets in each"
  IO.println "color class, and more colors permit larger complete graphs to be colored."