import Hypergraph.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas

-------------------
-- GYO algorithm --
-------------------

-- Helper function: find all isolated vertices
-- Input: hypergraph hg
-- Return: a List contains such isolated vertices
-- Idea: for each node in hypergraph nodes `n`, filters the hyperedges to those that contains `n`, check if the number is exactly 1
def findIsolatedVertices (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : List α :=
  hg.nodes.filter (λ n => (hg.hyperedges.filter (λ e => n ∈ e)).length = 1)

-- Helper function: remove all isolated vertices and the corresponding empty hyperedges
-- Input: hypergraph hg
-- Input: vertex v
-- Return: hypergraph after removal
def removeIsolatedVertexAndEdges (α : Type) [DecidableEq α]
    (hg : ComputableHypergraph α) (v : α) : ComputableHypergraph α :=
  let HyperedgesAfterRemoval := hg.hyperedges.map (λ e => List.erase e v)
  let updatedHyperedges := HyperedgesAfterRemoval.filter (λ e => ¬ List.isEmpty e)
  { nodes := List.erase hg.nodes v,
    hyperedges := updatedHyperedges }

-- Helper function: remove hyperedges that contains in other hyperedges
def removeIncludedHyperedges (α : Type) [DecidableEq α] (hyperedges : List (List α)) : List (List α) :=
  hyperedges.filter (λ e =>
    ¬ (hyperedges.any (λ other =>
      (other ≠ e) && (List.all e (λ x => x ∈ other)))))

-- Helper function: remove duplicates from nodes and hyperedges
def removeDuplicates (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : ComputableHypergraph α :=
  let HyperedgesAfterRemovalIncludes := removeIncludedHyperedges α hg.hyperedges
  {
    nodes := hg.nodes.eraseDup,
    hyperedges := HyperedgesAfterRemovalIncludes.eraseDup
  }

-- Helper function: recursive removal
-- partial is essential since we currently do not prove termination
partial def recursiveRemoval (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : ComputableHypergraph α :=
  let isolated := findIsolatedVertices α hg
    let hg' := isolated.foldl (λ acc v => removeIsolatedVertexAndEdges α acc v) hg
    let hg'' := removeDuplicates α hg'
    if hypergraphEqual hg'' hg then
      hg  -- No changes, terminate
    else
      recursiveRemoval α hg''

-- GYO Algorithm: Determines if a hypergraph is acyclic
-- Returns true if acyclic, false otherwise
def gyoAlgorithm (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
  let finalGraph := recursiveRemoval α hg
  finalGraph.nodes.isEmpty

--------------------
-- Below are test --
--------------------

-- Test Case 1: Initial Hypergraph with no hyperedges
-- Test Case 1.1: Check number of nodes and hyperedges
#eval computableNumNodes ℕ initialHypergraph          -- Expected Output: 6
#eval computableNumHyperedges ℕ initialHypergraph     -- Expected Output: 0

-- Test Case 1.2: Find isolated vertices in initialHypergraph
-- Since there are no hyperedges, no vertex appears in exactly one hyperedge
#eval findIsolatedVertices ℕ initialHypergraph          -- Expected Output: []

-- Test Case 2: Adding a node to the initial hypergraph
#eval computableNumNodes ℕ updatedHypergraph1          -- Expected Output: 7
#eval computableNumHyperedges ℕ updatedHypergraph1     -- Expected Output: 0

-- Test Case 2.1: Find isolated vertices in updatedHypergraph1
#eval findIsolatedVertices ℕ updatedHypergraph1          -- Expected Output: []

-- Test Case 3: Adding a single hyperedge
#eval computableNumNodes ℕ updatedHypergraph2          -- Expected Output: 7
#eval computableNumHyperedges ℕ updatedHypergraph2     -- Expected Output: 1

-- Test Case 3.1: Find isolated vertices in updatedHypergraph2
-- Nodes 0, 1, 3, 5 appear in exactly one hyperedge
#eval findIsolatedVertices ℕ updatedHypergraph2          -- Expected Output: [0, 1, 3, 5]

-- Test Case 3.2: Remove isolated vertex '0' and observe changes
def hypergraphAfterRemoval0 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ updatedHypergraph2 0

#eval hypergraphAfterRemoval0.nodes                     -- Expected Output: [1, 2, 3, 4, 5, 6]
#eval hypergraphAfterRemoval0.hyperedges                -- Expected Output: [[1, 3, 5]]

-- Test Case 3.3: Remove isolated vertex '1' from hypergraphAfterRemoval0
def hypergraphAfterRemoval1 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ hypergraphAfterRemoval0 1

#eval hypergraphAfterRemoval1.nodes                     -- Expected Output: [2, 3, 4, 5, 6]
#eval hypergraphAfterRemoval1.hyperedges                -- Expected Output: [[3, 5]]

-- Test Case 3.4: Remove isolated vertex '3' from hypergraphAfterRemoval1
def hypergraphAfterRemoval3 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ hypergraphAfterRemoval1 3

#eval hypergraphAfterRemoval3.nodes                     -- Expected Output: [2, 4, 5, 6]
#eval hypergraphAfterRemoval3.hyperedges                -- Expected Output: [[5]]

-- Test Case 3.5: Remove isolated vertex '5' from hypergraphAfterRemoval3
def hypergraphAfterRemoval5 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ hypergraphAfterRemoval3 5

#eval hypergraphAfterRemoval5.nodes                     -- Expected Output: [2, 4, 6]
#eval hypergraphAfterRemoval5.hyperedges                -- Expected Output: []  -- Hyperedge [5] becomes empty and is removed

-- Test Case 4: More Complex Hypergraph
def complexHypergraph : ComputableHypergraph ℕ :=
  { nodes := [0, 1, 2, 3, 4, 5, 6, 7, 8],
    hyperedges := [
      [0, 1, 2],
      [2, 3, 4],
      [4, 5],
      [5, 6],
      [6, 7],
      [7, 8]
    ] }

-- Test Case 4.1: Find isolated vertices in complexHypergraph
-- Let's list the occurrences:
-- 0: [0,1,2] -> 1
-- 1: [0,1,2] -> 1
-- 2: [0,1,2], [2,3,4] -> 2
-- 3: [2,3,4] -> 1
-- 4: [2,3,4], [4,5] -> 2
-- 5: [4,5], [5,6] -> 2
-- 6: [5,6], [6,7] -> 2
-- 7: [6,7], [7,8] -> 2
-- 8: [7,8] -> 1
-- Therefore, isolated vertices (appear in exactly one hyperedge): [0, 1, 3, 8]

#eval findIsolatedVertices ℕ complexHypergraph            -- Expected Output: [0, 1, 3, 8]

-- Test Case 4.2: Remove all isolated vertices [0,1,3,8] sequentially

-- Remove vertex 0
def complexAfterRemoval0 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ complexHypergraph 0

-- Remove vertex 1
def complexAfterRemoval1 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ complexAfterRemoval0 1

-- Remove vertex 3
def complexAfterRemoval3 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ complexAfterRemoval1 3

-- Remove vertex 8
def complexAfterRemoval8 : ComputableHypergraph ℕ :=
  removeIsolatedVertexAndEdges ℕ complexAfterRemoval3 8

-- Evaluating the nodes and hyperedges after each removal
#eval complexAfterRemoval0.nodes                         -- Expected Output: [1, 2, 3, 4, 5, 6, 7, 8]
#eval complexAfterRemoval0.hyperedges                    -- Expected Output: [[1, 2], [2, 3, 4], [4, 5], [5, 6], [6, 7], [7, 8]]

#eval complexAfterRemoval1.nodes                         -- Expected Output: [2, 3, 4, 5, 6, 7, 8]
#eval complexAfterRemoval1.hyperedges                    -- Expected Output: [[2], [2, 3, 4], [4, 5], [5, 6], [6, 7], [7, 8]]

#eval complexAfterRemoval3.nodes                         -- Expected Output: [2, 4, 5, 6, 7, 8]
#eval complexAfterRemoval3.hyperedges                    -- Expected Output: [[2], [2, 4], [4, 5], [5, 6], [6, 7], [7, 8]]

#eval complexAfterRemoval8.nodes                         -- Expected Output: [2, 4, 5, 6, 7]
#eval complexAfterRemoval8.hyperedges                    -- Expected Output: [[2], [2, 4], [4, 5], [5, 6], [6, 7], [7]]
