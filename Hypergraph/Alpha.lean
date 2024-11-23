import Hypergraph.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas

-------------------
-- GYO algorithm --
-------------------

-- Helper function: find all isolated vertices
-- Input: hypergraph hg
-- Return: a Finset contains such isolated vertices
-- Idea: for each node in hypergraph nodes `n`, filters the hyperedges to those that contains `n`, check if the number is exactly 1
def findIsolatedVertices (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Finset α :=
  hg.nodes.filter (λ n => (hg.hyperedges.filter (λ e => n ∈ e)).card = 1)

-- Helper function: remove all isolated vertices and the corresponding empty hyperedges
-- Input: hypergraph hg
-- Input: vertex v
-- Return: hypergraph after removal
def removeIsolatedVerticesAndEdges (α : Type) [DecidableEq α]
    (hg : ComputableHypergraph α) (vs : Finset α) : ComputableHypergraph α :=
  let newNodes := hg.nodes \ vs
  let newHyperedges := Finset.image (λ e => e \ vs) hg.hyperedges
  { nodes := newNodes, hyperedges := newHyperedges }

-- Helper function: remove hyperedges that contains in other hyperedges
def removeIncludedHyperedges (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : ComputableHypergraph α :=
  let updatedHyperedges := hg.hyperedges.filter (λ e =>
    ¬ ∃ other ∈ hg.hyperedges, (other ≠ e) ∧ (e ⊆ other))
  {
    nodes := hg.nodes
    hyperedges := updatedHyperedges
  }

-- Helper function: recursive removal
-- partial is essential since we currently do not prove termination
partial def recursiveRemoval (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : ComputableHypergraph α :=
  let isolated := findIsolatedVertices α hg
  let hg' := removeIsolatedVerticesAndEdges α hg isolated
  let hg'' := removeIncludedHyperedges α hg'

  if hg'' = hg then
    hg  -- No changes, terminate
  else
    recursiveRemoval α hg''

-- GYO Algorithm: Determines if a hypergraph is acyclic
-- Returns true if acyclic, false otherwise
def gyoAlgorithm (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
  let finalGraph := recursiveRemoval α hg
  ¬ finalGraph.nodes.Nonempty
