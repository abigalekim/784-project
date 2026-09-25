import Hypergraph.Basic
import Hypergraph.TestGraphs
import Mathlib.Data.List.Basic

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
def isAlphaAcylic (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
  let finalGraph := recursiveRemoval α hg
  ¬ finalGraph.nodes.Nonempty

-------------------------------------------------------------
-- Alpha acyclicity (Brault-Baron, "Hypergraph Acyclicity  --
-- Revisited", arXiv:1403.7076, Definitions 1 and 2)       --
-------------------------------------------------------------

-- Induced subhypergraph: H[S] = {e ∩ S | e ∈ H} \ {∅}
def inducedEdges (α : Type) [DecidableEq α] (G : ComputableHypergraph α) (S : Finset α) :
    Finset (Finset α) :=
  (G.hyperedges.image (· ∩ S)).filter (·.Nonempty)

-- Minimization: M(H) = {e ∈ H | ∄ f ∈ H, e ⊂ f}, the edges maximal for inclusion
def maximalEdges (α : Type) [DecidableEq α] (H : Finset (Finset α)) : Finset (Finset α) :=
  H.filter (fun e => ∀ f ∈ H, ¬ e ⊂ f)

-- x and y are neighbours when some edge contains both
def areNeighbours (α : Type) (G : ComputableHypergraph α) (x y : α) : Prop :=
  ∃ e ∈ G.hyperedges, x ∈ e ∧ y ∈ e

-- A clique is a set of vertices that are pairwise neighbours
def isClique (α : Type) (G : ComputableHypergraph α) (K : Finset α) : Prop :=
  K ⊆ G.nodes ∧ ∀ x ∈ K, ∀ y ∈ K, areNeighbours α G x y

-- A hypergraph is conformal when each of its (non-empty) cliques is included in an edge
def isConformal (α : Type) (G : ComputableHypergraph α) : Prop :=
  ∀ K : Finset α, K.Nonempty → isClique α G K → ∃ e ∈ G.hyperedges, K ⊆ e

-- Successor of i in the cyclic order 0 → 1 → ... → n-1 → 0
def cycleNext {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, by have := i.isLt; omega⟩

theorem cycleNext_val {n : Nat} (i : Fin n) :
    (cycleNext i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  unfold cycleNext; split <;> rfl

-- Edges of the usual graph cycle on t: {{t_i, t_{i+1}} | 1 ≤ i < n} ∪ {{t_n, t_1}}
def graphCycleEdges (α : Type) [DecidableEq α] {n : Nat} (t : Fin n → α) : Finset (Finset α) :=
  Finset.univ.image (fun i => ({t i, t (cycleNext i)} : Finset α))

-- A tuple (t_1, ..., t_n) of pairwise distinct vertices is a cycle of H when
-- M(H[{t_i | 1 ≤ i ≤ n}]) = {{t_i, t_{i+1}} | 1 ≤ i < n} ∪ {{t_n, t_1}}
structure HypergraphCycle (α : Type) [DecidableEq α] (G : ComputableHypergraph α) where
  n : Nat
  hn : n >= 3
  t : Fin n → α
  t_injective : Function.Injective t
  t_nodes : ∀ i : Fin n, t i ∈ G.nodes
  is_cycle : maximalEdges α (inducedEdges α G (Finset.univ.image t)) = graphCycleEdges α t

def isCycleFree (α : Type) [DecidableEq α] (G : ComputableHypergraph α) : Prop :=
  IsEmpty (HypergraphCycle α G)

-- A hypergraph is alpha acyclic iff it is both conformal and cycle-free
def alpha_acyclic_v2 (α : Type) [DecidableEq α] (G : ComputableHypergraph α) : Prop :=
  isConformal α G ∧ isCycleFree α G

----------------
-- Unit Tests --
----------------

-- Testing: findIsolatedVertices
def sampleHypergraph : ComputableHypergraph ℕ :=
  { nodes := {1, 2, 3},
    hyperedges := { {1, 2}, {2, 3}, {1, 3} } }

#eval findIsolatedVertices ℕ sampleHypergraph   -- Expected Output: ∅

-- Sample hypergraph with an isolated vertex
def sampleHypergraphWithIsolated : ComputableHypergraph ℕ :=
  { nodes := {1, 2, 3, 4, 5},
    hyperedges := { {1, 2}, {2, 3}, {4}, {5} } }

#eval findIsolatedVertices ℕ sampleHypergraphWithIsolated -- Expected Output: {1, 3, 4, 5}

def hgAfterRemoval := removeIsolatedVerticesAndEdges ℕ sampleHypergraphWithIsolated {1, 3, 4, 5}

#eval hgAfterRemoval.nodes -- Expected {2}
#eval hgAfterRemoval.hyperedges -- Expected {{2}}

def sampleHypergraphWithIncludedEdges : ComputableHypergraph ℕ :=
  { nodes := {1, 2, 3, 4, 5},
    hyperedges := { {1, 2}, {1, 2, 3}, {4}, {5}, {4, 5} } }

def hypergraphAfterRemoveIncludedEdges := removeIncludedHyperedges ℕ sampleHypergraphWithIncludedEdges
#eval hypergraphAfterRemoveIncludedEdges.hyperedges -- Expected Output: Hyperedge {{1, 2, 3}, {4, 5}} removed

#eval isAlphaAcylic ℕ sampleHypergraph -- Expected false

-------------------------
--   Correctness Test  --
-------------------------
#eval isAlphaAcylic ℕ braultBaronAHyperGraph   -- Expected true
#eval isAlphaAcylic ℕ braultBaronBHyperGraph   -- Expected true
#eval isAlphaAcylic ℕ braultBaronCHyperGraph   -- Expected true
#eval isAlphaAcylic ℕ braultBaronDHyperGraph   -- Expected false
#eval isAlphaAcylic ℕ braultBaronEHyperGraph   -- Expected false
#eval isAlphaAcylic ℕ braultBaronFHyperGraph   -- Expected false

-- alpha_acyclic_v2 is not vacuous: the triangle {01, 02, 12} (Brault-Baron Fig. 2f)
-- has the clique {0, 1, 2}, which lies in no edge, so it is not conformal
example : ¬ alpha_acyclic_v2 ℕ braultBaronFHyperGraph := by
  intro ⟨h_conf, _⟩
  obtain ⟨e, he, h_sub⟩ := h_conf {0, 1, 2} ⟨0, by decide⟩
    ⟨by decide, by unfold areNeighbours; decide⟩
  revert h_sub; revert e; decide
