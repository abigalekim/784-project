import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Init.Prelude

-- Definition: computable hypergraph
-- DecidableEq is essential for equality comparasion
structure ComputableHypergraph (α : Type) where
  nodes : Finset α
  hyperedges : Finset (Finset α)
deriving DecidableEq

#check instDecidableEqComputableHypergraph

-- Helper function: add node into hypergraph
-- DecidableEq is essential for equality comparasion
-- (α : Type) means we ask users explicitly give the node type
def addNode (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) (node : α) : ComputableHypergraph α :=
  { nodes := node :: hg.nodes,
    hyperedges := hg.hyperedges }

-- Helper function: add edge into hypergraph
-- DecidableEq is essential for equality comparasion
def addEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) (edge : List α) : ComputableHypergraph α :=
  { nodes := hg.nodes,
    hyperedges := edge :: hg.hyperedges }

-- Helper function: equality
def hypergraphEqual {α : Type} [DecidableEq α] (g1 g2 : ComputableHypergraph α) : Bool :=
  g1.nodes = g2.nodes ∧ g1.hyperedges = g2.hyperedges


-- Debug function: used for check nodes number
def computableNumNodes (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.nodes.length

-- Debug function: used for check edges number
def computableNumHyperedges (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.hyperedges.length

--------------------
-- Below are test --
--------------------

def initialHypergraph : ComputableHypergraph ℕ :=
  { nodes := [0, 1, 2, 3, 4, 5],  -- {0, 1, 2, 3, 4, 5}
    hyperedges := [] }

def updatedHypergraph1 : ComputableHypergraph ℕ :=
  addNode ℕ initialHypergraph 6  -- Adds node '6'

#eval computableNumNodes ℕ updatedHypergraph1   -- Outputs 7

def updatedHypergraph2 : ComputableHypergraph ℕ :=
  addEdge ℕ updatedHypergraph1 [0, 1, 3, 5]  -- Adds edge {0, 1, 3, 5}

#eval computableNumHyperedges ℕ updatedHypergraph2 -- Outputs 1
