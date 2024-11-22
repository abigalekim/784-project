import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Init.Prelude

open Finset

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
  { nodes := insert node hg.nodes,
    hyperedges := hg.hyperedges }

-- Helper function: create hyperedge
-- DecidableEq is essential for equality comparasion
def createHyperedge (α : Type) [DecidableEq α] (nodes : List α) : Finset α :=
  nodes.foldr insert Finset.empty

-- Helper function: add edge into hypergraph
-- DecidableEq is essential for equality comparasion
def addEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) (edge : Finset α) : ComputableHypergraph α :=
  { nodes := hg.nodes,
    hyperedges := insert edge hg.hyperedges }

-- Debug function: used for check nodes number
def computableNumNodes (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.nodes.card

-- Debug function: used for check edges number
def computableNumHyperedges (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.hyperedges.card

--------------------
-- Below are test --
--------------------

def initialHypergraph : ComputableHypergraph ℕ :=
  { nodes := Finset.range 6,  -- {0, 1, 2, 3, 4, 5}
    hyperedges := Finset.empty }

def updatedHypergraph1 : ComputableHypergraph ℕ :=
  addNode ℕ initialHypergraph 6  -- Adds node '6'

#eval computableNumNodes ℕ updatedHypergraph1   -- Outputs 7

def newEdge : Finset ℕ := createHyperedge ℕ [0, 1, 3, 5]
def updatedHypergraph2 : ComputableHypergraph ℕ :=
  addEdge ℕ updatedHypergraph1 newEdge  -- Adds edge {0, 1, 3, 5}

#eval computableNumHyperedges ℕ updatedHypergraph2 -- Outputs 1
