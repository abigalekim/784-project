import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic

open Finset

structure ComputableHypergraph (α : Type) [DecidableEq α] where
  nodes : Finset α
  hyperedges : Finset (Finset α)

def computableNumNodes {α : Type} [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.nodes.card

def computableNumHyperedges {α : Type} [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.hyperedges.card

def addNode [DecidableEq ℕ] (hg : ComputableHypergraph ℕ) (node : ℕ) : ComputableHypergraph ℕ :=
  { nodes := insert node hg.nodes,
    hyperedges := hg.hyperedges }

def createHyperedge {α : Type} [DecidableEq α] (nodes : List α) : Finset α :=
  nodes.foldr insert Finset.empty

def addEdge [DecidableEq ℕ] (hg : ComputableHypergraph ℕ) (edge : Finset ℕ) : ComputableHypergraph ℕ :=
  { nodes := hg.nodes,
    hyperedges := insert edge hg.hyperedges }

-- GYO algorithm --
def findIsolatedVertices [DecidableEq α] (hg : ComputableHypergraph α) : Finset α :=
  hg.nodes.filter (λ n => (hg.hyperedges.filter (λ e => n ∈ e)).card = 1)

def removeIsolatedVertex [DecidableEq α] (hg : ComputableHypergraph α) (v : α) : ComputableHypergraph α :=
  let updatedHyperedges : Finset (Finset α) := hg.hyperedges.image (λ e => e.erase v)
  let nonEmptyHyperedges : Finset (Finset α) := updatedHyperedges.filter (λ e => e.Nonempty)
  { nodes := hg.nodes.erase v,
    hyperedges := nonEmptyHyperedges }

-- def removeRedundantHyperedges [DecidableEq α] (hg : ComputableHypergraph α) : ComputableHypergraph α :=
--   let redundantEdges := hg.hyperedges.filter (λ e => hg.hyperedges.any (λ f => e < f))
--   { nodes := hg.nodes,
--     hyperedges := hg.hyperedges.filter (λ e => ¬redundantEdges.contains e) }

-- def gyoAlgorithm [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
--   let rec loop (g : ComputableHypergraph α) : ComputableHypergraph α :=
--     let isolated := findIsolatedVertices g
--     let g := isolated.fold (λ acc v => removeIsolatedVertex acc v) g
--     let gNew := removeRedundantHyperedges g
--     if gNew = g then g else loop gNew
--   let finalGraph := loop hg
--   finalGraph.nodes.empty

-- Below are test --

def initialHypergraph : ComputableHypergraph ℕ :=
  { nodes := Finset.range 6,  -- {0, 1, 2, 3, 4, 5}
    hyperedges := Finset.empty }

def updatedHypergraph1 : ComputableHypergraph ℕ :=
  addNode initialHypergraph 6  -- Adds node '6'

#eval computableNumNodes updatedHypergraph1      -- Outputs 6

def newEdge : Finset ℕ := createHyperedge [0, 1, 3, 5]  -- Assuming createHyperedge is defined
def updatedHypergraph2 : ComputableHypergraph ℕ :=
  addEdge updatedHypergraph1 newEdge  -- Adds edge {0, 1}

#eval computableNumHyperedges updatedHypergraph2 -- Outputs 1
