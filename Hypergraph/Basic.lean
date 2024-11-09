import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic

structure ComputableHypergraph (α : Type) [DecidableEq α] where
  nodes : Finset α
  hyperedges : Finset (Finset α)

def computableNumNodes {α : Type} [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.nodes.card

def computableNumHyperedges {α : Type} [DecidableEq α] (hg : ComputableHypergraph α) : Nat :=
  hg.hyperedges.card

variable [DecidableEq ℕ]

def exampleHypergraph : ComputableHypergraph ℕ :=
  { nodes := Finset.range 6,  -- {0, 1, 2, 3, 4, 5}
    hyperedges := insert (insert 0 (insert 1 (insert 2 Finset.empty))) Finset.empty}  -- {{0, 1, 2}}

#eval computableNumNodes exampleHypergraph      -- Outputs 6
#eval computableNumHyperedges exampleHypergraph -- Outputs 1
