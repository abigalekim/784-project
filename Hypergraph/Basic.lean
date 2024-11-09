import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Pairwise.Basic

structure Hypergraph (α : Type) where
  nodes : Set α
  hyperedges : Set (Set α)

def setsIntersect {α : Type} (s1 s2 : Set α) : Prop :=
  (s1 ∩ s2).Nonempty

-- def isAcyclic {α : Type} [DecidableEq α] (hg : Hypergraph α) : Bool :=
--   hg.hyperedges.Pairwise (λ e1 e2 => ¬ setsIntersect e1 e2)

def hello := "world"
