import Hypergraph.Basic
import Hypergraph.TestGraphs
open Finset

structure BetaCycle (α : Type) (G : ComputableHypergraph α) where
  n : Nat
  hn : n >= 3
  E : Fin n -> Finset α
  E_distinct : ∀ i j : Fin n, E i ≠ E j
  x : Fin n -> α
  x_distinct : ∀ i j : Fin n, x i ≠ x j
  cond_1:  ∀ i : Nat, (i_lt : i < n - 1) →
    x ⟨i,by omega⟩ ∈ E ⟨i,by omega⟩ ∧
    x ⟨i, by omega⟩ ∈ E ⟨i+1, by omega⟩
  cond_2 : ∀ i : Nat, ∀ j : Nat, (i_lt : i < n - 1 ∧ j < n ∧ j ≠ i ∧ j ≠ i + 1) →
    x ⟨i, by omega⟩ ∉ E ⟨j, by omega⟩
  cond_3 : x ⟨n - 1, by omega⟩ ∈ E ⟨n - 1, by omega⟩ ∧
    x ⟨n - 1, by omega⟩ ∈ E ⟨0, by omega⟩
  cond_4: ∀ j : Nat, (j_cond : j < n ∧ j ≠ n - 1 ∧ j ≠ 0) →  x ⟨n - 1, by omega⟩ ∉ E ⟨j, by omega⟩
  cond_5: ∀ i : Fin n, E i ∈ (G.hyperedges : Finset (Finset α))
  cond_6: ∀ i : Fin n, x i ∈ (G.nodes : Finset α)

def beta_acyclic_v2 (α : Type) (G : ComputableHypergraph α) := IsEmpty (BetaCycle α G)

def convert_beta_contrapositive (α : Type) (G : ComputableHypergraph α)
  (bc : BetaCycle α G) : ¬beta_acyclic_v2 α G :=
  fun h => IsEmpty.elim h bc

noncomputable def get_beta_cycle (α : Type) (G : ComputableHypergraph α)
  (h : ¬ beta_acyclic_v2 α G) : BetaCycle α G := by
    rw [beta_acyclic_v2] at h
    have non_empty_beta_acyclic : Nonempty (BetaCycle α G) := not_isEmpty_iff.mp h
    have result := Classical.choice non_empty_beta_acyclic
    exact result

def findVerticesNestEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Finset α :=
  hg.nodes.filter (λ n =>
    let edges := hg.hyperedges.filter (λ e => n ∈ e)
    (edges.filter (λ e =>
      let exclude_self := edges \ {e}
      exclude_self.Nonempty &&
      ∀ other ∈ exclude_self, (e ⊆ other || other ⊆ e))).card = edges.card
    )

def isBetaAcyclic (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
  let rec loop (g : ComputableHypergraph α) (iter : Nat) : ComputableHypergraph α :=
    match iter with
    | 0 => g
    | val + 1 =>
      let old_g := g
      -- remove vertices contained by nested edges
      let nestedEdgeVertices := findVerticesNestEdge α g
      let noNestedEdges := g.hyperedges.image (λ n => n \ nestedEdgeVertices)
      let g : ComputableHypergraph α := { nodes := g.nodes \ nestedEdgeVertices, hyperedges := noNestedEdges }
      -- remove empty hyperedges or singleton edges
      let newHyperEdges := g.hyperedges.filter (λ e => e.card > 1)
      let g := { nodes := g.nodes, hyperedges := newHyperEdges }

      if old_g = g then g else loop g val

  let maxIters : Nat := (hg.nodes.card + hg.hyperedges.card)
  let finalGraph := loop hg maxIters
  finalGraph.nodes = ∅

--------------------
-- Below are test --
--------------------
#eval isBetaAcyclic ℕ braultBaronAHyperGraph
#eval isBetaAcyclic ℕ braultBaronBHyperGraph
#eval isBetaAcyclic ℕ braultBaronCHyperGraph
#eval isBetaAcyclic ℕ braultBaronDHyperGraph
#eval isBetaAcyclic ℕ braultBaronEHyperGraph
#eval isBetaAcyclic ℕ braultBaronFHyperGraph
