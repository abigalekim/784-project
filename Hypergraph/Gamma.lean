import Hypergraph.Basic
import Hypergraph.TestGraphs
import Mathlib.Tactic.Linarith
open Finset

--set_option diagnostics true in
-- is a type where a set of edges and vertices and an x that can satisfy all these conditions
-- then there is an inhabitant of this type (there is a value of this type)
structure GammaCycle (α : Type) (G : ComputableHypergraph α) where
  n : Nat
  hn : n >= 3
  E : Fin n -> Finset α
  E_distinct : ∀ i j : Fin n, E i ≠ E j
  x : Fin n -> α
  x_distinct : ∀ i j : Fin n, x i ≠ x j
  cond_1 : ∀ i : Nat, ∀ j : Nat, (i_lt : i < n - 1 ∧ j < n ∧ j ≠ i ∧ j ≠ i + 1) →
    x ⟨i,by omega⟩ ∈ E ⟨i,by omega⟩ ∧
    x ⟨i, by omega⟩ ∈ E ⟨i+1, by omega⟩ ∧
    x ⟨i, by omega⟩ ∉ E ⟨j, by omega⟩
  cond_2 : x ⟨n - 1, by omega⟩ ∈ E ⟨n - 1, by omega⟩ ∧ x ⟨n - 1, by omega⟩ ∈ E ⟨0, by omega⟩
  cond_3: ∀ i : Fin n, E i ∈ (G.hyperedges : Finset (Finset α))
  cond_4: ∀ i : Fin n, x i ∈ (G.nodes : Finset α)

def gamma_acyclic_v2 (α : Type) (G : ComputableHypergraph α) := IsEmpty (GammaCycle α G)
def findVerticesNoHyperEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) :  Finset α :=
  let verticesInHyperedges : Finset α := hg.hyperedges.biUnion id
  hg.nodes \ verticesInHyperedges

def findVerticesOneHyperEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Finset α :=
  hg.nodes.filter (λ n => (hg.hyperedges.filter (λ e => n ∈ e)).card = 1)

def isGammaAcyclic (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
  let rec loop (g : ComputableHypergraph α) (iter : Nat) : ComputableHypergraph α :=
    match iter with
    | 0 => g
    | val + 1 =>
      let old_g := g
      let isolatedZeroVertices := findVerticesNoHyperEdge α g
      let isolatedOneVertices := findVerticesOneHyperEdge α g
      let isolatedVertices := isolatedOneVertices ∪ isolatedZeroVertices
      let noIsolatedHyperEdges := g.hyperedges.image (λ n => n \ isolatedOneVertices)
      let g : ComputableHypergraph α := { nodes := g.nodes \ isolatedVertices, hyperedges := noIsolatedHyperEdges }
      let g_size := g.hyperedges.card - 1
      let newHyperEdges := g.hyperedges.filter (λ e => (g.hyperedges.filter (λ f => (e ⊆ f ∨ e ∩ f = ∅) ∧ e ≠ f)).card = g_size)
      let newHyperEdges := g.hyperedges \ newHyperEdges
      let g := { nodes := g.nodes, hyperedges := newHyperEdges }

      if old_g = g then g else loop g val

  let maxIters : Nat := (hg.nodes.card + hg.hyperedges.card)
  let finalGraph := loop hg maxIters
  finalGraph.nodes = ∅

--------------------
-- Below are test --
--------------------
#eval isGammaAcyclic ℕ braultBaronAHyperGraph
#eval isGammaAcyclic ℕ braultBaronBHyperGraph
#eval isGammaAcyclic ℕ braultBaronCHyperGraph
#eval isGammaAcyclic ℕ braultBaronDHyperGraph
#eval isGammaAcyclic ℕ braultBaronEHyperGraph
#eval isGammaAcyclic ℕ braultBaronFHyperGraph
