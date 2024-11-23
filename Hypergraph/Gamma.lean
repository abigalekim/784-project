import Hypergraph.Basic
import Hypergraph.TestGraphs
open Finset

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
      let newHyperEdges := g.hyperedges.filter (λ e => (g.hyperedges.filter (λ f =>  e ⊆ f ∨ e ∩ f ≠ ∅)).card >= 1)
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
