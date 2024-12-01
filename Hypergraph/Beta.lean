import Hypergraph.Basic
import Hypergraph.TestGraphs
open Finset

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
