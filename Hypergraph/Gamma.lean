import Hypergraph.Basic
open Finset

def findVerticesNoHyperEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) :  Finset α :=
  let verticesInHyperedges : Finset α := hg.hyperedges.biUnion id
  hg.nodes \ verticesInHyperedges

def findVerticesOneHyperEdge (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Finset α :=
  hg.nodes.filter (λ n => (hg.hyperedges.filter (λ e => n ∈ e)).card = 1)

def isGamma (α : Type) [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
  let rec loop (g : ComputableHypergraph α) : ComputableHypergraph α :=
    let old_g := g
    let isolatedZeroVertices := findVerticesNoHyperEdge g
    let isolatedOneVertices := findVerticesOneHyperEdge g
    let isolatedVertices := isolatedOneVertices ∪ isolatedZeroVertices
    let noIsolatedHyperEdges := g.hyperedges.map (λ n => n \ isolatedOneVertices)
    let g := { nodes := g.nodes \ isolatedVertices, hyperedges := noIsolatedHyperEdges }
    let newHyperEdges := g.hyperedges.filter (λ e => (g.hyperedges.filter (λ f =>  e ⊆ f ∨ e ∩ f ≠ ∅)).card >= 1)
    let g := { nodes := g.nodes, hyperedges := newHyperEdges }

    if old_g = g then g else loop g

  let finalGraph := loop hg
  finalGraph.nodes = ∅
