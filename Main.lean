import Hypergraph.Basic

-- GYO algorithm --
def findIsolatedVertices [DecidableEq α] (hg : ComputableHypergraph α) : Finset α :=
  hg.nodes.filter (λ n => (hg.hyperedges.filter (λ e => n ∈ e)).card = 1)

def removeIsolatedVertex [DecidableEq α] (hg : ComputableHypergraph α) (v : α) : ComputableHypergraph α :=
  -- let updatedHyperedges : Finset (Finset α) := hg.hyperedges.image (λ e => e.erase v)
  let nonEmptyHyperedges : Finset (Finset α) := hg.hyperedges.filter (λ e => e.Nonempty)
  { nodes := hg.nodes.erase v,
    hyperedges := nonEmptyHyperedges }

-- def removeRedundantHyperedges [DecidableEq α] (hg : ComputableHypergraph α) : ComputableHypergraph α :=
--   let redundantEdges := hg.hyperedges.filter (λ e => hg.hyperedges.exists_coe (λ f => e < f))
--   { nodes := hg.nodes,
--     hyperedges := hg.hyperedges.filter (λ e => ¬redundantEdges.cons e) }

-- def gyoAlgorithm [DecidableEq α] (hg : ComputableHypergraph α) : Bool :=
--   let rec loop (g : ComputableHypergraph α) : ComputableHypergraph α :=
--     let isolated := findIsolatedVertices g
--     let g := isolated.fold (λ acc v => removeIsolatedVertex acc v) g
--     let gNew := removeRedundantHyperedges g
--     if gNew = g then g else loop gNew
--   let finalGraph := loop hg
--   finalGraph.nodes.empty

def main : IO Unit :=
  IO.println s!"Hello"
