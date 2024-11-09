import Hypergraph

def main : IO Unit :=
  let hg := Hypergraph.mk {1, 2, 3, 4} {{1, 2}, {3, 4}, {2, 3}}
  IO.println s!"Hello, {hello}!"
  -- IO.println s!"Hypergraph is acyclic: {isAcyclic hg}"
