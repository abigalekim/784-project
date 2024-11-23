import Hypergraph.Basic
import Hypergraph.Alpha
import Hypergraph.TestGraphs

-----------
-- Alpha --
-----------
#eval gyoAlgorithm ℕ braultBaronAHyperGraph -- Expected true
#eval gyoAlgorithm ℕ braultBaronBHyperGraph -- Expected true
#eval gyoAlgorithm ℕ braultBaronCHyperGraph -- Expected true
#eval gyoAlgorithm ℕ braultBaronDHyperGraph -- Expected false
#eval gyoAlgorithm ℕ braultBaronEHyperGraph -- Expected false
#eval gyoAlgorithm ℕ braultBaronFHyperGraph -- Expected false

def main : IO Unit :=
  IO.println s!"Hello"
