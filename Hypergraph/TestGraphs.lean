import Hypergraph.Basic
open Finset

----------------------------------------------
-- Generated Graphs from Brault-Baron paper --
----------------------------------------------
def braultBaronAHyperGraph : ComputableHypergraph ℕ :=
  { nodes := {0, 1, 2}, hyperedges := {{0, 1, 2}, {0, 1}}}

def braultBaronBHyperGraph : ComputableHypergraph ℕ :=
  { nodes := {0, 1, 2}, hyperedges := {{0, 1, 2}, {0, 2}, {1, 2}}}

def braultBaronCHyperGraph : ComputableHypergraph ℕ :=
  { nodes := {0, 1, 2}, hyperedges := {{0, 1, 2}, {0, 1}, {0, 2}, {1, 2}}}

def braultBaronDHyperGraph : ComputableHypergraph ℕ :=
  { nodes := {0, 1, 2}, hyperedges := {{0, 1, 2}, {0, 1, 3}, {1, 2, 3}, {0, 2, 3}}}

def braultBaronEHyperGraph : ComputableHypergraph ℕ :=
  { nodes := {0, 1, 2, 3}, hyperedges := {{0, 1}, {1, 2}, {2, 3}, {3, 0}}}

def braultBaronFHyperGraph : ComputableHypergraph ℕ :=
  { nodes := {0, 1, 2}, hyperedges := {{0, 1}, {0, 2}, {1, 2}}}
