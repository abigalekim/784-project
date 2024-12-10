import Hypergraph.Basic
import Hypergraph.TestGraphs
open Finset

structure BergCycle (α : Type) (G : ComputableHypergraph α) where
  n : Nat
  hn : n >= 2
  E : Fin n -> Finset α
  E_distinct : ∀ i j : Fin n, E i ≠ E j
  x : Fin n -> α
  x_distinct : ∀ i j : Fin n, x i ≠ x j
  cond_1 : ∀ i : Nat, (i_lt : i < n - 1) →
    x ⟨i,by omega⟩ ∈ E ⟨i,by omega⟩ ∧
    x ⟨i, by omega⟩ ∈ E ⟨i+1, by omega⟩
  cond_2 : x ⟨n - 1, by omega⟩ ∈ E ⟨n - 1, by omega⟩ ∧ x ⟨n - 1, by omega⟩ ∈ E ⟨0, by omega⟩

def berg_acyclic_v2 (α : Type) (G : ComputableHypergraph α) := IsEmpty (BergCycle α G)

def convert_berg_contrapositive (α : Type) (G : ComputableHypergraph α)
  (bc : BergCycle α G) : ¬berg_acyclic_v2 α G :=
  fun h => IsEmpty.elim h bc
