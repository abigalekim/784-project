import Hypergraph.Basic
import Hypergraph.Beta
import Hypergraph.Gamma
import Mathlib.Tactic.Contrapose

open Finset

def convert_beta_contrapositive {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (bc : BetaCycle α G) : ¬beta_acyclic_v2 α G :=
  fun h => h bc

def convert_gamma_contrapositive {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (bc : GammaCycle α G) : ¬gamma_acyclic_v2 α G :=
  fun h => h bc

--def get_beta_cycle {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
--  (h : ¬ beta_acyclic_v2 α G) : BetaCycle α G := by
--  have h_contra : ¬ (BetaCycle α G -> False) := by
--    simp [*]
--    exact h
--  Classical.choose h_contra

theorem converse_gamma_implies_beta {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (h : ¬ beta_acyclic_v2 α G) : ¬ gamma_acyclic_v2 α G := by sorry

theorem gamma_implies_beta {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (h : gamma_acyclic_v2 α G) : beta_acyclic_v2 α G := by
  intro h_contra
  have convert_h_contra := convert_beta_contrapositive G h_contra
  have h_not_gamma : ¬ gamma_acyclic_v2 α G :=
    converse_gamma_implies_beta G convert_h_contra
  contradiction
