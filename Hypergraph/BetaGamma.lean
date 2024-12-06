import Hypergraph.Basic
import Hypergraph.Beta
import Hypergraph.Gamma
import Mathlib.Tactic.Contrapose

open Finset

def convert_beta_contrapositive (α : Type) (G : ComputableHypergraph α)
  (bc : BetaCycle α G) : ¬beta_acyclic_v2 α G :=
  fun h => h bc

def convert_gamma_contrapositive (α : Type) (G : ComputableHypergraph α)
  (bc : GammaCycle α G) : ¬gamma_acyclic_v2 α G :=
  fun h => h bc

def get_beta_cycle (α : Type) (G : ComputableHypergraph α)
  (h : ¬ beta_acyclic_v2 α G) : BetaCycle α G := by sorry
  --have h_contra : ¬ (BetaCycle α G -> False) := by
  --  simp [*]
  --  exact h
  --Classical.choose h_contra

set_option diagnostics true
def convert_beta_to_gamma_cycle (α : Type) (G : ComputableHypergraph α)
  BetaCycle α G : GammaCycle α G := by sorry

theorem converse_gamma_implies_beta {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (h : ¬ beta_acyclic_v2 α G) : ¬ gamma_acyclic_v2 α G := by
    have h_beta_cycle := get_beta_cycle α G h
    have h_gamma_cycle := convert_beta_to_gamma_cycle α G h_beta_cycle
    have convert_to_gamma_acyclicity := convert_gamma_contrapositive α G h_gamma_cycle

theorem gamma_implies_beta (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (h : gamma_acyclic_v2 α G) : beta_acyclic_v2 α G := by
  intro h_contra
  have convert_h_contra := convert_beta_contrapositive α G h_contra
  have h_not_gamma : ¬ gamma_acyclic_v2 α G :=
    converse_gamma_implies_beta G convert_h_contra
  contradiction
