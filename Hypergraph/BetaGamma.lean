import Hypergraph.Basic
import Hypergraph.Beta
import Hypergraph.Gamma
import Mathlib.Tactic.Contrapose
import Init.Classical

open Finset

def convert_beta_contrapositive (α : Type) (G : ComputableHypergraph α)
  (bc : BetaCycle α G) : ¬beta_acyclic_v2 α G :=
  fun h => h bc

def convert_gamma_contrapositive (α : Type) (G : ComputableHypergraph α)
  (bc : GammaCycle α G) : ¬gamma_acyclic_v2 α G :=
  fun h => h bc

def get_beta_cycle (α : Type) (G : ComputableHypergraph α)
  (h : ¬ beta_acyclic_v2 α G) : BetaCycle α G := by sorry
    --have there_exists_beta_cycle : (∃ c : BetaCycle α G, beta_acyclic_v2 α G) := by sorry
    --have beta_val := Classical.choice there_exists_beta_cycle
    --exact beta_val
    -- if ¬ beta_acyclic_v2 α G, then ¬(BetaCycle α G -> False)
    -- ¬(BetaCycle α G -> False) = BetaCycle α G -> True
    -- this implies the existence of BetaCycle α G

set_option diagnostics true
def convert_beta_to_gamma_cycle (α : Type) (G : ComputableHypergraph α)
  (h : BetaCycle α G) : GammaCycle α G := by
  let g : GammaCycle α G := {
    n := h.n,
    hn := h.hn,
    E := h.E,
    E_distinct := h.E_distinct,
    x := h.x,
    x_distinct := h.x_distinct,
    cond_1 := h.cond_1
    cond_2 := h.cond_2,
    cond_3 := h.cond_4,
    cond_4 := h.cond_5
  }
  exact g

theorem converse_gamma_implies_beta {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (h : ¬ beta_acyclic_v2 α G) : ¬ gamma_acyclic_v2 α G := by
    have h_beta_cycle := get_beta_cycle α G h
    have h_gamma_cycle := convert_beta_to_gamma_cycle α G h_beta_cycle
    have convert_to_gamma_acyclicity := convert_gamma_contrapositive α G h_gamma_cycle
    exact convert_to_gamma_acyclicity

theorem gamma_implies_beta (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (h : gamma_acyclic_v2 α G) : beta_acyclic_v2 α G := by
  intro h_contra
  have convert_h_contra := convert_beta_contrapositive α G h_contra
  have h_not_gamma : ¬ gamma_acyclic_v2 α G :=
    converse_gamma_implies_beta G convert_h_contra
  contradiction
