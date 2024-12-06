import Hypergraph.Basic
import Hypergraph.Beta
import Hypergraph.Gamma
import Mathlib.Tactic.Contrapose
import Init.Classical
import Mathlib.Logic.IsEmpty

open Finset

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
    cond_3 := h.cond_3,
    cond_4 := h.cond_5,
    cond_5 := h.cond_6
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
  rw [gamma_acyclic_v2, beta_acyclic_v2] at *
  by_contra h_contra
  have h_not_gamma : ¬IsEmpty (GammaCycle α G) :=
    converse_gamma_implies_beta G h_contra
  have gamma_cycle_instance : GammaCycle α G :=
    Classical.choice (not_isEmpty_iff.mp h_not_gamma)
  exact IsEmpty.elim h gamma_cycle_instance
