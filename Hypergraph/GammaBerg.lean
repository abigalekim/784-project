import Hypergraph.Basic
import Hypergraph.Gamma
import Hypergraph.Berg
import Mathlib.Tactic.Contrapose
import Init.Classical
import Mathlib.Logic.IsEmpty

open Finset

def convert_gamma_to_berg_cycle (α : Type) (G : ComputableHypergraph α)
  (h : GammaCycle α G) : BergCycle α G := by
  let g : BergCycle α G := {
    n := h.n,
    hn := le_trans (by decide) h.hn,
    E := h.E,
    E_distinct := h.E_distinct,
    x := h.x,
    x_distinct := h.x_distinct,
    cond_1 := h.cond_1,
    cond_2 := h.cond_3
  }
  exact g

theorem converse_berg_implies_gamma {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (h : ¬ gamma_acyclic_v2 α G) : ¬ berg_acyclic_v2 α G := by
    have h_gamma_cycle := get_gamma_cycle α G h
    have h_berg_cycle := convert_gamma_to_berg_cycle α G h_gamma_cycle
    have convert_to_berg_acyclicity := convert_berg_contrapositive α G h_berg_cycle
    exact convert_to_berg_acyclicity

theorem berg_implies_gamma (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (h : berg_acyclic_v2 α G) : gamma_acyclic_v2 α G := by
  rw [berg_acyclic_v2, gamma_acyclic_v2] at *
  by_contra h_contra
  have h_not_berg : ¬IsEmpty (BergCycle α G) :=
    converse_berg_implies_gamma G h_contra
  have berg_cycle_instance : BergCycle α G :=
    Classical.choice (not_isEmpty_iff.mp h_not_berg)
  exact IsEmpty.elim h berg_cycle_instance
