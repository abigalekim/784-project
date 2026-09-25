import Hypergraph.Basic
import Hypergraph.Alpha
import Hypergraph.Beta
import Mathlib.Tactic.PushNeg
import Init.Classical
import Mathlib.Logic.IsEmpty
open Finset

-- Beta acyclicity implies alpha acyclicity (Brault-Baron, arXiv:1403.7076).
-- Alpha acyclic = conformal ∧ cycle-free, so we show, by contrapositive, that
-- both a cycle and a non-conformal clique yield a beta cycle.

------------------------------------------
-- A cycle of the hypergraph is a β-cycle --
------------------------------------------

-- Given a cycle t, pick for each i an edge E_i with E_i ∩ T = {t_i, t_{i+1}}.
-- Then (E_0, t_1, E_1, t_2, ..., E_{n-1}, t_0) is a beta cycle.
noncomputable def convert_cycle_to_beta_cycle (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (c : HypergraphCycle α G) : BetaCycle α G := by
  let T := Finset.univ.image c.t
  have h_edge : ∀ i : Fin c.n, ∃ e ∈ G.hyperedges, e ∩ T = {c.t i, c.t (cycleNext i)} := by
    intro i
    have h_mem : ({c.t i, c.t (cycleNext i)} : Finset α) ∈ graphCycleEdges α c.t :=
      mem_image_of_mem _ (mem_univ i)
    rw [← c.is_cycle] at h_mem
    have h_induced := (mem_filter.mp (mem_filter.mp h_mem).1).1
    obtain ⟨e, he, h_trace⟩ := mem_image.mp h_induced
    exact ⟨e, he, h_trace⟩
  choose E hE h_trace using h_edge
  -- t_k lies in E_j exactly when k is one of the two endpoints j, j+1
  have key : ∀ k j : Fin c.n, c.t k ∈ E j ↔ (k.val = j.val ∨ k.val = (cycleNext j).val) := by
    intro k j
    have hT : c.t k ∈ T := mem_image_of_mem _ (mem_univ k)
    rw [← Fin.ext_iff, ← Fin.ext_iff]
    constructor
    · intro h
      have h' : c.t k ∈ E j ∩ T := mem_inter.mpr ⟨h, hT⟩
      rw [h_trace j, mem_insert, mem_singleton] at h'
      rcases h' with h' | h'
      · exact Or.inl (c.t_injective h')
      · exact Or.inr (c.t_injective h')
    · intro h
      have h' : c.t k ∈ E j ∩ T := by
        rw [h_trace j]
        rcases h with rfl | rfl <;> simp
      exact (mem_inter.mp h').1
  have hn := c.hn
  exact {
    n := c.n,
    hn := c.hn,
    E := E,
    E_distinct := by
      intro i j h_ne h_eq
      have h_ne' : i.val ≠ j.val := fun h => h_ne (Fin.ext h)
      have h1 := (key i j).mp (h_eq ▸ (key i i).mpr (Or.inl rfl))
      have h2 := (key j i).mp (h_eq ▸ (key j j).mpr (Or.inl rfl))
      simp only [cycleNext_val] at h1 h2
      have := i.isLt; have := j.isLt
      split_ifs at h1 h2 <;> omega,
    x := fun i => c.t (cycleNext i),
    x_distinct := by
      intro i j h_ne h_eq
      have h := congrArg Fin.val (c.t_injective h_eq)
      have h_ne' : i.val ≠ j.val := fun h => h_ne (Fin.ext h)
      simp only [cycleNext_val] at h
      have := i.isLt; have := j.isLt
      split_ifs at h <;> omega,
    cond_1 := by
      intro i hi
      simp only [key, cycleNext_val, or_true, true_or, true_and, and_true]
      split_ifs <;> (try simp only [or_false, false_or, or_true, true_or, not_or]) <;> omega,
    cond_2 := by
      intro i j ⟨hi, hj, hji, hji'⟩
      simp only [key, cycleNext_val, or_true, true_or, true_and, and_true]
      split_ifs <;> (try simp only [or_false, false_or, or_true, true_or, not_or]) <;> omega,
    cond_3 := by
      simp only [key, cycleNext_val, or_true, true_or, true_and, and_true]
      split_ifs <;> (try simp only [or_false, false_or, or_true, true_or, not_or]) <;> omega,
    cond_4 := by
      intro j ⟨hj, hj', hj''⟩
      simp only [key, cycleNext_val, or_true, true_or, true_and, and_true]
      split_ifs <;> (try simp only [or_false, false_or, or_true, true_or, not_or]) <;> omega,
    cond_5 := hE,
    cond_6 := fun i => c.t_nodes _
  }

theorem cycle_free_of_beta_acyclic (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (h : beta_acyclic_v2 α G) : isCycleFree α G :=
  ⟨fun c => IsEmpty.elim h (convert_cycle_to_beta_cycle α G c)⟩

----------------------------------------------------
-- A non-conformal hypergraph contains a β-cycle  --
----------------------------------------------------

-- Take a clique K of minimal size that is not included in any edge (Characterization 1).
-- It has three distinct vertices x, y, z, and for each w ∈ K some edge e_w satisfies
-- K \ {w} ⊆ e_w and w ∉ e_w. Then (e_x, z, e_y, x, e_z, y) is a beta cycle.
theorem conformal_of_beta_acyclic (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (h : beta_acyclic_v2 α G) : isConformal α G := by
  classical
  by_contra h_nc
  let bad : Finset α → Prop := fun K =>
    K.Nonempty ∧ isClique α G K ∧ ∀ e ∈ G.hyperedges, ¬ K ⊆ e
  have h_ex : ∃ m, ∃ K, K.card = m ∧ bad K := by
    unfold isConformal at h_nc
    push_neg at h_nc
    obtain ⟨K, hK, hc, hK'⟩ := h_nc
    exact ⟨K.card, K, rfl, hK, hc, hK'⟩
  obtain ⟨K, hK_card, hK_ne, ⟨hK_nodes, hK_clique⟩, hK_not_sub⟩ := Nat.find_spec h_ex
  -- Removing any vertex w from K (keeping it non-empty) yields a clique inside some edge avoiding w
  have h_erase : ∀ w ∈ K, ∀ u ∈ K, u ≠ w → ∃ e ∈ G.hyperedges, K.erase w ⊆ e ∧ w ∉ e := by
    intro w hw u hu huw
    have h_sub : ∃ e ∈ G.hyperedges, K.erase w ⊆ e := by
      by_contra h_none
      push_neg at h_none
      have h_bad : bad (K.erase w) :=
        ⟨⟨u, mem_erase.mpr ⟨huw, hu⟩⟩,
         ⟨(erase_subset w K).trans hK_nodes,
          fun x hx y hy => hK_clique x (mem_of_mem_erase hx) y (mem_of_mem_erase hy)⟩,
         h_none⟩
      have h_le := Nat.find_min' h_ex ⟨K.erase w, rfl, h_bad⟩
      have h_lt := card_erase_lt_of_mem hw
      omega
    obtain ⟨e, he, h_sub⟩ := h_sub
    refine ⟨e, he, h_sub, fun hwe => hK_not_sub e he ?_⟩
    intro v hv
    by_cases hvw : v = w
    · exact hvw ▸ hwe
    · exact h_sub (mem_erase.mpr ⟨hvw, hv⟩)
  -- Find three distinct vertices of K
  obtain ⟨x, hx⟩ := hK_ne
  obtain ⟨e0, he0, hxe0, -⟩ := hK_clique x hx x hx
  obtain ⟨y, hy, hye0⟩ := not_subset.mp (hK_not_sub e0 he0)
  have hxy : x ≠ y := fun h => hye0 (h ▸ hxe0)
  obtain ⟨e1, he1, hxe1, hye1⟩ := hK_clique x hx y hy
  obtain ⟨z, hz, hze1⟩ := not_subset.mp (hK_not_sub e1 he1)
  have hxz : x ≠ z := fun h => hze1 (h ▸ hxe1)
  have hyz : y ≠ z := fun h => hze1 (h ▸ hye1)
  obtain ⟨ex, hex, hex_sub, hx_ex⟩ := h_erase x hx y hy hxy.symm
  obtain ⟨ey, hey, hey_sub, hy_ey⟩ := h_erase y hy x hx hxy
  obtain ⟨ez, hez, hez_sub, hz_ez⟩ := h_erase z hz x hx hxz
  have hy_ex : y ∈ ex := hex_sub (mem_erase.mpr ⟨hxy.symm, hy⟩)
  have hz_ex : z ∈ ex := hex_sub (mem_erase.mpr ⟨hxz.symm, hz⟩)
  have hx_ey : x ∈ ey := hey_sub (mem_erase.mpr ⟨hxy, hx⟩)
  have hz_ey : z ∈ ey := hey_sub (mem_erase.mpr ⟨hyz.symm, hz⟩)
  have hx_ez : x ∈ ez := hez_sub (mem_erase.mpr ⟨hxz, hx⟩)
  have hy_ez : y ∈ ez := hez_sub (mem_erase.mpr ⟨hyz, hy⟩)
  have hexy : ex ≠ ey := fun h => hx_ex (h ▸ hx_ey)
  have hexz : ex ≠ ez := fun h => hx_ex (h ▸ hx_ez)
  have heyz : ey ≠ ez := fun h => hy_ey (h ▸ hy_ez)
  let E : Fin 3 → Finset α := fun i => if i.val = 0 then ex else if i.val = 1 then ey else ez
  let v : Fin 3 → α := fun i => if i.val = 0 then z else if i.val = 1 then x else y
  let bc : BetaCycle α G := {
    n := 3,
    hn := by decide,
    E := E,
    E_distinct := by
      intro i j h_ne
      rcases i with ⟨_ | _ | _ | i, hi⟩ <;> rcases j with ⟨_ | _ | _ | j, hj⟩ <;> (try omega) <;>
        simp_all [E, Ne.symm]
    x := v,
    x_distinct := by
      intro i j h_ne
      rcases i with ⟨_ | _ | _ | i, hi⟩ <;> rcases j with ⟨_ | _ | _ | j, hj⟩ <;> (try omega) <;>
        simp_all [v, Ne.symm]
    cond_1 := by
      intro i hi
      rcases i with _ | _ | i <;> (try omega) <;> simp [E, v, *],
    cond_2 := by
      intro i j ⟨hi, hj, hji, hji'⟩
      rcases i with _ | _ | i <;> rcases j with _ | _ | _ | j <;> (try omega) <;> simp_all [E, v],
    cond_3 := by simp [E, v, *],
    cond_4 := by
      intro j ⟨hj, hj', hj''⟩
      rcases j with _ | _ | _ | j <;> (try omega) <;> simp_all [E, v],
    cond_5 := by
      intro i
      rcases i with ⟨_ | _ | _ | i, hi⟩ <;> (try omega) <;> simp [E, *],
    cond_6 := by
      intro i
      rcases i with ⟨_ | _ | _ | i, hi⟩ <;> (try omega) <;>
        simp [v, hK_nodes hx, hK_nodes hy, hK_nodes hz]
  }
  exact IsEmpty.elim h bc

-----------------------------
-- Beta implies alpha      --
-----------------------------

theorem beta_implies_alpha (α : Type) [DecidableEq α] (G : ComputableHypergraph α)
  (h : beta_acyclic_v2 α G) : alpha_acyclic_v2 α G :=
  ⟨conformal_of_beta_acyclic α G h, cycle_free_of_beta_acyclic α G h⟩

theorem converse_beta_implies_alpha {α : Type} [DecidableEq α] (G : ComputableHypergraph α)
  (h : ¬ alpha_acyclic_v2 α G) : ¬ beta_acyclic_v2 α G :=
  fun hb => h (beta_implies_alpha α G hb)
