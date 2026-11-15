/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Open additive maps with bounded lifts

An additive map between seminormed groups is open if every element has a preimage
whose norm is bounded by a fixed multiple of its norm (`TauCeti.isOpenMap_of_exists_norm_le`), and
is an open quotient map when it is also continuous (`TauCeti.isOpenQuotientMap_of_exists_norm_le`).
Neither completeness nor a Banach hypothesis is required. When the target is a normed group,
`(1 + ε)`-sharp approximate preimages give uniform `2`-bounded preimages
(`TauCeti.exists_norm_le_two_mul_of_forall_pos_exists_norm_le_add`).
-/

public section

namespace TauCeti

/-- An additive map between seminormed groups with uniformly norm-bounded lifts is open. -/
theorem isOpenMap_of_exists_norm_le {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [SeminormedAddGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ}
    (h : ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ K * ‖y‖) : IsOpenMap f := by
  let L := max K 1
  have hL : 0 < L := lt_max_of_lt_right one_pos
  intro U hU
  rw [Metric.isOpen_iff] at hU ⊢
  rintro _ ⟨x, hxU, rfl⟩
  obtain ⟨r, hr, hrU⟩ := hU x hxU
  refine ⟨r / L, div_pos hr hL, fun y hy => ?_⟩
  obtain ⟨z, hz, hzn⟩ := h (-f x + y)
  refine ⟨x + z, hrU ?_, by rw [map_add, hz, add_neg_cancel_left]⟩
  have hy' : ‖-f x + y‖ < r / L := by
    rw [← dist_eq_norm_neg_add]
    exact Metric.mem_ball'.1 hy
  rw [Metric.mem_ball', dist_eq_norm_neg_add, neg_add_cancel_left]
  calc ‖z‖ ≤ L * ‖-f x + y‖ :=
      hzn.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (norm_nonneg _))
    _ < r := by simpa only [mul_comm] using (lt_div_iff₀ hL).mp hy'

/-- A continuous additive map between seminormed groups with uniformly norm-bounded lifts is an
open quotient map. -/
theorem isOpenQuotientMap_of_exists_norm_le {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [SeminormedAddGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] {f : 𝓕} (hf : Continuous f) {K : ℝ}
    (h : ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ K * ‖y‖) : IsOpenQuotientMap f :=
  ⟨fun y ↦ let ⟨x, hx, _⟩ := h y; ⟨x, hx⟩, hf, isOpenMap_of_exists_norm_le f h⟩

/-- If every element of a normed group `F` admits preimages along a zero-preserving map `f` of norm
at most `‖y‖ + ε` for every `ε > 0`, then every element admits a preimage of norm at most
`2 * ‖y‖`. -/
theorem exists_norm_le_two_mul_of_forall_pos_exists_norm_le_add {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [NormedAddGroup F] [FunLike 𝓕 E F] [ZeroHomClass 𝓕 E F] {f : 𝓕}
    (h : ∀ y, ∀ ε > 0, ∃ x, f x = y ∧ ‖x‖ ≤ ‖y‖ + ε) (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ 2 * ‖y‖ := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy], by simp⟩
  · obtain ⟨x, hx, hn⟩ := h y ‖y‖ (norm_pos_iff.mpr hy)
    exact ⟨x, hx, hn.trans_eq (two_mul ‖y‖).symm⟩

end TauCeti
