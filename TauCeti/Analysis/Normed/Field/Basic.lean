/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.Order.IntermediateValue

/-!
# Separating radii by norms of a nontrivially normed field, and solving norm equations

In a nontrivially normed field `𝕜` the norms need not be dense, so two radii `0 < r < s` need not
be separated by the norm of an element of `𝕜`. They are separated after raising to a power:
`NormedField.exists_pow_lt_norm_lt_pow` gives `m : ℕ` and `c : 𝕜` with `rᵐ < ‖c‖ < sᵐ`. Compare
`NormedField.exists_lt_norm_lt`, which separates the radii themselves in a densely normed field.
Over an algebraically closed field `m`-th roots exist, so the radii themselves are separated:
`NormedField.exists_lt_norm_lt_of_isAlgClosed`. Iterating, the norms of a sequence decrease
strictly inside any interval `(r, s)`: `NormedField.exists_strictAnti_norm_mem_Ioo_of_isAlgClosed`.

The same roots solve norm equations: over an algebraically closed normed field, for a multiset `s`
containing `0` and any `c`, some `d` has `∏_{a ∈ s} max ‖d‖ ‖a‖ = ‖c‖`
(`NormedField.exists_prod_map_max_norm_eq_of_isAlgClosed`). For a nonarchimedean norm the left
side is the Gauss norm at radius `‖d‖` of the polynomial with roots `s`, so `‖d‖` is a radius at
which that Gauss norm equals `‖c‖`.
-/

public section

namespace NormedField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- **Two radii `0 < r < s` are separated by a norm after raising to a power**: there are `m : ℕ`
and `c : 𝕜` with `rᵐ < ‖c‖ < sᵐ`. -/
theorem exists_pow_lt_norm_lt_pow {r s : ℝ} (hr₀ : 0 < r) (hlt : r < s) :
    ∃ (m : ℕ) (c : 𝕜), r ^ m < ‖c‖ ∧ ‖c‖ < s ^ m := by
  -- choose `m` with `‖k‖ < (s / r)ᵐ` and `c` in the shell `sᵐ / ‖k‖ ≤ ‖c‖ < sᵐ`
  obtain ⟨k, hk⟩ := exists_one_lt_norm 𝕜
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖k‖ ((one_lt_div hr₀).mpr hlt)
  obtain ⟨c, -, hcs, hcr, -⟩ :=
    rescale_to_shell hk (pow_pos (hr₀.trans hlt) m) (one_ne_zero' 𝕜)
  rw [smul_eq_mul, mul_one] at hcs hcr
  refine ⟨m, c, lt_of_lt_of_le ?_ hcr, hcs⟩
  rw [lt_div_iff₀ (one_pos.trans hk), ← lt_div_iff₀' (pow_pos hr₀ m), ← div_pow]
  exact hm

/-- **The norms of an algebraically closed nontrivially normed field are dense**: two radii
`0 ≤ r < s` are separated by the norm of an element. This is the conclusion of
`NormedField.exists_lt_norm_lt` without a `DenselyNormedField` instance. -/
theorem exists_lt_norm_lt_of_isAlgClosed [IsAlgClosed 𝕜] {r s : ℝ} (hr₀ : 0 ≤ r) (hlt : r < s) :
    ∃ c : 𝕜, r < ‖c‖ ∧ ‖c‖ < s := by
  -- separate a positive radius `r' ≥ r` from `s`, so that `r = 0` needs no special case
  have hr' : 0 < max r (s / 2) := lt_max_of_lt_right (by linarith)
  have hlt' : max r (s / 2) < s := max_lt hlt (by linarith)
  obtain ⟨m, c, hm, hc⟩ := exists_pow_lt_norm_lt_pow 𝕜 hr' hlt'
  have hm₀ : m ≠ 0 := by
    rintro rfl
    exact (hm.trans hc).ne (by simp)
  obtain ⟨d, rfl⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hm₀)
  rw [norm_pow] at hm hc
  exact ⟨d, (le_max_left _ _).trans_lt ((pow_lt_pow_iff_left₀ hr'.le (norm_nonneg d) hm₀).mp hm),
    (pow_lt_pow_iff_left₀ (norm_nonneg d) (hr'.trans hlt').le hm₀).mp hc⟩

/-- **The norms of an algebraically closed nontrivially normed field contain a strictly decreasing
sequence in any interval** `(r, s)` with `0 ≤ r < s`. -/
theorem exists_strictAnti_norm_mem_Ioo_of_isAlgClosed [IsAlgClosed 𝕜] {r s : ℝ} (hr₀ : 0 ≤ r)
    (hlt : r < s) : ∃ c : ℕ → 𝕜, StrictAnti (fun n ↦ ‖c n‖) ∧ ∀ n, ‖c n‖ ∈ Set.Ioo r s := by
  -- `next y` has norm strictly between `r` and `‖y‖` whenever `r < ‖y‖`
  have hnext (y : 𝕜) : ∃ z : 𝕜, r < ‖y‖ → r < ‖z‖ ∧ ‖z‖ < ‖y‖ := by
    by_cases hy : r < ‖y‖
    · obtain ⟨z, hz⟩ := exists_lt_norm_lt_of_isAlgClosed 𝕜 hr₀ hy
      exact ⟨z, fun _ ↦ hz⟩
    · exact ⟨0, fun h ↦ (hy h).elim⟩
  choose next hnext using hnext
  obtain ⟨c₀, hc₀⟩ := exists_lt_norm_lt_of_isAlgClosed 𝕜 hr₀ hlt
  have hmem (n : ℕ) : r < ‖next^[n] c₀‖ ∧ ‖next^[n] c₀‖ < s := by
    induction n with
    | zero => exact hc₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨(hnext _ ih.1).1, (hnext _ ih.1).2.trans ih.2⟩
  refine ⟨fun n ↦ next^[n] c₀, strictAnti_nat_of_succ_lt fun n ↦ ?_, hmem⟩
  simpa only [Function.iterate_succ_apply'] using (hnext _ (hmem n).1).2

/-- **Solving `∏_{a ∈ s} max ‖d‖ ‖a‖ = ‖c‖` over an algebraically closed field**: if `0 ∈ s`, then
for every `c` some `d` satisfies this equation. For a nonarchimedean norm its left side is the
Gauss norm at radius `‖d‖` of the polynomial `∏_{a ∈ s} (T - a)`, so `‖d‖` is a radius at which
that Gauss norm equals `‖c‖`. -/
theorem exists_prod_map_max_norm_eq_of_isAlgClosed {𝕜 : Type*} [NormedField 𝕜] [IsAlgClosed 𝕜]
    {s : Multiset 𝕜} (hs : 0 ∈ s) (c : 𝕜) :
    ∃ d : 𝕜, (s.map fun a ↦ max ‖d‖ ‖a‖).prod = ‖c‖ := by
  set φ : ℝ → ℝ := fun t ↦ (s.map fun a ↦ max t ‖a‖).prod with hφ
  have hφ₀ : φ 0 = 0 :=
    Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨0, hs, by simp⟩)
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, by rw [norm_zero]; exact hφ₀⟩
  -- a real solution `r > 0` exists by the intermediate value theorem; at `r` the left side is
  -- `r ^ m ‖∏_{‖a‖ > r} a‖` with `m ≥ 1`, so `r` is the norm of an `m`-th root in `𝕜`
  -- `φ` is continuous, vanishes at `0` and is at least `t` for `t ≥ 1`
  have hcont : Continuous φ :=
    continuous_multiset_prod _ fun a _ ↦ continuous_id.max continuous_const
  set t₁ := max 1 ‖c‖
  have ht₁ : ‖c‖ ≤ φ t₁ := by
    have hcard : Multiset.card s ≠ 0 := (Multiset.card_pos_iff_exists_mem.mpr ⟨0, hs⟩).ne'
    calc ‖c‖ ≤ t₁ := le_max_right _ _
      _ ≤ t₁ ^ Multiset.card s := le_self_pow₀ (le_max_left _ _) hcard
      _ = (s.map fun _ ↦ t₁).prod := by simp
      _ ≤ φ t₁ := Multiset.prod_map_le_prod_map₀ _ _
          (fun _ _ ↦ zero_le_one.trans (le_max_left _ _)) fun _ _ ↦ le_max_left _ _
  obtain ⟨r, ⟨hr₀, -⟩, hφr⟩ := intermediate_value_Icc (zero_le_one.trans (le_max_left _ _))
    hcont.continuousOn ⟨hφ₀.symm ▸ norm_nonneg c, ht₁⟩
  have hr : 0 < r := by
    refine hr₀.lt_of_ne fun h ↦ hc ?_
    rw [← h, hφ₀] at hφr
    exact norm_eq_zero.mp hφr.symm
  -- split `s` into the elements of norm at most `r` and the others
  set s₁ := s.filter fun a ↦ ‖a‖ ≤ r
  set s₂ := s.filter fun a ↦ ¬ ‖a‖ ≤ r
  have hsplit : φ r = r ^ Multiset.card s₁ * ‖s₂.prod‖ := by
    have h₁ : s₁.map (fun a ↦ max r ‖a‖) = s₁.map fun _ ↦ r :=
      Multiset.map_congr rfl fun a ha ↦ max_eq_left (Multiset.mem_filter.mp ha).2
    have h₂ : s₂.map (fun a ↦ max r ‖a‖) = s₂.map norm :=
      Multiset.map_congr rfl fun a ha ↦ max_eq_right (le_of_not_ge (Multiset.mem_filter.mp ha).2)
    simp only [hφ]
    rw [← Multiset.filter_add_not (fun a ↦ ‖a‖ ≤ r) s, Multiset.map_add, Multiset.prod_add, h₁, h₂,
      Multiset.norm_prod, Multiset.map_const', Multiset.prod_replicate]
  have hm : Multiset.card s₁ ≠ 0 := (Multiset.card_pos_iff_exists_mem.mpr
    ⟨0, Multiset.mem_filter.mpr ⟨hs, by simpa using hr.le⟩⟩).ne'
  have hs₂ : s₂.prod ≠ 0 := Multiset.prod_ne_zero fun h ↦
    (Multiset.mem_filter.mp h).2 (by simpa using hr.le)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c / s₂.prod) (Nat.pos_of_ne_zero hm)
  have hdr : ‖d‖ = r := by
    rw [← pow_left_inj₀ (norm_nonneg d) hr.le hm, ← norm_pow, hd, norm_div,
      div_eq_iff (norm_ne_zero_iff.mpr hs₂), ← hsplit, hφr]
  exact ⟨d, by rw [hdr]; exact hφr⟩

end NormedField
