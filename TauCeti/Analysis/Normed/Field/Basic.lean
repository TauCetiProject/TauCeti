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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
If instead the norms accumulate at `1`, then for `r < 1` and any `n` some `ϖ` with `‖ϖ‖ < 1` has
`r < ‖ϖ‖ ^ n`: `NormedField.exists_lt_norm_pow_of_forall_exists_one_lt_norm_lt`.

The same roots solve norm equations: over an algebraically closed normed field, for a multiset `s`
containing `0` and any `c`, some `d` has `∏_{a ∈ s} max ‖d‖ ‖a‖ = ‖c‖`
(`NormedField.exists_prod_map_max_norm_eq_of_isAlgClosed`). For a nonarchimedean norm the left
side is the Gauss norm at radius `‖d‖` of the polynomial with roots `s`, so `‖d‖` is a radius at
which that Gauss norm equals `‖c‖`.

A normed field whose norm takes every positive real value is densely normed
(`DenselyNormedField.ofForallExistsNormEq`). Separating open subintervals of `(0, ∞)` by norms is
equivalent to the positive norms being dense in `(0, ∞)`
(`NormedField.forall_exists_lt_norm_lt_iff_Ioi_subset_closure`), so in a densely normed field the
positive norms are dense in `(0, ∞)` (`NormedField.Ioi_subset_closure_image_norm`) and the range of
the norm has closure `[0, ∞)` (`NormedField.closure_range_norm`).

Finally, `TauCeti.norm_sub_div_le_of_dist_div_le` turns a bound on the ratio `F / w` near `c⁻¹`
into a relative error bound for `F - w / c`.
-/

public section

/-- The inverse of an element of norm greater than one has norm less than one. -/
theorem TauCeti.norm_inv_lt_one_of_one_lt_norm {K : Type*} [NormedDivisionRing K]
    {j : K} (hj : 1 < ‖j‖) : ‖j⁻¹‖ < 1 := by
  simpa only [norm_inv] using inv_lt_one_of_one_lt₀ hj

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

variable {𝕜} in
/-- **If the norms of `𝕜` accumulate at `1`, some element of norm less than one has `n`-th power
of norm above any `r < 1`**: for every `n` some `ϖ` with `0 < ‖ϖ‖ < 1` has `r < ‖ϖ‖ ^ n`. -/
theorem exists_lt_norm_pow_of_forall_exists_one_lt_norm_lt
    (hacc : ∀ ε : ℝ, 1 < ε → ∃ x : 𝕜, 1 < ‖x‖ ∧ ‖x‖ < ε) {r : ℝ} (hr : r < 1) (n : ℕ) :
    ∃ ϖ : 𝕜, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ r < ‖ϖ‖ ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_norm_lt_one 𝕜
    exact ⟨ϖ, hϖ0, hϖ1, by simpa using hr⟩
  rcases le_or_gt r 0 with hr0 | hr0
  · obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_norm_lt_one 𝕜
    exact ⟨ϖ, hϖ0, hϖ1, hr0.trans_lt (by positivity)⟩
  -- take `ϖ = x⁻¹` for `1 < ‖x‖ < r ^ (-1 / n)`
  obtain ⟨x, hx1, hxε⟩ := hacc (r⁻¹ ^ (n : ℝ)⁻¹)
    (Real.one_lt_rpow ((one_lt_inv₀ hr0).mpr hr) (by simpa using Nat.pos_of_ne_zero hn))
  have hx0 : 0 < ‖x‖ := zero_lt_one.trans hx1
  refine ⟨x⁻¹, by rw [norm_inv]; positivity, by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx1,
    ?_⟩
  rw [norm_inv, inv_pow, lt_inv_comm₀ hr0 (by positivity)]
  calc ‖x‖ ^ n < (r⁻¹ ^ (n : ℝ)⁻¹) ^ n := pow_lt_pow_left₀ hxε hx0.le hn
    _ = r⁻¹ := Real.rpow_inv_natCast_pow (by positivity) hn

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

/-- A normed field whose norm takes every positive real value is densely normed. The underlying
normed field is the given one, so that over a `NontriviallyNormedField` this structure induces the
original `NontriviallyNormedField` up to structure eta. -/
@[expose, instance_reducible]
def DenselyNormedField.ofForallExistsNormEq {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : ∀ r : ℝ, 0 < r → ∃ x : 𝕜, ‖x‖ = r) : DenselyNormedField 𝕜 where
  toNormedField := h'
  lt_norm_lt r₁ r₂ h₀ hr := by
    obtain ⟨x, hx⟩ := h ((r₁ + r₂) / 2) (by linarith)
    exact ⟨x, by linarith, by linarith⟩

namespace NormedField

/-- Positive norms separate open subintervals `(r₁, r₂)` of `(0, ∞)` if and only if they are
dense in `(0, ∞)`. -/
theorem forall_exists_lt_norm_lt_iff_Ioi_subset_closure {α : Type*} [Norm α] :
    (∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂) ↔
      Set.Ioi (0 : ℝ) ⊆ closure ((‖·‖) '' {x : α | 0 < ‖x‖}) := by
  refine ⟨fun h r hr ↦ Metric.mem_closure_iff.mpr fun ε hε ↦ ?_,
    fun h r₁ r₂ hr₁ hlt ↦ ?_⟩
  · have hr₀ : 0 < r := hr
    obtain ⟨x, hx₁, hx₂⟩ := h (max (r / 2) (r - ε)) (r + ε) (lt_max_of_lt_left (half_pos hr₀))
      (max_lt (by linarith) (by linarith))
    refine ⟨‖x‖, ⟨x, (lt_max_of_lt_left (half_pos hr₀)).trans hx₁, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith [le_max_right (r / 2) (r - ε)]⟩
  · have hm : (r₁ + r₂) / 2 ∈ Set.Ioi (0 : ℝ) := by
      rw [Set.mem_Ioi]
      linarith
    obtain ⟨_, ⟨x, -, rfl⟩, hdist⟩ :=
      Metric.mem_closure_iff.mp (h hm) ((r₂ - r₁) / 2) (by linarith)
    rw [Real.dist_eq, abs_lt] at hdist
    exact ⟨x, by linarith, by linarith⟩

/-- In a densely normed field, the positive norms are dense in `(0, ∞)`. -/
theorem Ioi_subset_closure_image_norm (𝕜 : Type*) [DenselyNormedField 𝕜] :
    Set.Ioi (0 : ℝ) ⊆ closure ((‖·‖) '' {x : 𝕜 | 0 < ‖x‖}) :=
  forall_exists_lt_norm_lt_iff_Ioi_subset_closure.mp fun _ _ hr₁ ↦ exists_lt_norm_lt 𝕜 hr₁.le

/-- In a densely normed field, the closure of the range of the norm is `[0, ∞)`. -/
@[simp]
theorem closure_range_norm (𝕜 : Type*) [DenselyNormedField 𝕜] :
    closure (Set.range (‖·‖ : 𝕜 → ℝ)) = Set.Ici 0 := by
  refine Set.Subset.antisymm (closure_minimal ?_ isClosed_Ici) fun r hr ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact norm_nonneg x
  · rcases eq_or_lt_of_le (Set.mem_Ici.mp hr) with rfl | hr₀
    · exact subset_closure ⟨0, norm_zero⟩
    · exact closure_mono (Set.image_subset_range _ _) (Ioi_subset_closure_image_norm 𝕜 hr₀)

end NormedField

namespace TauCeti

/-- A bound on the ratio `F / w` near `c⁻¹` is a relative error bound for `w / c`: if
`dist (F / w) c⁻¹ ≤ η / ‖c‖` and `w ≠ 0`, then `‖F - w / c‖ ≤ η * ‖w / c‖`. -/
theorem norm_sub_div_le_of_dist_div_le {𝕜 : Type*} [NormedField 𝕜] {F w c : 𝕜} {η : ℝ}
    (hw : w ≠ 0) (h : dist (F / w) c⁻¹ ≤ η / ‖c‖) : ‖F - w / c‖ ≤ η * ‖w / c‖ := by
  have hmul := mul_le_mul_of_nonneg_right h (norm_nonneg w)
  rw [dist_eq_norm, ← norm_mul] at hmul
  have heq : (F / w - c⁻¹) * w = F - w / c := by
    field_simp
  rw [heq] at hmul
  calc ‖F - w / c‖ ≤ η / ‖c‖ * ‖w‖ := hmul
    _ = η * ‖w / c‖ := by rw [norm_div]; ring

end TauCeti
