/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.GroupTheory.FiniteAbelian.WeightedCharacterSums

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Top comparison for projected Frobenius Riesz sums

After averaging over translates, the thick-place contribution is a sum over the surviving
characters and the top places. Comparing the coset counts of the tops with the `4 : 3` profile
replaces the kept coefficients by positive Fourier weights. The discarded characters cost
only the norms of their remainders, and the variation and coset-count errors together fit
in a `4 x^(1/2+ε)` power budget. The cutoff for this comparison is uniform in the host.

The normalization and bound follow Levent Alpöge's `Deduction.CharacterBalanceMoves.core`
and `Deduction.CharacterBalanceMoves.one_char` in `ChCore.lean` of the
[published formalization](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).
-/

public section

open Finset Filter

namespace TauCeti

private theorem eventually_logarithmic_top_error_le (o : ℕ) (C : ℝ) {ε : ℝ}
    (hε : -(1 / 2) < ε) :
    ∀ᶠ x : ℝ in atTop,
      (4 * (o : ℝ) + 4 * (o : ℝ) ^ 2 * x ^ ε) * (C * Real.log x) ≤ 4 * x ^ (1 / 2 + ε) := by
  have hlog (d r : ℝ) (hr : 0 < r) : ∀ᶠ x : ℝ in atTop, d * Real.log x ≤ 2 * x ^ r := by
    have h := ((isLittleO_log_rpow_atTop hr).const_mul_left d).bound (show 0 < 2 by norm_num)
    filter_upwards [eventually_ge_atTop (0 : ℝ), h] with x hx h
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx _)] at h
    exact (le_abs_self _).trans h
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlog (4 * o * C) (1 / 2 + ε) (by linarith), hlog (4 * o ^ 2 * C) (1 / 2) (by norm_num)]
    with x hx hvar hcounts
  calc
    _ = (4 * o * C) * Real.log x + x ^ ε * ((4 * o ^ 2 * C) * Real.log x) := by ring
    _ ≤ 2 * x ^ (1 / 2 + ε) + x ^ ε * (2 * x ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add hx, add_comm ε]; ring

open scoped Classical in
private theorem top_character_comparison {α ι Q : Type*} [Group Q] [Fintype Q]
    {o : ℕ} (hQ : Fintype.card Q ≤ o) (S : Finset α) (p : α → Q) (I K : Finset ι)
    (hKI : K ⊆ I) (hI : I.card ≤ 4 * o)
    (χ : ι → Q →* ℂ) (c z : ι → ℂ) (f : ι → α → ℂ) {x ε D : ℝ}
    (hν : ∀ q, |((S.filter fun a ↦ p a = q).card : ℝ) -
      ((if q = 1 then 4 else 3) / (3 * (Fintype.card Q : ℝ) + 1)) * S.card| ≤
        x ^ (-1 + ε) * S.card)
    (hc : ∀ i ∈ I \ K, ‖c i‖ ≤ 1) (hcK : ∀ i ∈ K, c i = 1)
    (hf : ∀ i ∈ I, ∀ a ∈ S, ‖f i a - z i‖ ≤ D) (hz : ∀ i ∈ K, ‖z i‖ ≤ x * D)
    (hx : 0 ≤ x) (hD : 0 ≤ D) :
    (S.card : ℝ) * ((∑ i ∈ K, (if χ i = 1 then 1 else (3 * (Fintype.card Q : ℝ) + 1)⁻¹) *
      (z i).re) -
      (∑ i ∈ I \ K, ‖z i‖) - (4 * (o : ℝ) + 4 * (o : ℝ) ^ 2 * x ^ ε) * D) ≤
      ∑ i ∈ I, (c i * ∑ a ∈ S, χ i (p a) * f i a).re := by
  let n : ℝ := Fintype.card Q
  let ν (q : Q) : ℝ := (if q = 1 then 4 else 3) / (3 * n + 1)
  have hden : 0 < 3 * n + 1 := by dsimp [n]; positivity
  have hden_eq : 1 + (n - 1) * (3 / 4) = (3 * n + 1) / 4 := by ring
  have hprofile (q : Q) : ν q =
      (if q = 1 then 1 else (3 / 4 : ℝ)) / (1 + (n - 1) * (3 / 4)) := by
    rw [hden_eq]
    dsimp only [ν]
    split_ifs <;> field_simp [hden.ne']
  have hFourier (i : ι) : ∑ q, (ν q : ℂ) * χ i q =
      ((if χ i = 1 then 1 else (3 * n + 1)⁻¹ : ℝ) : ℂ) := by
    simp_rw [hprofile]
    have hn : 1 + ((Fintype.card Q : ℝ) - 1) * (3 / 4) ≠ 0 :=
      (hden_eq.trans_ne (div_ne_zero hden.ne' (by norm_num)))
    rw [(χ i).sum_normalized_twoLevel_mul_apply (3 / 4) hn, hden_eq]
    split_ifs
    · simp
    · congr 1
      field_simp [hden.ne']; norm_num
  have hkept : (∑ i ∈ K, (c i * (∑ q, (ν q : ℂ) * χ i q) * z i).re) =
      ∑ i ∈ K, (if χ i = 1 then 1 else (3 * n + 1)⁻¹) * (z i).re := by
    exact sum_congr rfl fun i hi ↦ by simp only [hcK i hi, one_mul, hFourier, Complex.re_ofReal_mul]
  have hphase (i : ι) (hi : i ∈ I) : ‖c i‖ ≤ 1 := by
    by_cases hiK : i ∈ K
    · simp [hcK i hiK]
    · exact hc i (mem_sdiff.mpr ⟨hi, hiK⟩)
  have h := card_mul_le_sum_re_weighted_characters_of_fiber_counts
    S p ν I K hKI χ c z f (fun _ ↦ D) (x ^ (-1 + ε)) hν hphase hf
  have hvar : (∑ _i ∈ I, D) ≤ 4 * (o : ℝ) * D := by
    rw [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hD
  have hsize : (∑ i ∈ K, ‖z i‖) ≤ 4 * (o : ℝ) * (x * D) :=
    (sum_le_sum hz).trans (by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_le_card hKI).trans hI)
        (mul_nonneg hx hD))
  have hcounts : (Fintype.card Q : ℝ) * x ^ (-1 + ε) * (∑ i ∈ K, ‖z i‖) ≤
      4 * (o : ℝ) ^ 2 * x ^ ε * D := by
    have hcard : (Fintype.card Q : ℝ) ≤ o := by exact_mod_cast hQ
    calc
      _ ≤ (o : ℝ) * x ^ (-1 + ε) * (4 * (o : ℝ) * (x * D)) :=
        mul_le_mul (by gcongr) hsize (sum_nonneg fun _ _ ↦ norm_nonneg _) (by positivity)
      _ = 4 * (o : ℝ) ^ 2 * (x ^ (-1 + ε) * x) * D := by ring
      _ ≤ _ := by
        rcases hx.eq_or_lt with rfl | hx'
        · simp only [mul_zero, zero_mul]; positivity
        · rw [← Real.rpow_add_one hx'.ne', neg_add_cancel_comm]
  rw [hkept] at h
  exact (mul_le_mul_of_nonneg_left (by linarith only [hvar, hcounts]) (Nat.cast_nonneg _)).trans h

open scoped Classical in
/-- The projected thick sum bounds from below the cyclic-family sum with the `4 : 3` weights,
scaled by the number of tops, after charging the norms at the common scale of indices in
`I \ K` and an error of `4 x^(1/2+ε)`, where `ε` is the precision exponent. The natural
number `o` bounds the size of the quotient, and `p` assigns each top in `S` to its coset. The
cutoff depends only on `o`, the logarithmic budget `C`, and the precision exponent. -/
theorem card_mul_cyclic_riesz_sum_le_projection (o : ℕ) (C : ℝ) {ε : ℝ} (hε : -(1 / 2) < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x ≥ x₀,
      ∀ {α ι Q : Type*} [Group Q] [Fintype Q], Fintype.card Q ≤ o →
      ∀ (S : Finset α) (p : α → Q) (I K : Finset ι), K ⊆ I → I.card ≤ 4 * o →
      ∀ (χ : ι → Q →* ℂ) (c z : ι → ℂ) (f : ι → α → ℂ),
      (∀ q, |((S.filter fun a ↦ p a = q).card : ℝ) -
        ((if q = 1 then 4 else 3) / (3 * (Fintype.card Q : ℝ) + 1)) * S.card| ≤
          x ^ (-1 + ε) * S.card) →
      (∀ i ∈ I \ K, ‖c i‖ ≤ 1) → (∀ i ∈ K, c i = 1) →
      (∀ i ∈ I, ∀ a ∈ S, ‖f i a - z i‖ ≤ |C| * Real.log x) →
      (∀ i ∈ K, ‖z i‖ ≤ x * (|C| * Real.log x)) →
      S.card * ((∑ i ∈ K, (if χ i = 1 then 1 else (3 * (Fintype.card Q : ℝ) + 1)⁻¹) *
        (z i).re) -
        (∑ i ∈ I \ K, ‖z i‖) - 4 * x ^ (1 / 2 + ε)) ≤
        ∑ i ∈ I, (c i * ∑ a ∈ S, χ i (p a) * f i a).re := by
  obtain ⟨y, hy⟩ := eventually_atTop.mp (eventually_logarithmic_top_error_le o |C| hε)
  refine ⟨max 3 y, le_max_left .., fun x hx ↦ ?_⟩
  intro α ι Q _ _ hQ S p I K hKI hI χ c z f hν hc hcK hf hz
  have hx1 : 1 ≤ x := by linarith [le_max_left (3 : ℝ) y]
  have hcost := top_character_comparison hQ S p I K hKI hI χ c z f hν hc hcK hf hz
    (zero_le_one.trans hx1) (mul_nonneg (abs_nonneg _) (Real.log_nonneg hx1))
  have herror := hy x ((le_max_right ..).trans hx)
  exact (mul_le_mul_of_nonneg_left (by linarith only [herror]) (Nat.cast_nonneg _)).trans hcost

end TauCeti
