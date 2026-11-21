/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.RCLike.Basic
import TauCeti.Analysis.SpecialFunctions.Log.GrowthScale
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The classical zero-free region for the Riemann zeta function

De la Vallée Poussin proved that `ζ(s)` has no zeros in a region of the form
`Re s ≥ 1 - c / log (|Im s| + 3)` away from its simple pole at `s = 1`.

For `|Im s| ≥ 1`, Landau's local logarithmic-derivative lemma (proved via the Euler–Maclaurin
bound on the disc of radius `1 / 2` centred at `9 / 8 + i t` in
`TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds`) gives an upper bound of order
`log (|t| + 3)` for `-Re (ζ′/ζ)`, retaining any nearby zero `ρ = β + i t` with a positive
partial-fraction term `(σ - β)⁻¹` (and extending across `Re s > 9 / 8` via the Dirichlet series
at `9 / 8`). Combined with the pole bound `-Re (ζ′/ζ(1 + η)) ≤ η⁻¹ + O(1)` and the `3–4–1`
trigonometric inequality at `σ = 1 + 4 (1 - β)`, this forces `1 - β ≫ (log (|t| + 3))⁻¹`.

For `|Im s| ≤ 1`, the regularized function `LFunctionTrivChar₁ 1` (equal to `(s - 1) ζ(s)` away
from `s = 1`) is entire and nonvanishing along the segment `{1} × [-1, 1]`, so compactness separates
its zeros in `[1/2, 1] × [-1, 1]` from the line `Re s = 1` by a uniform strip.

## Main results

* `TauCeti.LFunctions.riemannZeta_zeroFreeRegion`: the classical de la Vallée Poussin zero-free
  region `Re s ≥ 1 - c / log (|Im s| + 3)` for `riemannZeta` away from `s = 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13.
* Michael Stoll, David Loeffler, and Terence Tao, `riemannZeta_ne_zero_of_one_le_re` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §3.11.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti.LFunctions

private theorem exists_neg_re_logDeriv_riemannZeta_retained :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ : ℝ} {s : ℂ}, 1 ≤ σ → σ ≤ 9 / 8 → 1 ≤ |s.im| → 7 / 8 ≤ s.re →
      riemannZeta s = 0 →
        -(logDeriv riemannZeta (σ + s.im * I)).re + (σ - s.re)⁻¹ ≤
          A * Real.log (|s.im| + 3) := by
  obtain ⟨A, hA, hLandau⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_add_sum_le
  refine ⟨A, hA, fun {σ s} hσ1 hσ2 ht hs7 hζ0 ↦ ?_⟩
  have hs_lt1 : s.re < 1 :=
    by_contra fun h ↦ riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ0
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall ((9 / 8 : ℝ) + s.im * I) ((1 / 2 : ℝ) / 2)) :=
    analyticOn_riemannZeta.mono fun w hw h1 ↦ by
      subst h1
      have him : |s.im| ≤ (1 / 2 : ℝ) / 2 := by
        simpa using RCLike.abs_im_sub_le_of_mem_closedBall hw
      linarith
  exact hf.neg_re_logDeriv_add_sub_inv_le
    (riemannZeta_ne_zero_of_one_le_re (by simp; norm_num))
    (abs_le.mpr ⟨by linarith, by linarith⟩) hζ0 (hs_lt1.le.trans hσ1) (hLandau hσ1 hσ2 ht {s})

private theorem exists_riemannZeta_ne_zero_of_one_le_abs_im :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 ≤ |s.im| → 1 - c / Real.log (|s.im| + 3) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨A₁, hA₁, hfree⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_le
  obtain ⟨A₂, hA₂, hret⟩ := exists_neg_re_logDeriv_riemannZeta_retained
  obtain ⟨C₁, hC₁0, hpole0⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set B : ℝ := 3 * C₁ / Real.log 3 + 4 * A₂ + 2 * A₁
  obtain ⟨c, hc0, -, hcutoff⟩ := TauCeti.exists_pos_le_mul_and_mul_lt_mul_inv
    (cutoff := (1 / 32 : ℝ)) (L₀ := Real.log 3) (weight := (1 / 20 : ℝ)) (M := B)
    (by norm_num) hlog3 (by norm_num) (by positivity)
  refine ⟨c, hc0, fun s ht hs hζ0 ↦ ?_⟩
  set L : ℝ := Real.log (|s.im| + 3)
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  set δ : ℝ := 1 - s.re
  have hδ0 : 0 < δ := sub_pos.2 <|
    by_contra fun h ↦ riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ0
  obtain ⟨hδ_32, hlt⟩ := hcutoff hδ0 hlog_ge (by linarith)
  set σ : ℝ := 1 + 4 * δ
  have hpole : -(logDeriv riemannZeta σ).re ≤ (4 * δ)⁻¹ + C₁ / Real.log 3 * L :=
    le_trans (by simpa [σ] using hpole0 (η := 4 * δ) (by positivity) (by linarith))
      (add_le_add_right (TauCeti.le_div_mul_of_le hC₁0 hlog3 hlog_ge) _)
  have hzero_t : -(logDeriv riemannZeta (σ + s.im * I)).re + (5 * δ)⁻¹ ≤ A₂ * L := by
    have hsub : σ - s.re = 5 * δ := by simp only [σ, δ]; ring
    simpa [hsub] using hret (σ := σ) (s := s) (by linarith) (by linarith) ht (by linarith) hζ0
  have hzero_2t : -(logDeriv riemannZeta (σ + 2 * s.im * I)).re ≤ 2 * A₁ * L := by
    have him : ((σ : ℂ) + 2 * s.im * I).im = 2 * s.im := by simp
    have h2 := hfree (s := (σ : ℂ) + 2 * s.im * I) (by simp; linarith)
      (by rw [him, abs_mul]; norm_num; linarith)
    have hlog2 : Real.log (|2 * s.im| + 3) ≤ 2 * L := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      simpa using Real.log_mul_two_mul_add_le (q := 1) le_rfl (abs_nonneg s.im) (by norm_num)
    rw [him] at h2; nlinarith
  have h341 : 3 * (logDeriv riemannZeta σ).re + 4 * (logDeriv riemannZeta (σ + s.im * I)).re +
      (logDeriv riemannZeta (σ + 2 * s.im * I)).re ≤ 0 := by
    simpa [one_pow, LFunction_modOne_eq] using
      (1 : DirichletCharacter ℂ 1).threeFourOne_re_logDeriv_riemannZeta_LFunction_nonpos
        (σ := σ) (by linarith) s.im
  have hcomb : 1 / 20 * δ⁻¹ ≤ B * L := by
    have halg : 4 * (5 * δ)⁻¹ - 3 * (4 * δ)⁻¹ = 1 / 20 * δ⁻¹ := by field_simp [hδ0.ne']; ring
    have : B * L = 3 * (C₁ / Real.log 3 * L) + 4 * (A₂ * L) + 2 * A₁ * L := by simp [B]; ring
    linarith
  exact hlt.not_ge hcomb

private theorem exists_riemannZeta_ne_zero_of_abs_im_le_one :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s ≠ 1 → |s.im| ≤ 1 → 1 - δ ≤ s.re → riemannZeta s ≠ 0 := by
  set K : Set ℂ := Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  set Z : Set ℂ := {z ∈ K | LFunctionTrivChar₁ 1 z = 0}
  have hZ : IsCompact Z :=
    hK.inter_right (isClosed_eq (differentiable_LFunctionTrivChar₁ 1).continuous continuous_const)
  have hline (z : ℂ) (hz : 1 ≤ z.re) : LFunctionTrivChar₁ 1 z ≠ 0 := by
    rcases eq_or_ne z 1 with rfl | hz1
    · exact LFunctionTrivChar₁_apply_one_ne_zero 1
    · rw [LFunctionTrivChar₁, Function.update_of_ne hz1, LFunctionTrivChar, LFunction_modOne_eq]
      exact mul_ne_zero (sub_ne_zero.2 hz1) (riemannZeta_ne_zero_of_one_le_re hz)
  have hne_of_not_mem (δ : ℝ) (hδ_half : δ ≤ 1 / 2) (hdisj : ∀ z ∈ Z, z.re < 1 - δ)
      (s : ℂ) (hs1 : s ≠ 1) (hsim : |s.im| ≤ 1) (hsre : 1 - δ ≤ s.re) : riemannZeta s ≠ 0 := by
    rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1
    have hsK : s ∈ K := ⟨⟨by linarith, h1.le⟩, abs_le.mp hsim⟩
    have hsZ : LFunctionTrivChar₁ 1 s ≠ 0 := fun h0 ↦ (hdisj s ⟨hsK, h0⟩).not_ge hsre
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, LFunction_modOne_eq]
      at hsZ
    exact right_ne_zero_of_mul hsZ
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · exact ⟨1 / 2, by norm_num, hne_of_not_mem (1 / 2) le_rfl (by simp [hZe])⟩
  obtain ⟨z₀, hz₀Z, hz₀max⟩ := hZ.exists_isMaxOn hZne continuous_re.continuousOn
  have hz₀_lt1 : z₀.re < 1 :=
    lt_of_le_of_ne hz₀Z.1.1.2 fun h1 ↦ hline z₀ h1.ge hz₀Z.2
  refine ⟨min (1 / 2) ((1 - z₀.re) / 2), by positivity,
    hne_of_not_mem _ (min_le_left _ _) fun z hz ↦ ?_⟩
  have hle : z.re ≤ z₀.re := hz₀max hz
  have hmin : min (1 / 2) ((1 - z₀.re) / 2) ≤ (1 - z₀.re) / 2 := min_le_right _ _
  linarith

/-- **The classical de la Vallée Poussin zero-free region for `ζ`.** There is an absolute constant
`c > 0` such that `riemannZeta s ≠ 0` whenever `s ≠ 1` and
`1 - c / Real.log (|s.im| + 3) ≤ s.re`. -/
theorem riemannZeta_zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨c₁, hc₁, hhigh⟩ := exists_riemannZeta_ne_zero_of_one_le_abs_im
  obtain ⟨δ, hδ, hlow⟩ := exists_riemannZeta_ne_zero_of_abs_im_le_one
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨min c₁ (δ * Real.log 3), by positivity, fun s hs1 hsre ↦ ?_⟩
  have hlog_ge : Real.log 3 ≤ Real.log (|s.im| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < Real.log (|s.im| + 3) := hlog3.trans_le hlog_ge
  rcases le_or_gt 1 |s.im| with him | him
  · refine hhigh s him (le_trans ?_ hsre)
    gcongr
    exact min_le_left _ _
  · refine hlow s hs1 him.le (le_trans ?_ hsre)
    have hdiv := div_le_of_le_mul₀ hlog_pos.le hδ.le
      ((min_le_right c₁ _).trans (mul_le_mul_of_nonneg_left hlog_ge hδ.le))
    linarith

/-! ### Example -/

example : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ 10 → ∀ σ : ℝ, 1 - δ ≤ σ → σ < 1 →
    riemannZeta (σ + t * I) ≠ 0 := by
  obtain ⟨c, hc, hζ⟩ := riemannZeta_zeroFreeRegion
  have _ : 0 < Real.log 13 := Real.log_pos (by norm_num)
  refine ⟨c / Real.log 13, by positivity, fun t ht σ hσ1 hσ2 ↦ ?_⟩
  have hs1 : (σ : ℂ) + t * I ≠ 1 := fun h ↦ by
    have := congrArg re h; simp at this; linarith
  refine hζ _ hs1 ?_
  have hlog : Real.log (|((σ : ℂ) + t * I).im| + 3) ≤ Real.log 13 :=
    Real.log_le_log (by positivity) (by simp; linarith)
  have hlog_pos : 0 < Real.log (|((σ : ℂ) + t * I).im| + 3) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans_le (Real.log_le_log (by norm_num) (by simp))
  have hdiv : c / Real.log 13 ≤ c / Real.log (|((σ : ℂ) + t * I).im| + 3) :=
    div_le_div_of_nonneg_left hc.le hlog_pos hlog
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  linarith

end TauCeti.LFunctions
