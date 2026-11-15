/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The Japanese bracket in `L²` and the `L¹` bound by a weighted `L²` norm

Let `V` be a finite-dimensional real normed space of dimension `d`. For `2s > d` the negative
power `(1 + ‖x‖ ^ 2) ^ (-s / 2)` of the Japanese bracket is square integrable for every additive
Haar measure (`TauCeti.memLp_rpow_neg_one_add_norm_sq`), since its square is the integrable
function `(1 + ‖x‖ ^ 2) ^ (-2s / 2)` (`integrable_rpow_neg_one_add_norm_sq`). Consequently a
function of polynomial growth `C (1 + ‖x‖) ^ k` becomes square integrable after multiplication by
`(1 + ‖x‖ ^ 2) ^ (s / 2)` once `d < -2 (s + k)`
(`TauCeti.memLp_two_one_add_norm_sq_rpow_smul_of_norm_le`). For every `s`, the
Cauchy–Schwarz inequality gives

`‖v‖₁ ≤ ‖(1 + ‖·‖ ^ 2) ^ (-s / 2)‖₂ ‖(1 + ‖·‖ ^ 2) ^ (s / 2) v‖₂`

(`TauCeti.eLpNorm_one_le_eLpNorm_rpow_neg_one_add_norm_sq_mul_eLpNorm_one_add_norm_sq_rpow_smul`).
Together these bound the `L¹` norm of a function by a weighted `L²` norm when `2s > d`. Applied
to the Fourier transform of a function in the Bessel-potential space `H^s`, whose `H^s` norm is
the weighted `L²` norm of its Fourier transform, this is the estimate behind the Sobolev embedding
`H^s ⊆ C₀` and the algebra property of `H^s` for `s > d / 2`.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., §9.3.
-/

public section

open MeasureTheory Module
open scoped ENNReal

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `2s > dim V` the function `(1 + ‖x‖ ^ 2) ^ (-s / 2)` is square integrable. -/
theorem memLp_rpow_neg_one_add_norm_sq [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {s : ℝ} (hs : (finrank ℝ V : ℝ) < 2 * s) :
    MemLp (fun x : V => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 μ := by
  have hc : Continuous fun x : V => (1 + ‖x‖ ^ 2) ^ (-s / 2) :=
    (by fun_prop : Continuous fun x : V => 1 + ‖x‖ ^ 2).rpow_const fun x =>
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2).ne'
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hc.aestronglyMeasurable]
  convert (integrable_rpow_neg_one_add_norm_sq (μ := μ) hs).lintegral_lt_top using 2
  funext x
  have hpos : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [← ofReal_norm, Real.norm_of_nonneg (by positivity), ENNReal.toReal_ofNat,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul hpos.le]
  ring_nf

/-- **A negative Japanese bracket weight makes polynomial growth square integrable.** If
`‖f x‖ ≤ C (1 + ‖x‖) ^ k` almost everywhere, then `x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2) • f x` is square
integrable for every additive Haar measure on a finite-dimensional real normed space of dimension
`d < -2 (s + k)`. -/
theorem memLp_two_one_add_norm_sq_rpow_smul_of_norm_le [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {f : V → F}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} {k : ℕ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    {s : ℝ} (hs : (finrank ℝ V : ℝ) < -2 * (s + k)) :
    MemLp (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2) • f x) 2 μ := by
  refine ((memLp_rpow_neg_one_add_norm_sq μ (s := -(s + k)) (by linarith)).const_mul
    (C * 2 ^ k)).mono' ((((continuous_const.add (continuous_norm.pow 2)).rpow_const fun x ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2).ne').aestronglyMeasurable).smul hf) ?_
  filter_upwards [hfC] with x hx
  -- `⟨x⟩ ^ s (1 + ‖x‖) ^ k ≤ 2 ^ k ⟨x⟩ ^ (s + k)`.
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hx) (by positivity)
  have hk : (1 + ‖x‖) ^ k ≤ 2 ^ k * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := by
    simpa [one_add_one_eq_two] using one_add_mul_norm_pow_le zero_le_one x k
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (1 + ‖x‖ ^ 2) ^ (s / 2) * ‖f x‖
      ≤ (1 + ‖x‖ ^ 2) ^ (s / 2) * (C * (2 ^ k * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2))) := by
        gcongr
        exact hx.trans (by gcongr)
    _ = C * 2 ^ k * (1 + ‖x‖ ^ 2) ^ (-(-(s + k)) / 2) := by
        rw [neg_neg, add_div, Real.rpow_add (by positivity)]
        ring

/-- **The `L¹` norm is bounded by a weighted `L²` norm.** For every `s` and every function `v`,
`‖v‖₁ ≤ ‖(1 + ‖·‖ ^ 2) ^ (-s / 2)‖₂ ‖(1 + ‖·‖ ^ 2) ^ (s / 2) v‖₂`. The first factor is finite
when `2s > dim V` (`TauCeti.memLp_rpow_neg_one_add_norm_sq`). -/
theorem eLpNorm_one_le_eLpNorm_rpow_neg_one_add_norm_sq_mul_eLpNorm_one_add_norm_sq_rpow_smul
    (μ : Measure V) (s : ℝ) (v : V → F) :
    eLpNorm v 1 μ ≤ eLpNorm (fun x : V => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 μ *
      eLpNorm (fun x => (1 + ‖x‖ ^ 2) ^ (s / 2) • v x) 2 μ := by
  have h : v = (fun x : V => (1 + ‖x‖ ^ 2) ^ (-s / 2)) •
      fun x => (1 + ‖x‖ ^ 2) ^ (s / 2) • v x := by
    funext x
    rw [Pi.smul_apply', smul_smul, ← Real.rpow_add (by positivity), neg_div, neg_add_cancel,
      Real.rpow_zero, one_smul]
  conv_lhs => rw [h]
  exact eLpNorm_smul_le_mul_eLpNorm_of_pos one_pos

end TauCeti
