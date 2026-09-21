/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# The Poincaré–Wirtinger inequality for `C¹` functions on a convex domain

Let `Ω` be a bounded convex open subset of a finite-dimensional real normed space `E` of
dimension `n`, let `μ` be an additive Haar measure, and let `S ⊆ Ω` have positive measure. For a
`C¹` function `u` on `Ω` and `1 ≤ p < ∞`, this file proves

`‖u - ⨍ y in S, u y ∂μ‖_{Lᵖ(Ω)} ≤ C * ‖Du‖_{Lᵖ(Ω)}`, where
`C = μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)`.

The constant depends only on the dimension, through the Haar measure of the unit ball, on the
diameter of `Ω` and on the measure of `S`, as it must: rescaling `Ω` by `t` multiplies it by
`t`. The mean may be taken over any subset of positive measure, not only over `Ω` itself.

The proof bounds the deviation `u x - ⨍ S u` pointwise by the Riesz potential
`∫_Ω ‖Du y‖ ‖x - y‖ ^ (1 - n) dy` (`TauCeti.enorm_sub_setAverage_le_of_convex`), and bounds that
potential in `Lᵖ(Ω)` by Schur's test (`TauCeti.lintegral_rpow_lintegral_mul_le`): since `Ω` lies
in the closed ball of radius `diam Ω` about each of its points, the integral of the kernel
`‖x - y‖ ^ (1 - n)` over `Ω` in either variable is at most `n μ(B(0, 1)) diam Ω`. The constant is
not sharp; Gilbarg–Trudinger obtain `(μ(B(0, 1)) / μ(S)) ^ (1 - 1/n) (diam Ω) ^ n` from a finer
bound on the Riesz potential.

## Main declarations

* `TauCeti.lintegral_enorm_sub_setAverage_rpow_le_of_convex`: the inequality in `∫⁻` form.
* `TauCeti.eLpNorm_sub_setAverage_le_of_convex`: the inequality between `Lᵖ` seminorms.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16 and equation (7.45).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E}

/-- **The Poincaré–Wirtinger inequality on a convex domain**, in `∫⁻` form. If `u` is `C¹` on a
bounded convex open set `Ω` and `S ⊆ Ω` has positive measure, then for `1 ≤ p` the `p`-th power
of the deviation of `u` from its mean over `S` has integral over `Ω` at most `C ^ p` times the
integral of `‖Du‖ ^ p` over `Ω`, where `C = μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` and `n` is
the dimension of the space. -/
theorem lintegral_enorm_sub_setAverage_rpow_le_of_convex (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) {p : ℝ}
    (hp : 1 ≤ p) :
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal ((μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) ^ p) *
        ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ^ p ∂μ := by
  set n := finrank ℝ E
  set d := diam Ω
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hS_top : μ S ≠ ∞ := ((measure_mono hS).trans_lt hb.measure_lt_top).ne
  -- The Riesz kernel and its potential of the norm of the derivative.
  set k : E → E → ℝ≥0∞ := fun x y => ‖x - y‖ₑ ^ (1 - (n : ℝ))
  set V : E → ℝ≥0∞ := fun x => ∫⁻ y in Ω, k x y * ‖fderiv ℝ u y‖ₑ ∂μ
  -- The pointwise potential estimate, with its constant `c`.
  set c : ℝ≥0∞ := ENNReal.ofReal (d ^ n / n) / μ S
  have hpoint : ∀ x ∈ Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤ c * V x := fun x hx => by
    simpa only [V, k, mul_comm (‖fderiv ℝ u _‖ₑ)] using
      enorm_sub_setAverage_le_of_convex hΩ hΩc hb hu hx hS hS₀
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero the kernel vanishes, and so does the left-hand side.
    have hk0 : ∀ x y : E, k x y = 0 := fun x y => by
      simp [k, n, Subsingleton.elim x y, finrank_zero_of_subsingleton]
    have hzero : ∀ x ∈ Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ^ p = 0 := fun x hx => by
      have h := hpoint x hx
      simp only [V, hk0, zero_mul, lintegral_zero, mul_zero, nonpos_iff_eq_zero] at h
      rw [h, ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hp)]
    rw [setLIntegral_congr_fun hΩ.measurableSet hzero, lintegral_zero]
    exact bot_le
  have hn : 0 < (n : ℝ) := Nat.cast_pos.2 finrank_pos
  have hd : 0 ≤ d := diam_nonneg
  -- Schur's test for the kernel `k` on `Ω`: both of its marginal integrals are at most `K`.
  set K : ℝ := n * μ.real (ball 0 1) * d
  have hK : 0 ≤ K := by positivity
  have hmarg : ∀ x ∈ Ω, ∫⁻ y in Ω, k x y ∂μ ≤ ENNReal.ofReal K := fun x hx =>
    calc
      _ ≤ ∫⁻ y in closedBall x d, k x y ∂μ :=
        lintegral_mono_set fun _ hy => mem_closedBall.2 (dist_le_diam_of_mem hb hy hx)
      _ = _ := by
        rw [setLIntegral_closedBall_enorm_sub_rpow (by linarith) hd, add_sub_cancel,
          Real.rpow_one, div_one]
  have hcont := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hschur : ∫⁻ x in Ω, V x ^ p ∂μ ≤
      ENNReal.ofReal K ^ (p - 1) * ENNReal.ofReal K * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ^ p ∂μ :=
    lintegral_rpow_lintegral_mul_le (by fun_prop)
      (hcont.enorm.aemeasurable hΩ.measurableSet) hp
      ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ hmarg))
      ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun y hy => by
        simpa only [k, enorm_sub_rev y] using hmarg y hy))
  -- Assemble the constant.
  have hc : c = ENNReal.ofReal (d ^ n / n / μ.real S) := by
    have hSpos : 0 < μ.real S := ENNReal.toReal_pos hS₀ hS_top
    rw [ENNReal.ofReal_div_of_pos hSpos, ofReal_measureReal hS_top]
  have hcK : c * ENNReal.ofReal K =
      ENNReal.ofReal (μ.real (ball 0 1) * d ^ (n + 1) / μ.real S) := by
    rw [hc, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [K]
    field_simp
    ring
  have hKp : ENNReal.ofReal K ^ (p - 1) * ENNReal.ofReal K = ENNReal.ofReal K ^ p := by
    rw [ENNReal.ofReal_rpow_of_nonneg hK (by linarith), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hK hp0, ← Real.rpow_add_one' hK (by linarith), sub_add_cancel]
  calc
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ^ p ∂μ ≤ ∫⁻ x in Ω, c ^ p * V x ^ p ∂μ :=
      setLIntegral_mono' hΩ.measurableSet fun x hx => by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact ENNReal.rpow_le_rpow (hpoint x hx) hp0
    _ = c ^ p * ∫⁻ x in Ω, V x ^ p ∂μ := lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hp0 (hc ▸ ENNReal.ofReal_ne_top))
    _ ≤ c ^ p * (ENNReal.ofReal K ^ p * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) := by
      rw [← hKp]
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hp0, hcK,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0]

/-- **The Poincaré–Wirtinger inequality on a convex domain.** If `u` is `C¹` on a bounded convex
open set `Ω` and `S ⊆ Ω` has positive measure, then for `1 ≤ p < ∞` the `Lᵖ(Ω)` seminorm of the
deviation of `u` from its mean over `S` is at most `μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` times
the `Lᵖ(Ω)` seminorm of the derivative of `u`, where `n` is the dimension of the space. -/
theorem eLpNorm_sub_setAverage_le_of_convex (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) p (μ.restrict Ω) ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) *
        eLpNorm (fderiv ℝ u) p (μ.restrict Ω) :=
  eLpNorm_le_eLpNorm_of_lintegral_rpow_le (by positivity) (zero_lt_one.trans_le hp).ne' hp'
    (lintegral_enorm_sub_setAverage_rpow_le_of_convex hΩ hΩc hb hu hS hS₀
      (by simpa using ENNReal.toReal_mono hp' hp))

end TauCeti
