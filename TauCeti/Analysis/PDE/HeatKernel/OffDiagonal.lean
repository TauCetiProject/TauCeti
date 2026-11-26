/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
import TauCeti.Analysis.Convolution.Young

/-!
# Off-diagonal estimates for the heat semigroup

The heat flow improves integrability from `Lᵖ` to every `Lᵠ` with `p ≤ q`, with the
scale-invariant bound `(4πt)^(-(d/2)(1/p - 1/q))`. Young's convolution inequality and
the Gaussian kernel bound give this estimate for Banach-space-valued functions, including
the endpoint `q = ∞`. These estimates supply the integrability gain used in derivative
smoothing bounds.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real
open scoped Convolution ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Off-diagonal heat estimate.** For `1 ≤ p ≤ q ≤ ∞`, convolution with `K_t`
maps `Lᵖ` to `Lᵠ` with constant `(4πt)^(-(d/2)(1/p - 1/q))`.
The extended norm formulation also applies when the input norm is infinite. -/
theorem eLpNorm_heatKernel_convolution_le {t : ℝ} (ht : 0 < t) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) {f : E → F} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (heatKernel t ⋆ f) q volume ≤
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 *
        (1 / p.toReal - 1 / q.toReal))) * eLpNorm f p volume := by
  let r : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hpi : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hqi : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have hr : 1 ≤ r := by
    apply ENNReal.one_le_inv.2
    exact tsub_le_iff_right.2 (by simpa [add_comm] using add_le_add_left hqi 1)
  have hrp : r⁻¹ + p⁻¹ = 1 + q⁻¹ := by
    simp only [r, inv_inv]
    exact tsub_add_cancel_of_le (hpi.trans le_self_add)
  have hreal : 1 / r.toReal + 1 / p.toReal = 1 + 1 / q.toReal := by
    have h := congrArg ENNReal.toReal hrp
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hr).ne')
        (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp).ne'),
      ENNReal.toReal_add ENNReal.one_ne_top
        (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le (hp.trans hpq)).ne')] at h
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_one, one_div] using h
  have he : 1 - 1 / r.toReal = 1 / p.toReal - 1 / q.toReal := by linarith
  have h := eLpNorm_convolution_le_of_inv_add_inv_eq (.lsmul ℝ ℝ) hr hp hrp
    ((contDiff_heatKernel (k := ⊤) t).continuous.aestronglyMeasurable) hf
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul, eLpNorm_heatKernel_le ht hr] at h
  simpa only [he] using h

variable [CompleteSpace F]

/-- At positive times the `Lᵖ` heat semigroup satisfies the full `Lᵖ`–`Lᵠ` estimate,
including `q = ∞`. -/
theorem eLpNorm_heatSemigroup_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hpq : p ≤ q) {t : ℝ≥0} (ht : t ≠ 0) (f : Lp F p (volume : Measure E)) :
    eLpNorm (heatSemigroup hp t f) q volume ≤
      ENNReal.ofReal ((4 * π * (t : ℝ)) ^ (-(Module.finrank ℝ E : ℝ) / 2 *
        (1 / p.toReal - 1 / q.toReal))) * eLpNorm f p volume := by
  rw [eLpNorm_congr_ae (heatSemigroup_ae_eq_convolution_coeFn hp ht f)]
  exact eLpNorm_heatKernel_convolution_le (by positivity) Fact.out hpq (Lp.aestronglyMeasurable f)

/-- Heat evolution sends finite-`p` data to every larger `Lᵠ` space at positive times. -/
theorem memLp_heatSemigroup {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hpq : p ≤ q) {t : ℝ≥0} (ht : t ≠ 0) (f : Lp F p (volume : Measure E)) :
    MemLp (heatSemigroup hp t f : E → F) q volume :=
  (eLpNorm_heatSemigroup_le hp hpq ht f).trans_lt (by finiteness)

end TauCeti
