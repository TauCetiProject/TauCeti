/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Smoothing
import TauCeti.Analysis.Convolution.Young
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Off-diagonal estimates for the heat semigroup

The heat flow improves integrability from `Lᵖ` to every `Lᵠ` with `p ≤ q`, with the
scale-invariant bound `(4πt)^(-(d/2)(1/p - 1/q))`. Young's convolution inequality and
the Gaussian kernel bound give this estimate for Banach-space-valued functions, including
the endpoint `q = ∞`. Splitting the flow into two positive time steps combines this gain
with the diagonal derivative estimates.
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

/-- **Off-diagonal derivative estimates.** For each order `m`, a constant depending only
on `m` and the dimension bounds `‖D^m e^{tΔ} f‖_q` by
`C t^(-m/2 - (d/2)(1/p - 1/q)) ‖f‖_p`, simultaneously for `1 ≤ p ≤ q ≤ ∞`, `p < ∞`.
The estimate holds for every continuous representative of the heat evolution. -/
theorem exists_eLpNorm_iteratedFDeriv_le_of_ae_eq_heatSemigroup_of_le (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃p q : ℝ≥0∞⦄ [Fact (1 ≤ p)] (hp : p ≠ ∞), p ≤ q →
      ∀ ⦃t : ℝ≥0⦄, t ≠ 0 → ∀ (f : Lp F p (volume : Measure E)) ⦃u : E → F⦄,
        Continuous u → (heatSemigroup hp t f : E → F) =ᵐ[volume] u →
          eLpNorm (iteratedFDeriv ℝ m u) q volume ≤
            ENNReal.ofReal (C * (t : ℝ) ^ (-(m : ℝ) / 2 -
              (Module.finrank ℝ E : ℝ) / 2 * (1 / p.toReal - 1 / q.toReal))) *
                eLpNorm f p volume := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_heatKernel_convolution_le (E := E) (F := F) m
  refine ⟨C * 2 ^ ((m : ℝ) / 2), by positivity, fun p q _ hp hpq t ht f u hu hfu => ?_⟩
  let s : ℝ≥0 := t / 2
  have hs : (0 : ℝ) < s := by positivity
  let g := heatSemigroup hp s f
  have hbound := ae_le_lpNorm_exponent_top
    (memLp_heatSemigroup hp le_top (NNReal.coe_ne_zero.1 hs.ne') f)
  have hug : u = heatKernel (s : ℝ) ⋆ (g : E → F) :=
    (Continuous.ae_eq_iff_eq volume hu (contDiff_heatKernel_convolution hs hbound).continuous).1
      (hfu.symm.trans (heatSemigroup_ae_eq_convolution_heatSemigroup_half hp ht f))
  let a : ℝ := (Module.finrank ℝ E : ℝ) / 2 * (1 / p.toReal - 1 / q.toReal)
  have ha : 0 ≤ a := by
    have hi := ENNReal.toReal_mono
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne')
      (ENNReal.inv_le_inv.2 hpq)
    exact mul_nonneg (by positivity) (sub_nonneg.2
      (by simpa only [ENNReal.toReal_inv, one_div] using hi))
  have hsmall : (4 * π * (s : ℝ)) ^ (-a) ≤ (t : ℝ) ^ (-a) := by
    have he : 4 * π * (s : ℝ) = (2 * π) * (t : ℝ) := by simp [s]; ring
    rw [he, mul_rpow (by positivity) t.coe_nonneg]
    exact mul_le_of_le_one_left (by positivity)
      (rpow_le_one_of_one_le_of_nonpos (by linarith [two_le_pi]) (by linarith))
  have hscale : (s : ℝ) ^ (-(m : ℝ) / 2) =
      2 ^ ((m : ℝ) / 2) * (t : ℝ) ^ (-(m : ℝ) / 2) := by
    rw [NNReal.coe_div, NNReal.coe_ofNat, div_rpow t.coe_nonneg zero_le_two,
      div_eq_inv_mul, ← rpow_neg zero_le_two, neg_div, neg_neg]
  rw [hug]
  grw [hC hs (Lp.aestronglyMeasurable g) hbound (le_trans Fact.out hpq),
    eLpNorm_heatSemigroup_le hp hpq (NNReal.coe_ne_zero.1 hs.ne')]
  have he : -(Module.finrank ℝ E : ℝ) / 2 * (1 / p.toReal - 1 / q.toReal) = -a := by
    dsimp [a]; ring
  rw [he]
  grw [hsmall]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hscale]
  apply le_of_eq
  have he' : -(m : ℝ) / 2 - (Module.finrank ℝ E : ℝ) / 2 *
      (1 / p.toReal - 1 / q.toReal) = -(m : ℝ) / 2 + -a := by dsimp [a]; ring
  rw [he', rpow_add (by positivity : 0 < (t : ℝ))]
  congr 2
  ring

end TauCeti
