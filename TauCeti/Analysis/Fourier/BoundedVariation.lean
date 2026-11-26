/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Integral

import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.BoundedVariation.OneDimensional.Basic
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Fourier decay for functions of bounded variation

This module proves Fourier transform decay bounds on `ℝ` for functions of bounded variation and
for absolutely continuous primitives whose derivative has bounded variation.

* **Bounded variation decay.** For an integrable function `f : ℝ → E` of bounded variation into a
  complex Banach space, pairing `BoundedVariationOn.integral_deriv_smul_eq_neg_integral_lsmul`
  with the cutoff characters `φ_n(x) = χ(x / (n + 1)) 𝐞 (-(x * ξ))` and passing to the limit
  gives the exact identity
  `(2 * π * I * ξ) • 𝓕 f ξ = ∫ᵛ x, (𝐞 (-(x * ξ)) : ℂ) ∂[lsmul ℝ ℂ; hbv.vectorMeasure]`.
  Taking norms via `BoundedVariationOn.variation_vectorMeasure_univ_le` yields
  `2 * π * |ξ| * ‖𝓕 f ξ‖ ≤ (eVariationOn f univ).toReal` for all `ξ : ℝ` (without
  `[CompleteSpace E]`, as the Bochner integral vanishes on non-complete spaces), and hence
  `‖𝓕 f ξ‖ ≤ (eVariationOn f univ).toReal / (2 * π * |ξ|)` for `ξ ≠ 0`. The constant `1 / (2π)`
  is sharp and attained by `1_[0,1]` at `ξ = 1 / 2`.
* **Absolutely continuous primitive with BV derivative.** If `f` and `g` are integrable and
  `f x = f a + ∫ t in a..x, g t`, then `f` tends to `0` at `±∞` (via
  `MeasureTheory.IntegrableAtFilter.tendsto_zero_atTop_of_eq_add_integral` and its `atBot`
  counterpart) and
  Fubini integration by parts on `[-R, R]` via
  `TauCeti.intervalIntegral.integral_deriv_smul_add_eq_sub_of_le`
  gives `𝓕 g ξ = (2 * π * I * ξ) • 𝓕 f ξ` in any complex normed space. If `g` also has bounded
  variation, then `(2 * π * |ξ|) ^ 2 * ‖𝓕 f ξ‖ ≤ (eVariationOn g univ).toReal` and
  `(1 + ξ ^ 2) * ‖𝓕 f ξ‖ ≤ (∫ x, ‖f x‖) + (eVariationOn g univ).toReal / (4 * π ^ 2)`.
  The constant `1 / (2π)²` is sharp and attained by the tent `max 0 (1 - |x|)` at `ξ = 1 / 2`.

## Main declarations

* `MeasureTheory.Integrable.smul_fourier_eq_integral_vectorMeasure`: exact integration-by-parts
  identity relating `(2 * π * I * ξ) • 𝓕 f ξ` to the vector-measure integral of `𝐞 (-(x * ξ))`
  against `hbv.vectorMeasure`.
* `MeasureTheory.Integrable.two_pi_abs_mul_norm_fourier_le_eVariationOn` and
  `MeasureTheory.Integrable.norm_fourier_le_eVariationOn_div`: `O(1 / |ξ|)` Fourier decay for
  integrable BV functions.
* `MeasureTheory.Integrable.fourier_eq_smul_fourier_of_eq_add_integral`:
  `𝓕 g ξ = (2 * π * I * ξ) • 𝓕 f ξ` for integrable `f, g` with `f x = f a + ∫ t in a..x, g t`.
* `MeasureTheory.Integrable.two_pi_abs_sq_mul_norm_fourier_le_eVariationOn`,
  `MeasureTheory.Integrable.norm_fourier_le_eVariationOn_div_sq`, and
  `MeasureTheory.Integrable.one_add_sq_mul_norm_fourier_le_of_boundedVariationOn_deriv`:
  `O(1 / ξ²)` decay for a primitive whose derivative has bounded variation.

## References

* A. Kontorovich, T. Tao, *Prime Number Theorem And ...*, Lemmas 3.1.4–3.1.6.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Chapter I.
-/

public section

open Complex Filter MeasureTheory Set Topology
open scoped FourierTransform Real

/-! ### Bounded variation Fourier decay -/

private theorem hasDerivAt_cutoff_phase (χ : ContDiffBump (0 : ℝ)) (R ξ x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (χ (t / R) : ℂ) * (𝐞 (-(t * ξ)) : ℂ))
      (((deriv χ (x / R) / R : ℝ) : ℂ) * (𝐞 (-(x * ξ)) : ℂ) +
        (χ (x / R) : ℂ) * ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ))) x := by
  have hχd : HasDerivAt (fun t : ℝ ↦ χ (t / R)) (deriv χ (x / R) / R) x := by
    have hdiv : HasDerivAt (fun t : ℝ ↦ t / R) (1 / R) x := (hasDerivAt_id x).div_const R
    have hcomp :=
      ((χ.contDiff (n := 1)).differentiable one_ne_zero (x / R)).hasDerivAt.comp x hdiv
    simpa [Function.comp_def, div_eq_mul_inv] using hcomp
  have hphase : HasDerivAt (fun t : ℝ ↦ (𝐞 (-(t * ξ)) : ℂ))
      ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ)) x := by
    refine ((Real.hasDerivAt_fourierChar (-(x * ξ))).scomp x
      (((hasDerivAt_id x).mul_const ξ).neg)).congr_deriv ?_
    rw [Complex.real_smul]
    push_cast
    ring
  exact hχd.ofReal_comp.mul hphase

private theorem tendsto_cutoff_deriv_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (χ : ContDiffBump (0 : ℝ)) {f : ℝ → E} (hf : Integrable f) (ξ : ℝ) :
    Tendsto (fun n : ℕ ↦
      ∫ x, (((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) *
        (𝐞 (-(x * ξ)) : ℂ)) • f x)
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ :=
    ((χ.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
      χ.hasCompactSupport.deriv
  have hbound (n : ℕ) :
      ‖∫ x, (((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) *
          (𝐞 (-(x * ξ)) : ℂ)) • f x‖ ≤
        (M / ((n : ℝ) + 1)) * ∫ x, ‖f x‖ := by
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc
      ‖∫ x, (((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) *
          (𝐞 (-(x * ξ)) : ℂ)) • f x‖
        ≤ ∫ x, ‖(((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) *
            (𝐞 (-(x * ξ)) : ℂ)) • f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (M / ((n : ℝ) + 1)) * ‖f x‖ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
            (hf.norm.const_mul _) (ae_of_all _ fun x ↦ ?_)
          dsimp only
          rw [norm_smul, Complex.norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
            Real.norm_eq_abs, abs_div, abs_of_pos hR]
          gcongr
          simpa [Real.norm_eq_abs] using hM (x / ((n : ℝ) + 1))
      _ = (M / ((n : ℝ) + 1)) * ∫ x, ‖f x‖ := integral_const_mul _ _
  refine squeeze_zero_norm hbound ?_
  have hdiv : Tendsto (fun n : ℕ ↦ M / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simpa using hdiv.mul_const (∫ x, ‖f x‖)

private theorem tendsto_cutoff_phase_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (χ : ContDiffBump (0 : ℝ)) {f : ℝ → E} (hf : Integrable f) (ξ : ℝ) :
    Tendsto (fun n : ℕ ↦
      ∫ x, ((χ (x / ((n : ℝ) + 1)) : ℂ) * ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ))) • f x)
      atTop (𝓝 ((-2 * π * I * ξ) • 𝓕 f ξ)) := by
  have hmain : Tendsto (fun n : ℕ ↦
      ∫ x, (χ (x / ((n : ℝ) + 1)) : ℂ) • (𝐞 (-(x * ξ)) • f x))
      atTop (𝓝 (∫ x, 𝐞 (-(x * ξ)) • f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖) ?_ hf.norm ?_ ?_
    · intro n
      have hχc : Continuous (fun x : ℝ ↦ (χ (x / ((n : ℝ) + 1)) : ℂ)) :=
        Complex.continuous_ofReal.comp (χ.continuous.comp (continuous_id.div_const _))
      have hpc : Continuous (fun x : ℝ ↦ 𝐞 (-(x * ξ))) := by fun_prop
      exact hχc.aestronglyMeasurable.smul (hpc.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    · intro n
      refine ae_of_all _ fun x ↦ ?_
      rw [norm_smul, Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg χ.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    · refine ae_of_all _ fun x ↦ tendsto_const_nhds.congr' ?_
      have hlim : Tendsto (fun n : ℕ ↦ x / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      filter_upwards [hlim.eventually χ.eventuallyEq_one] with n hn
      simp [hn]
  have heq (n : ℕ) :
      ∫ x, ((χ (x / ((n : ℝ) + 1)) : ℂ) * ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ))) • f x =
        (-2 * π * I * ξ) • ∫ x, (χ (x / ((n : ℝ) + 1)) : ℂ) • (𝐞 (-(x * ξ)) • f x) := by
    rw [← integral_smul]
    congr 1 with x
    rw [Circle.smul_def, smul_smul, smul_smul]
    congr 1
    ring
  simp_rw [heq, Real.fourier_real_eq]
  exact hmain.const_smul (-2 * π * I * ξ)

private theorem tendsto_cutoff_vectorMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (χ : ContDiffBump (0 : ℝ)) {f : ℝ → E}
    (hbv : BoundedVariationOn f univ) (ξ : ℝ) :
    Tendsto (fun n : ℕ ↦
      ∫ᵛ x, (χ (x / ((n : ℝ) + 1)) : ℂ) * (𝐞 (-(x * ξ)) : ℂ)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; hbv.vectorMeasure])
      atTop (𝓝 (∫ᵛ x, (𝐞 (-(x * ξ)) : ℂ)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; hbv.vectorMeasure])) := by
  refine VectorMeasure.tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
  · refine Eventually.of_forall fun n ↦ ?_
    have hpc : Continuous (fun x : ℝ ↦ (𝐞 (-(x * ξ)) : ℂ)) := by fun_prop
    exact ((Complex.continuous_ofReal.comp
      (χ.continuous.comp (continuous_id.div_const _))).mul hpc).aestronglyMeasurable
  · refine ⟨1, Eventually.of_forall fun n ↦ ae_of_all _ fun x ↦ ?_⟩
    rw [Complex.norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact χ.le_one
  · refine ae_of_all _ fun x ↦ tendsto_const_nhds.congr' ?_
    have hlim : Tendsto (fun n : ℕ ↦ x / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    filter_upwards [hlim.eventually χ.eventuallyEq_one] with n hn
    simp [hn]

private theorem cutoff_ibp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (χ : ContDiffBump (0 : ℝ)) {f : ℝ → E} (hf : Integrable f)
    (hbv : BoundedVariationOn f univ) (ξ : ℝ) (n : ℕ) :
    (∫ x, (((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) *
        (𝐞 (-(x * ξ)) : ℂ)) • f x) +
    (∫ x, ((χ (x / ((n : ℝ) + 1)) : ℂ) *
        ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ))) • f x) =
      -∫ᵛ x, (χ (x / ((n : ℝ) + 1)) : ℂ) * (𝐞 (-(x * ξ)) : ℂ)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; hbv.vectorMeasure] := by
  let φ : ℝ → ℂ := fun x ↦ (χ (x / ((n : ℝ) + 1)) : ℂ) * (𝐞 (-(x * ξ)) : ℂ)
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp_cd : ContDiff ℝ 1 (fun x : ℝ ↦ (𝐞 (-(x * ξ)) : ℂ)) :=
    (contDiff_id.mul contDiff_const).neg.fourierChar
  have hφ_cd : ContDiff ℝ 1 φ :=
    (ofRealCLM.contDiff.comp ((χ.contDiff (n := 1)).comp (contDiff_id.div_const _))).mul hp_cd
  have hχ_cs : HasCompactSupport (fun x : ℝ ↦ χ (x / ((n : ℝ) + 1))) := by
    simpa only [div_eq_inv_mul, smul_eq_mul] using
      χ.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')
  have hφ_cs : HasCompactSupport φ :=
    (hχ_cs.comp_left Complex.ofReal_zero).mul_right
  have h1 : Integrable (fun x ↦ (((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) *
      (𝐞 (-(x * ξ)) : ℂ)) • f x) := by
    have hcont : Continuous (fun x : ℝ ↦
        ((deriv χ (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) : ℝ) : ℂ) * (𝐞 (-(x * ξ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp
        ((((χ.contDiff (n := 1)).continuous_deriv le_rfl).comp
          (continuous_id.div_const _)).div_const _)).mul hp_cd.continuous
    obtain ⟨M, hM⟩ :=
      ((χ.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
        χ.hasCompactSupport.deriv
    refine (hf.norm.const_mul (M / ((n : ℝ) + 1))).mono'
      (hcont.aestronglyMeasurable.smul hf.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, Complex.norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_eq_abs, abs_div, abs_of_pos hR]
    gcongr
    simpa [Real.norm_eq_abs] using hM (x / ((n : ℝ) + 1))
  have h2 : Integrable (fun x ↦ ((χ (x / ((n : ℝ) + 1)) : ℂ) *
      ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ))) • f x) := by
    have hcont : Continuous (fun x : ℝ ↦ (χ (x / ((n : ℝ) + 1)) : ℂ) *
        ((-2 * π * I * ξ) * (𝐞 (-(x * ξ)) : ℂ))) :=
      (Complex.continuous_ofReal.comp
        (χ.continuous.comp (continuous_id.div_const _))).mul
        (continuous_const.mul hp_cd.continuous)
    refine (hf.norm.const_mul ‖(-2 * π * I * ξ : ℂ)‖).mono'
      (hcont.aestronglyMeasurable.smul hf.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    calc χ (x / ((n : ℝ) + 1)) * ‖(-2 * π * I * ξ : ℂ)‖ * ‖f x‖
      ≤ 1 * ‖(-2 * π * I * ξ : ℂ)‖ * ‖f x‖ := by gcongr; exact χ.le_one
      _ = ‖(-2 * π * I * ξ : ℂ)‖ * ‖f x‖ := by rw [one_mul]
  rw [← integral_add h1 h2, ← hbv.integral_deriv_smul_eq_neg_integral_lsmul hφ_cd hφ_cs]
  congr 1 with x
  rw [(hasDerivAt_cutoff_phase χ ((n : ℝ) + 1) ξ x).deriv, add_smul]

namespace MeasureTheory.Integrable

/-- **Integration by parts for the Fourier transform of a function of bounded variation.**
For an integrable function `f : ℝ → E` of bounded variation into a complex Banach space, multiplying
its Fourier transform by `2 * π * I * ξ` yields the integral of `x ↦ (𝐞 (-(x * ξ)) : ℂ)` against
its distributional derivative measure `hbv.vectorMeasure`. -/
theorem smul_fourier_eq_integral_vectorMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℝ → E} (hf : Integrable f)
    (hbv : BoundedVariationOn f univ) (ξ : ℝ) :
    (2 * π * I * ξ) • 𝓕 f ξ =
      ∫ᵛ x, (𝐞 (-(x * ξ)) : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; hbv.vectorMeasure] := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hLHS := (tendsto_cutoff_deriv_integral χ hf ξ).add
    (tendsto_cutoff_phase_integral χ hf ξ)
  simp only [zero_add] at hLHS
  have hRHS := (tendsto_cutoff_vectorMeasure χ hbv ξ).neg
  have heq : (-2 * π * I * ξ) • 𝓕 f ξ =
      -∫ᵛ x, (𝐞 (-(x * ξ)) : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; hbv.vectorMeasure] :=
    tendsto_nhds_unique (hLHS.congr (cutoff_ibp χ hf hbv ξ)) hRHS
  have hneg : (2 * π * I * ξ) • 𝓕 f ξ = -((-2 * π * I * ξ) • 𝓕 f ξ) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hneg, heq, neg_neg]

/-- Multiplicative Fourier decay bound for an integrable function of bounded variation on `ℝ`:
`2 * π * |ξ| * ‖𝓕 f ξ‖ ≤ (eVariationOn f univ).toReal` for every real `ξ`, including `ξ = 0`.
No completeness assumption on `E` is needed because the Bochner integral vanishes on non-complete
spaces. -/
theorem two_pi_abs_mul_norm_fourier_le_eVariationOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} (hf : Integrable f) (hbv : BoundedVariationOn f univ)
    (ξ : ℝ) :
    2 * π * |ξ| * ‖𝓕 f ξ‖ ≤ (eVariationOn f univ).toReal := by
  by_cases hE : CompleteSpace E
  · have hnorm_lhs : ‖(2 * π * I * ξ) • 𝓕 f ξ‖ = 2 * π * |ξ| * ‖𝓕 f ξ‖ := by
      rw [norm_smul]
      simp [abs_of_pos Real.pi_pos, mul_assoc]
    rw [← hnorm_lhs, hf.smul_fourier_eq_integral_vectorMeasure hbv ξ]
    have hconst : ∀ᵐ x ∂hbv.vectorMeasure.variation, ‖(𝐞 (-(x * ξ)) : ℂ)‖ ≤ 1 :=
      ae_of_all _ fun _ ↦ by simp
    calc
      ‖∫ᵛ x, (𝐞 (-(x * ξ)) : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; hbv.vectorMeasure]‖
        ≤ 1 * ‖(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E)‖ *
            hbv.vectorMeasure.variation.real univ :=
          VectorMeasure.norm_integral_le_of_norm_le_const hconst
      _ ≤ 1 * 1 * (eVariationOn f univ).toReal := by
          gcongr
          · exact ContinuousLinearMap.opNorm_lsmul_le
          · exact ENNReal.toReal_mono hbv hbv.variation_vectorMeasure_univ_le
      _ = (eVariationOn f univ).toReal := by rw [one_mul, one_mul]
  · have h0 : 𝓕 f ξ = 0 := by
      rw [Real.fourier_eq', integral_of_not_completeSpace hE]
    rw [h0, norm_zero, mul_zero]
    exact ENNReal.toReal_nonneg

/-- **Fourier decay for functions of bounded variation** (Kontorovich–Tao, Lemma 3.1.4).
If `f : ℝ → E` is integrable and of bounded variation on `ℝ`, then
`‖𝓕 f ξ‖ ≤ (eVariationOn f univ).toReal / (2 * π * |ξ|)` for every real `ξ ≠ 0`.
The constant `1 / (2π)` is sharp and attained by `1_[0,1]` at `ξ = 1 / 2`. -/
theorem norm_fourier_le_eVariationOn_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} (hf : Integrable f) (hbv : BoundedVariationOn f univ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ (eVariationOn f univ).toReal / (2 * π * |ξ|) := by
  have hpos : 0 < 2 * π * |ξ| := mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.mpr hξ)
  rw [le_div_iff₀' hpos]
  exact hf.two_pi_abs_mul_norm_fourier_le_eVariationOn hbv ξ

/-! ### Absolutely continuous primitives and derivatives of bounded variation -/

/-- **Fourier transform of an almost-everywhere derivative via an indefinite integral.**
If `f, g : ℝ → E` are integrable and `f x = f a + ∫ t in a..x, g t` for all `x : ℝ`, then
`𝓕 g ξ = (2 * π * I * ξ) • 𝓕 f ξ` for every `ξ : ℝ`. Neither continuity of `g` nor bounded
variation nor completeness of `E` is assumed. -/
theorem fourier_eq_smul_fourier_of_eq_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : ℝ → E} {a : ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfg : ∀ x, f x = f a + ∫ t in a..x, g t) (ξ : ℝ) :
    𝓕 g ξ = (2 * π * I * ξ) • 𝓕 f ξ := by
  by_cases hE : CompleteSpace E
  · have hfg_shift (R x : ℝ) : f x = f (-R) + ∫ t in -R..x, g t := by
      have h1 : f x - f (-R) = (∫ t in a..x, g t) - ∫ t in a..(-R), g t := by
        rw [hfg x, hfg (-R)]; abel
      have h2 := _root_.intervalIntegral.integral_add_adjacent_intervals (a := a) (b := -R)
        (c := x) hg.intervalIntegrable hg.intervalIntegrable
      rw [eq_add_of_sub_eq' h1, ← h2]
      abel
    let φ : ℝ → ℂ := fun x ↦ (𝐞 (-(x * ξ)) : ℂ)
    have hφ_cd : ContDiff ℝ 1 φ := (contDiff_id.mul contDiff_const).neg.fourierChar
    have hIBP (R : ℝ) (hR : 0 ≤ R) :
        ((-2 * π * I * ξ) • ∫ x in -R..R, 𝐞 (-(x * ξ)) • f x) +
        (∫ t in -R..R, 𝐞 (-(t * ξ)) • g t) =
          𝐞 (-(R * ξ)) • f R - 𝐞 (-(-R * ξ)) • f (-R) := by
      have h := TauCeti.intervalIntegral.integral_deriv_smul_add_eq_sub_of_le (a := -R) (b := R)
        (by linarith) hφ_cd hg.intervalIntegrable (fun x _ ↦ hfg_shift R x)
      have hderiv : (fun x ↦ deriv φ x • f x) =
          fun x ↦ (-2 * π * I * ξ) • (𝐞 (-(x * ξ)) • f x) := by
        ext x
        have hd : HasDerivAt φ ((-2 * π * I * ξ) * φ x) x := by
          refine ((Real.hasDerivAt_fourierChar (-(x * ξ))).scomp x
            (((hasDerivAt_id x).mul_const ξ).neg)).congr_deriv ?_
          rw [Complex.real_smul]; push_cast; ring
        rw [hd.deriv, Circle.smul_def, smul_smul]
      rw [hderiv, _root_.intervalIntegral.integral_smul] at h
      dsimp only [φ] at h
      simpa only [← Circle.smul_def] using h
    have hlim_f : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, 𝐞 (-(x * ξ)) • f x)
        atTop (𝓝 (𝓕 f ξ)) := by
      rw [Real.fourier_real_eq]
      exact intervalIntegral_tendsto_integral (hf.fourierChar_smul (by fun_prop))
        tendsto_neg_atTop_atBot tendsto_id
    have hlim_g : Tendsto (fun R : ℝ ↦ ∫ t in -R..R, 𝐞 (-(t * ξ)) • g t)
        atTop (𝓝 (𝓕 g ξ)) := by
      rw [Real.fourier_real_eq]
      exact intervalIntegral_tendsto_integral (hg.fourierChar_smul (by fun_prop))
        tendsto_neg_atTop_atBot tendsto_id
    have hf_top : Tendsto f atTop (𝓝 0) :=
      (hf.integrableAtFilter atTop).tendsto_zero_atTop_of_eq_add_integral
        hg.integrableOn (Eventually.of_forall hfg)
    have hf_bot : Tendsto f atBot (𝓝 0) :=
      (hf.integrableAtFilter atBot).tendsto_zero_atBot_of_eq_add_integral
        hg.integrableOn (Eventually.of_forall hfg)
    have hbd_pos : Tendsto (fun R : ℝ ↦ 𝐞 (-(R * ξ)) • f R) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| by
        simpa [Circle.norm_smul] using hf_top.norm
    have hbd_neg : Tendsto (fun R : ℝ ↦ 𝐞 (-(-R * ξ)) • f (-R)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| by
        simpa [Circle.norm_smul] using (hf_bot.comp tendsto_neg_atTop_atBot).norm
    have hsum_zero : (-2 * π * I * ξ) • 𝓕 f ξ + 𝓕 g ξ = 0 :=
      tendsto_nhds_unique
        (((hlim_f.const_smul _).add hlim_g).congr'
          (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR; exact hIBP R hR))
        (by simpa using hbd_pos.sub hbd_neg)
    have hneg : -((-2 * π * I * ξ) • 𝓕 f ξ) = (2 * π * I * ξ) • 𝓕 f ξ := by
      rw [← neg_smul]; congr 1; ring
    rw [← hneg]
    exact eq_neg_of_add_eq_zero_right hsum_zero
  · simp [Real.fourier_eq', integral_of_not_completeSpace hE]

/-- Multiplicative quadratic Fourier decay when the integrable derivative `g` of `f` has bounded
variation on `ℝ` (Kontorovich–Tao, Lemma 3.1.5). Holds for every real `ξ`, including `ξ = 0`. -/
theorem two_pi_abs_sq_mul_norm_fourier_le_eVariationOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : ℝ → E} {a : ℝ} (hf : Integrable f) (hg : Integrable g)
    (hg_bv : BoundedVariationOn g univ) (hfg : ∀ x, f x = f a + ∫ t in a..x, g t) (ξ : ℝ) :
    (2 * π * |ξ|) ^ 2 * ‖𝓕 f ξ‖ ≤ (eVariationOn g univ).toReal := by
  have h1 := hg.two_pi_abs_mul_norm_fourier_le_eVariationOn hg_bv ξ
  rw [hf.fourier_eq_smul_fourier_of_eq_add_integral hg hfg ξ, norm_smul] at h1
  have hnorm : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
    simp [abs_of_pos Real.pi_pos, mul_assoc]
  rw [hnorm] at h1
  simpa [sq, mul_assoc] using h1

/-- Quadratic Fourier decay when the integrable derivative `g` of `f` has bounded variation on `ℝ`
(Kontorovich–Tao, Lemma 3.1.5). The constant `1 / (2π)²` is sharp and attained by the tent
`x ↦ max 0 (1 - |x|)` at `ξ = 1 / 2`. -/
theorem norm_fourier_le_eVariationOn_div_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : ℝ → E} {a : ℝ} (hf : Integrable f) (hg : Integrable g)
    (hg_bv : BoundedVariationOn g univ) (hfg : ∀ x, f x = f a + ∫ t in a..x, g t)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ (eVariationOn g univ).toReal / (2 * π * |ξ|) ^ 2 := by
  have hpos : 0 < (2 * π * |ξ|) ^ 2 :=
    sq_pos_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.mpr hξ))
  rw [le_div_iff₀' hpos]
  exact hf.two_pi_abs_sq_mul_norm_fourier_le_eVariationOn hg hg_bv hfg ξ

/-- Combined `(1 + ξ²)` Fourier decay bound when the integrable derivative `g` of `f` has bounded
variation on `ℝ` (Kontorovich–Tao, Lemma 3.1.6). Holds for every real `ξ`, including `ξ = 0`. -/
theorem one_add_sq_mul_norm_fourier_le_of_boundedVariationOn_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℝ → E} {a : ℝ} (hf : Integrable f)
    (hg : Integrable g) (hg_bv : BoundedVariationOn g univ)
    (hfg : ∀ x, f x = f a + ∫ t in a..x, g t) (ξ : ℝ) :
    (1 + ξ ^ 2) * ‖𝓕 f ξ‖ ≤ (∫ x, ‖f x‖) + (eVariationOn g univ).toReal / (4 * π ^ 2) := by
  rw [add_mul, one_mul]
  refine add_le_add (Real.norm_fourier_le_integral_norm f ξ) ?_
  have h2 := hf.two_pi_abs_sq_mul_norm_fourier_le_eVariationOn hg hg_bv hfg ξ
  have h4pi : (0 : ℝ) < 4 * π ^ 2 := by positivity
  rw [le_div_iff₀' h4pi]
  have heq : (4 * π ^ 2) * (ξ ^ 2 * ‖𝓕 f ξ‖) = (2 * π * |ξ|) ^ 2 * ‖𝓕 f ξ‖ := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  rw [heq]
  exact h2

end MeasureTheory.Integrable

/-! ### Sharpness and boundary checks -/

section Checks

private theorem eVariationOn_indicator_Icc_zero_one :
    eVariationOn ((Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ))) univ = 2 := by
  let f : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ))
  have hleft : eVariationOn f (Iic 0) = 1 := by
    have h := eVariationOn.inter_Iic_eq_edist_of_const (f := f) (c := 0)
      ⟨-1, mem_univ _, by norm_num⟩ (mem_univ 0) fun x hx ↦
      indicator_of_notMem (fun h ↦ by linarith [hx.2.out, h.1]) _
    rw [univ_inter] at h
    rw [h]
    simp [f, edist_dist]
  have hmid : eVariationOn f (Icc 0 1) = 0 :=
    eVariationOn.constant_on <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp [f, indicator_of_mem hx, indicator_of_mem hy]
  have hright : eVariationOn f (Ici 1) = 1 := by
    have h := eVariationOn.inter_Ici_eq_edist_of_const (f := f) (c := 0)
      ⟨2, mem_univ _, by norm_num⟩ (mem_univ 1) fun x hx ↦
      indicator_of_notMem (fun h ↦ by linarith [hx.2.out, h.2]) _
    rw [univ_inter] at h
    rw [h]
    simp [f, edist_dist]
  have h01 : eVariationOn f (Iic 1) = 1 := by
    rw [← Iic_union_Icc_eq_Iic zero_le_one, eVariationOn.union f isGreatest_Iic
      (isLeast_Icc zero_le_one), hleft, hmid, add_zero]
  rw [← Iic_union_Ici (a := (1 : ℝ)), eVariationOn.union f isGreatest_Iic isLeast_Ici, h01, hright]
  norm_num

/-- Sharpness and `ξ ≠ 0` necessity check for
`MeasureTheory.Integrable.norm_fourier_le_eVariationOn_div`:
for `f = 1_[0,1]`, `eVariationOn f univ = 2`, at `ξ = 1 / 2` both sides equal `2 / π`, and at
`ξ = 0` we have `𝓕 f 0 = 1` while the right-hand side evaluates to the junk value `0`. -/
example :
    let f : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ ↦ 1)
    eVariationOn f univ = 2 ∧
      ‖𝓕 f (1 / 2)‖ = 2 / π ∧
      (eVariationOn f univ).toReal / (2 * π * |(1 / 2 : ℝ)|) = 2 / π ∧
      𝓕 f 0 = 1 ∧
      (eVariationOn f univ).toReal / (2 * π * |(0 : ℝ)|) = 0 := by
  intro f
  have hev : eVariationOn f univ = 2 := eVariationOn_indicator_Icc_zero_one
  have hf_half : 𝓕 f (1 / 2) = 2 / (π * I) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have heq : (fun x : ℝ ↦ Complex.exp (↑(-2 * π * x * (1 / 2)) * I) • f x) =
        (Icc (0 : ℝ) 1).indicator (fun x ↦ Complex.exp ((-(π : ℂ) * I) * x)) := by
      ext x
      by_cases hx : x ∈ Icc (0 : ℝ) 1
      · simp only [f, indicator_of_mem hx, smul_eq_mul, mul_one]
        congr 1; push_cast; ring
      · simp [f, hx]
    have hcne : -(π : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← _root_.intervalIntegral.integral_of_le zero_le_one, integral_exp_mul_complex hcne]
    have hexp : Complex.exp (-(π : ℂ) * I * (1 : ℝ)) = -1 := by
      have h1 : -(π : ℂ) * I * (1 : ℝ) = -(π * I) := by push_cast; ring
      rw [h1, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [hexp]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]
    have hne : (π : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp [hne]
    ring
  have hnorm_half : ‖𝓕 f (1 / 2)‖ = 2 / π := by
    rw [hf_half, norm_div, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have hrhs_half : (eVariationOn f univ).toReal / (2 * π * |(1 / 2 : ℝ)|) = 2 / π := by
    rw [hev]
    norm_num
    field_simp [Real.pi_ne_zero]
  have hf_zero : 𝓕 f 0 = 1 := by
    rw [Real.fourier_real_eq]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Complex.real_smul, mul_one,
      measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  exact ⟨hev, hnorm_half, hrhs_half, hf_zero, by simp⟩

private noncomputable def tentDeriv : ℝ → ℂ :=
  (Ico (-1 : ℝ) 0).indicator (fun _ ↦ 1) - (Ico (0 : ℝ) 1).indicator (fun _ ↦ 1)

private theorem tentDeriv_of_lt_neg_one {x : ℝ} (hx : x < -1) : tentDeriv x = 0 := by
  have h1 : x ∉ Ico (-1 : ℝ) 0 := fun h ↦ by linarith [h.1]
  have h2 : x ∉ Ico (0 : ℝ) 1 := fun h ↦ by linarith [h.1]
  simp [tentDeriv, h1, h2]

private theorem tentDeriv_of_mem_Ico_neg {x : ℝ} (h1 : -1 ≤ x) (h2 : x < 0) :
    tentDeriv x = 1 := by
  have hm : x ∈ Ico (-1 : ℝ) 0 := ⟨h1, h2⟩
  have hn : x ∉ Ico (0 : ℝ) 1 := fun h ↦ by linarith [h.1]
  simp [tentDeriv, hm, hn]

private theorem tentDeriv_of_mem_Ico_pos {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) :
    tentDeriv x = -1 := by
  have hn : x ∉ Ico (-1 : ℝ) 0 := fun h ↦ by linarith [h.2]
  have hm : x ∈ Ico (0 : ℝ) 1 := ⟨h1, h2⟩
  simp [tentDeriv, hn, hm]

private theorem tentDeriv_of_one_le {x : ℝ} (hx : 1 ≤ x) : tentDeriv x = 0 := by
  have h1 : x ∉ Ico (-1 : ℝ) 0 := fun h ↦ by linarith [h.2]
  have h2 : x ∉ Ico (0 : ℝ) 1 := fun h ↦ by linarith [h.2]
  simp [tentDeriv, h1, h2]

private theorem eVariationOn_tentDeriv : eVariationOn tentDeriv univ = 4 := by
  have h1 : eVariationOn tentDeriv (Iic (-1)) = 1 := by
    have h := eVariationOn.inter_Iic_eq_edist_of_const (f := tentDeriv) (c := 0)
      ⟨-2, mem_univ _, by norm_num⟩ (mem_univ (-1)) fun _ hx ↦ tentDeriv_of_lt_neg_one hx.2
    rw [univ_inter] at h
    rw [h, tentDeriv_of_mem_Ico_neg le_rfl (by norm_num), edist_dist]
    norm_num
  have h2 : eVariationOn tentDeriv (Icc (-1) 0) = 2 := by
    have hmem : (0 : ℝ) ∈ Ici (-1) := by norm_num
    have h := eVariationOn.inter_Iic_eq_edist_of_const (f := tentDeriv) (c := 1)
      ⟨-1, le_rfl, by norm_num⟩ hmem fun _ hx ↦ tentDeriv_of_mem_Ico_neg hx.1 hx.2
    rw [← Ici_inter_Iic, h, tentDeriv_of_mem_Ico_pos le_rfl zero_lt_one, edist_dist, dist_eq_norm]
    norm_num
  have h3 : eVariationOn tentDeriv (Icc 0 1) = 1 := by
    have hmem : (1 : ℝ) ∈ Ici 0 := zero_le_one
    have h := eVariationOn.inter_Iic_eq_edist_of_const (f := tentDeriv) (c := -1)
      ⟨0, le_rfl, zero_lt_one⟩ hmem fun _ hx ↦ tentDeriv_of_mem_Ico_pos hx.1 hx.2
    rw [← Ici_inter_Iic, h, tentDeriv_of_one_le le_rfl, edist_dist, dist_eq_norm]
    norm_num
  have h4 : eVariationOn tentDeriv (Ici 1) = 0 :=
    eVariationOn.constant_on <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [tentDeriv_of_one_le hx, tentDeriv_of_one_le hy]
  have h01 : eVariationOn tentDeriv (Iic 0) = 3 := by
    rw [← Iic_union_Icc_eq_Iic (by norm_num : (-1 : ℝ) ≤ 0),
      eVariationOn.union tentDeriv isGreatest_Iic (isLeast_Icc (by norm_num)), h1, h2]
    norm_num
  have h02 : eVariationOn tentDeriv (Iic 1) = 4 := by
    rw [← Iic_union_Icc_eq_Iic zero_le_one,
      eVariationOn.union tentDeriv isGreatest_Iic (isLeast_Icc zero_le_one), h01, h3]
    norm_num
  rw [← Iic_union_Ici (a := (1 : ℝ)), eVariationOn.union tentDeriv isGreatest_Iic isLeast_Ici,
    h02, h4, add_zero]

private theorem tentDeriv_integrable : Integrable tentDeriv := by
  have h1 : Integrable ((Ico (-1 : ℝ) 0).indicator (fun _ ↦ (1 : ℂ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  have h2 : Integrable ((Ico (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  exact h1.sub h2

private theorem tent_eq_add_integral (x : ℝ) :
    ((max (0 : ℝ) (1 - |x|) : ℝ) : ℂ) =
      ((max (0 : ℝ) (1 - |(0 : ℝ)|) : ℝ) : ℂ) + ∫ t in (0 : ℝ)..x, tentDeriv t := by
  have hf0 : ((max (0 : ℝ) (1 - |(0 : ℝ)|) : ℝ) : ℂ) = 1 := by simp
  have h0_1 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : ∫ t in (0 : ℝ)..y, tentDeriv t = -(y : ℂ) := by
    rw [_root_.intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ (-1 : ℂ)) hy0 fun _ ht ↦
      tentDeriv_of_mem_Ico_pos ht.1.le (ht.2.trans_le hy1),
      _root_.intervalIntegral.integral_const, Complex.real_smul]
    push_cast; ring
  have hm1_0 (y : ℝ) (hym : -1 ≤ y) (hy0 : y ≤ 0) : ∫ t in y..(0 : ℝ), tentDeriv t = -(y : ℂ) := by
    rw [_root_.intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ (1 : ℂ)) hy0 fun _ ht ↦
      tentDeriv_of_mem_Ico_neg (hym.trans ht.1.le) ht.2,
      _root_.intervalIntegral.integral_const, Complex.real_smul]
    push_cast; ring
  rw [hf0]
  by_cases h1 : 1 ≤ x
  · have htail : ∫ t in (1 : ℝ)..x, tentDeriv t = 0 := by
      rw [_root_.intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ (0 : ℂ)) h1 fun _ ht ↦
        tentDeriv_of_one_le ht.1.le, _root_.intervalIntegral.integral_const, smul_zero]
    have hadd := _root_.intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := 1) (c := x)
      tentDeriv_integrable.intervalIntegrable tentDeriv_integrable.intervalIntegrable
    rw [← hadd, h0_1 1 zero_le_one le_rfl, htail]
    rw [max_eq_left (by rw [abs_of_nonneg (by linarith)]; linarith)]; push_cast; ring
  · by_cases h0 : 0 ≤ x
    · rw [h0_1 x h0 (le_of_not_ge h1),
        max_eq_right (by rw [abs_of_nonneg h0]; linarith), abs_of_nonneg h0]
      push_cast; ring
    · by_cases hm : -1 ≤ x
      · rw [_root_.intervalIntegral.integral_symm, hm1_0 x hm (le_of_not_ge h0),
          abs_of_neg (lt_of_not_ge h0), max_eq_right (by linarith)]
        push_cast; ring
      · have htail : ∫ t in x..(-1 : ℝ), tentDeriv t = 0 := by
          rw [_root_.intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ (0 : ℂ))
            (le_of_not_ge hm) fun _ ht ↦ tentDeriv_of_lt_neg_one ht.2,
            _root_.intervalIntegral.integral_const, smul_zero]
        have hadd := _root_.intervalIntegral.integral_add_adjacent_intervals
          (a := x) (b := -1) (c := 0)
          tentDeriv_integrable.intervalIntegrable tentDeriv_integrable.intervalIntegrable
        rw [_root_.intervalIntegral.integral_symm, ← hadd, htail, hm1_0 (-1) le_rfl (by norm_num),
          max_eq_left (by rw [abs_of_neg (by linarith)]; linarith)]
        push_cast; ring

private theorem fourier_tentDeriv_half : 𝓕 tentDeriv (1 / 2) = 4 / (-(π : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hsplit : (fun x : ℝ ↦ Complex.exp (↑(-2 * π * x * (1 / 2)) * I) • tentDeriv x) =
      fun x ↦ (Ico (-1 : ℝ) 0).indicator (fun t ↦ Complex.exp ((-(π : ℂ) * I) * t)) x -
        (Ico (0 : ℝ) 1).indicator (fun t ↦ Complex.exp ((-(π : ℂ) * I) * t)) x := by
    ext x
    have hp : Complex.exp (↑(-2 * π * x * (1 / 2)) * I) = Complex.exp ((-(π : ℂ) * I) * x) := by
      congr 1; push_cast; ring
    simp only [tentDeriv, Pi.sub_apply, smul_eq_mul, mul_sub, hp]
    by_cases h1 : x ∈ Ico (-1 : ℝ) 0 <;> by_cases h2 : x ∈ Ico (0 : ℝ) 1 <;> simp [h1, h2]
  have hcont : Continuous (fun x : ℝ ↦ Complex.exp ((-(π : ℂ) * I) * x)) :=
    (continuous_const.mul Complex.continuous_ofReal).cexp
  have hi1 : Integrable ((Ico (-1 : ℝ) 0).indicator (fun x ↦
      Complex.exp ((-(π : ℂ) * I) * x))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (hcont.integrableOn_Icc.mono_set Ico_subset_Icc_self)
  have hi2 : Integrable ((Ico (0 : ℝ) 1).indicator (fun x ↦
      Complex.exp ((-(π : ℂ) * I) * x))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (hcont.integrableOn_Icc.mono_set Ico_subset_Icc_self)
  have hcne : -(π : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [hsplit, integral_sub hi1 hi2, integral_indicator measurableSet_Ico,
    integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    integral_Ico_eq_integral_Ioc,
    ← _root_.intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0),
    ← _root_.intervalIntegral.integral_of_le zero_le_one,
    integral_exp_mul_complex hcne, integral_exp_mul_complex hcne]
  have hexp_pos : Complex.exp (-(π : ℂ) * I * (1 : ℝ)) = -1 := by
    have h1 : -(π : ℂ) * I * (1 : ℝ) = -(π * I) := by push_cast; ring
    rw [h1, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hexp_neg : Complex.exp (-(π : ℂ) * I * (-1 : ℝ)) = -1 := by
    have h1 : -(π : ℂ) * I * (-1 : ℝ) = π * I := by push_cast; ring
    rw [h1, Complex.exp_pi_mul_I]
  rw [hexp_pos, hexp_neg]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  ring

private theorem integral_tent_eq_one : ∫ x : ℝ, max (0 : ℝ) (1 - |x|) = 1 := by
  have hsupp_eq : (fun x : ℝ ↦ max (0 : ℝ) (1 - |x|)) =
      (Icc (-1 : ℝ) 1).indicator (fun x ↦ 1 - |x|) := by
    ext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp [indicator_of_mem hx, max_eq_right (sub_nonneg.mpr (abs_le.mpr hx))]
    · rw [indicator_of_notMem hx]
      have habs : 1 < |x| := lt_of_not_ge fun h ↦ hx (abs_le.mp h)
      exact max_eq_left (by linarith)
  rw [hsupp_eq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← _root_.intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hcont : Continuous (fun x : ℝ ↦ 1 - |x|) := continuous_const.sub continuous_abs
  have hsplit := _root_.intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (-1 : ℝ)) (b := 0) (c := 1)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [← hsplit]
  have hL : ∫ x in (-1 : ℝ)..0, (1 - |x|) = 1 / 2 := by
    have heq : EqOn (fun x : ℝ ↦ 1 - |x|) (fun x ↦ 1 + x) (uIcc (-1) 0) := by
      intro x hx; rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
      dsimp only; rw [abs_of_nonpos hx.2]; ring
    rw [_root_.intervalIntegral.integral_congr heq]
    have hftc := _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 0)
      (f := fun x : ℝ ↦ x + x ^ 2 / 2) (f' := fun x ↦ 1 + x)
      (fun x _ ↦ ((hasDerivAt_id x).fun_add ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv
        (by norm_num))
      ((continuous_const.add continuous_id).intervalIntegrable _ _)
    rw [hftc]; norm_num
  have hR : ∫ x in (0 : ℝ)..1, (1 - |x|) = 1 / 2 := by
    have heq : EqOn (fun x : ℝ ↦ 1 - |x|) (fun x ↦ 1 - x) (uIcc 0 1) := by
      intro x hx; rw [uIcc_of_le zero_le_one] at hx
      dsimp only; rw [abs_of_nonneg hx.1]
    rw [_root_.intervalIntegral.integral_congr heq]
    have hftc := _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ ↦ x - x ^ 2 / 2) (f' := fun x ↦ 1 - x)
      (fun x _ ↦ ((hasDerivAt_id x).fun_sub ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv
        (by norm_num))
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)
    rw [hftc]; norm_num
  rw [hL, hR]; norm_num

/-- Sharpness check for `MeasureTheory.Integrable.norm_fourier_le_eVariationOn_div_sq` and
`MeasureTheory.Integrable.one_add_sq_mul_norm_fourier_le_of_boundedVariationOn_deriv`: for the tent
function `f x = max 0 (1 - |x|)` with derivative `g` of total variation `4`, both sides of the
quadratic decay bound equal `4 / π ^ 2` at `ξ = 1 / 2`, and `𝓕 f 0 = 1`, `∫ x, ‖f x‖ = 1`. -/
example :
    let f : ℝ → ℂ := fun t ↦ ((max (0 : ℝ) (1 - |t|) : ℝ) : ℂ)
    let g : ℝ → ℂ :=
      (Ico (-1 : ℝ) 0).indicator (fun _ ↦ 1) - (Ico (0 : ℝ) 1).indicator (fun _ ↦ 1)
    eVariationOn g univ = 4 ∧
      (∀ x, f x = f 0 + ∫ t in (0 : ℝ)..x, g t) ∧
      ‖𝓕 f (1 / 2)‖ = 4 / π ^ 2 ∧
      (eVariationOn g univ).toReal / (2 * π * |(1 / 2 : ℝ)|) ^ 2 = 4 / π ^ 2 ∧
      𝓕 f 0 = 1 ∧
      ∫ x, ‖f x‖ = 1 := by
  intro f g
  have hf_cont : Continuous f :=
    Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_abs))
  have hf_supp : HasCompactSupport f := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
    intro x hx
    simp only [Function.mem_support, ne_eq, f, ofReal_eq_zero] at hx
    by_contra hnot
    have habs : 1 < |x| := lt_of_not_ge fun h ↦ hnot (abs_le.mp h)
    exact hx (max_eq_left (by linarith))
  have hf_int : Integrable f := hf_cont.integrable_of_hasCompactSupport hf_supp
  have hrel := hf_int.fourier_eq_smul_fourier_of_eq_add_integral tentDeriv_integrable
    tent_eq_add_integral (1 / 2)
  have hf_half : 𝓕 f (1 / 2) = (4 / π ^ 2 : ℝ) := by
    have hne : (π : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : (π : ℂ) * I * 𝓕 f (1 / 2) = 4 / (-(π : ℂ) * I) := by
      have heq : (2 * (π : ℂ) * I * ((1 / 2 : ℝ) : ℂ)) = (π : ℂ) * I := by push_cast; ring
      rw [← fourier_tentDeriv_half, hrel, smul_eq_mul, heq]
    have hmul : 𝓕 f (1 / 2) = 4 / (-(π : ℂ) * I) / ((π : ℂ) * I) :=
      eq_div_of_mul_eq hne (by rw [mul_comm]; exact h2)
    rw [hmul]
    push_cast
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [Complex.I_sq]
  have hnorm_half : ‖𝓕 f (1 / 2)‖ = 4 / π ^ 2 := by
    rw [hf_half, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hrhs_half : (eVariationOn tentDeriv univ).toReal / (2 * π * |(1 / 2 : ℝ)|) ^ 2 =
      4 / π ^ 2 := by
    rw [eVariationOn_tentDeriv]; norm_num; field_simp [Real.pi_ne_zero]
  have hf_zero : 𝓕 f 0 = 1 := by
    rw [Real.fourier_real_eq]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
    dsimp only [f]
    rw [integral_complex_ofReal, integral_tent_eq_one]
    norm_num
  have hnorm_int : ∫ x, ‖f x‖ = 1 := by
    have heq : (fun x : ℝ ↦ ‖f x‖) = fun x ↦ max (0 : ℝ) (1 - |x|) := by
      ext x; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    rw [heq, integral_tent_eq_one]
  exact ⟨eVariationOn_tentDeriv, tent_eq_add_integral, hnorm_half, hrhs_half, hf_zero, hnorm_int⟩

end Checks
