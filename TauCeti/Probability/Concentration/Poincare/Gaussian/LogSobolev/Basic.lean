/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.Gaussian.LogSobolev.Sharpness
public import TauCeti.Probability.Concentration.Poincare.Herbst
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Concentration.Poincare.CompactSupport
import TauCeti.Probability.Concentration.Poincare.Tensorization
import TauCeti.Probability.Concentration.Poincare.Transport
import TauCeti.Probability.Distributions.Gaussian.LogSobolev

/-!
# The canonical Gaussian logarithmic Sobolev inequality and Lipschitz concentration

The standard Gaussian satisfies `MeasureTheory.Measure.LogSobolevInequality` with optimal constant
`1`, both on `ℝ` (`gaussianReal 0 1`) and on any finite-dimensional real inner product space `E`
(`stdGaussian E`, including dimension zero). More generally, `gaussianReal m v` satisfies
`LogSobolevInequality` with constant `v`. On any nontrivial finite-dimensional real inner product
space, the admissible constants for `stdGaussian E` are exactly those satisfying `1 ≤ C`.

Combining `logSobolevInequality_stdGaussian` with Herbst's argument in
`TauCeti.Probability.Concentration.Poincare.Herbst` yields the sharp Tsirelson–Ibragimov–Sudakov
sub-Gaussian concentration inequality for arbitrary `K`-Lipschitz functions `f : E → ℝ` without any
smoothness or prior integrability hypothesis: `f - ∫ f ∂stdGaussian E` has sub-Gaussian variance
proxy `K ^ 2`, and
`(stdGaussian E).real {x | t ≤ |f x - ∫ y, f y ∂stdGaussian E|} ≤ 2 * exp (-t² / (2 * K²))`.

## Main results

* `TauCeti.Probability.logSobolevInequality_gaussianReal_zero_one` and
  `TauCeti.Probability.logSobolevInequality_gaussianReal_zero_one_iff`: sharp `LogSobolevInequality`
  for `gaussianReal 0 1`.
* `TauCeti.Probability.logSobolevInequality_gaussianReal`:
  `(gaussianReal m v).LogSobolevInequality v` for all `m : ℝ` and `v : ℝ≥0`.
* `TauCeti.Probability.logSobolevInequality_stdGaussian` and
  `TauCeti.Probability.logSobolevInequality_stdGaussian_iff`: sharp `LogSobolevInequality` for
  `stdGaussian E`.
* `LipschitzWith.hasSubgaussianMGF_stdGaussian_sub_integral` and
  `LipschitzWith.measureReal_stdGaussian_setOf_le_abs_sub_integral_le`: sharp
  Gaussian Lipschitz concentration with variance proxy `K ^ 2`.

## References

* L. Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. **97** (1975), 1061–1083.
* B. S. Tsirelson, I. A. Ibragimov, and V. N. Sudakov, *Norms of Gaussian sample functions*,
  Lecture Notes in Math. **550**, Springer, 1976, 20–41.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §2.3.
* The statement layout parallels `TauCeti.Probability.Concentration.Poincare.Gaussian.Basic`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal

namespace TauCeti.Probability

/-- The standard Gaussian on `ℝ` satisfies the full smooth-test logarithmic Sobolev inequality with
constant `1`. -/
theorem logSobolevInequality_gaussianReal_zero_one :
    (gaussianReal 0 1).LogSobolevInequality 1 := by
  refine Measure.logSobolevInequality_iff_forall_hasCompactSupport.mpr fun f hf hc ↦ ?_
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨B, hB⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  simpa only [mul_one, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, sq_abs] using
    entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal (hf.of_le (by simp))
      ⟨A, by simpa only [Real.norm_eq_abs] using hA⟩
      ⟨B, by simpa only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] using hB⟩

/-- The standard Gaussian on `ℝ` satisfies the logarithmic Sobolev inequality with constant `C`
if and only if `1 ≤ C`. -/
theorem logSobolevInequality_gaussianReal_zero_one_iff {C : ℝ} :
    (gaussianReal 0 1).LogSobolevInequality C ↔ 1 ≤ C :=
  ⟨one_le_of_logSobolevInequality_gaussianReal,
    fun h ↦ logSobolevInequality_gaussianReal_zero_one.mono h⟩

/-- Every real Gaussian law `gaussianReal m v` (including the degenerate law `v = 0`) satisfies the
logarithmic Sobolev inequality with constant `v`. -/
theorem logSobolevInequality_gaussianReal (m : ℝ) (v : ℝ≥0) :
    (gaussianReal m v).LogSobolevInequality v := by
  have hscaled :=
    (logSobolevInequality_gaussianReal_zero_one.map_smul (a := √(v : ℝ))).map_add_right m
  have hv : NNReal.mk (√(v : ℝ) ^ 2) (sq_nonneg _) * 1 = v :=
    NNReal.eq (by simp [Real.sq_sqrt v.coe_nonneg])
  have hmul : (gaussianReal 0 1).map (fun x : ℝ ↦ √(v : ℝ) • x) = gaussianReal 0 v := by
    simpa only [smul_eq_mul, mul_zero, hv] using
      gaussianReal_map_const_mul (μ := 0) (v := 1) √(v : ℝ)
  rwa [hmul, gaussianReal_map_add_const, zero_add, Real.sq_sqrt v.coe_nonneg, mul_one] at hscaled

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian on a finite-dimensional real inner product space satisfies the full
smooth-test logarithmic Sobolev inequality with constant `1`. This includes dimension zero. -/
theorem logSobolevInequality_stdGaussian : (stdGaussian E).LogSobolevInequality 1 := by
  have hpi :
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).LogSobolevInequality 1 := by
    rw [← map_pi_eq_stdGaussian]
    exact Measure.LogSobolevInequality.piLp _ 1 fun _ ↦ logSobolevInequality_gaussianReal_zero_one
  simpa only [stdGaussian_map] using
    hpi.map_linearIsometryEquiv (stdOrthonormalBasis ℝ E).repr.symm

/-- On a nontrivial finite-dimensional real inner product space, the standard Gaussian has
logarithmic Sobolev constant `C` if and only if `1 ≤ C`. -/
theorem logSobolevInequality_stdGaussian_iff [Nontrivial E] {C : ℝ} :
    (stdGaussian E).LogSobolevInequality C ↔ 1 ≤ C :=
  ⟨fun h ↦ by
    have hpi :
        (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).LogSobolevInequality C := by
      simpa only [stdGaussian_map] using h.map_linearIsometryEquiv (stdOrthonormalBasis ℝ E).repr
    rw [← map_pi_eq_stdGaussian] at hpi
    exact one_le_of_logSobolevInequality_gaussianReal (hpi.of_piLp ⟨0, Module.finrank_pos⟩),
    fun h ↦ (logSobolevInequality_stdGaussian E).mono h⟩

end TauCeti.Probability

namespace LipschitzWith

open TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {K : ℝ≥0} {f : E → ℝ}

/-- **Gaussian Lipschitz MGF bound**: for any `K`-Lipschitz function `f : E → ℝ` on a
finite-dimensional real inner product space, `f - ∫ f ∂stdGaussian E` is sub-Gaussian with sharp
variance proxy `K ^ 2`. -/
theorem hasSubgaussianMGF_stdGaussian_sub_integral (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂stdGaussian E) (K ^ 2) (stdGaussian E) := by
  simpa using (logSobolevInequality_stdGaussian E).hasSubgaussianMGF_of_lipschitzWith hf

/-- **Gaussian Lipschitz concentration**: for any `K`-Lipschitz function `f : E → ℝ` on a
finite-dimensional real inner product space and `0 ≤ t`,
`(stdGaussian E).real {x | t ≤ |f x - ∫ y, f y ∂stdGaussian E|} ≤ 2 * exp (-t² / (2 * K²))`. -/
theorem measureReal_stdGaussian_setOf_le_abs_sub_integral_le (hf : LipschitzWith K f)
    {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian E).real {x | t ≤ |f x - ∫ y, f y ∂stdGaussian E|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (K : ℝ) ^ 2)) := by
  simpa only [one_mul] using
    (logSobolevInequality_stdGaussian E).measureReal_abs_sub_integral_ge_le_of_lipschitzWith hf ht

end LipschitzWith
