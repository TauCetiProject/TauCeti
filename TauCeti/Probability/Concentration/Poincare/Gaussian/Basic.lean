/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.Linear
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Concentration.Poincare.CompactSupport
import TauCeti.Probability.Concentration.Poincare.Tensorization
import TauCeti.Probability.Concentration.Poincare.Transport
import TauCeti.Probability.Distributions.Gaussian.Poincare

/-!
# The canonical Gaussian Poincaré inequality

The standard Gaussian satisfies `MeasureTheory.Measure.PoincareInequality` with constant `1`.
This uses the full smooth, square-integrable, finite-energy test class; the function and its
derivative need not be bounded. On a nontrivial finite-dimensional real inner product space,
the admissible constants are exactly those at least `1`.

The scalar bounded-test inequality is proved in
`TauCeti.Probability.Distributions.Gaussian.Poincare`. The compact-test criterion extends it to
the canonical predicate. Tensorization and isometric transport give `stdGaussian` on any
finite-dimensional real inner product space, including dimension zero.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, §2.3.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace TauCeti.Probability

/-- The standard Gaussian on `ℝ` satisfies the full smooth-test Poincaré inequality with
constant `1`. -/
theorem poincareInequality_gaussianReal_zero_one :
    (gaussianReal 0 1).PoincareInequality 1 := by
  apply Measure.poincareInequality_iff_forall_hasCompactSupport.mpr
  intro f hf hc
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨B, hB⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by simp))
  have hfb : ∃ A, ∀ x, |f x| ≤ A := ⟨A, by simpa only [Real.norm_eq_abs] using hA⟩
  have hdb : ∃ B, ∀ x, |deriv f x| ≤ B := ⟨B, by
    simpa only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] using hB⟩
  simpa only [one_mul, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, sq_abs] using
    variance_le_integral_deriv_sq_gaussianReal (hf.of_le (by simp)) hfb hdb

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian on a finite-dimensional real inner product space satisfies the
full smooth-test Poincaré inequality with constant `1`. This includes dimension zero. -/
theorem poincareInequality_stdGaussian : (stdGaussian E).PoincareInequality 1 := by
  have hpi : (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).PoincareInequality 1 := by
    rw [← map_pi_eq_stdGaussian]
    exact Measure.PoincareInequality.piLp (fun _ ↦ gaussianReal 0 1) 1
      (fun _ ↦ poincareInequality_gaussianReal_zero_one)
  simpa only [stdGaussian_map] using
    hpi.map_linearIsometryEquiv (stdOrthonormalBasis ℝ E).repr.symm

/-- On a nontrivial finite-dimensional real inner product space, the standard Gaussian has
Poincaré constant `C` exactly when `1 ≤ C`. -/
theorem poincareInequality_stdGaussian_iff [Nontrivial E] {C : ℝ} :
    (stdGaussian E).PoincareInequality C ↔ 1 ≤ C := by
  refine ⟨fun h ↦ h.one_le_of_covarianceBilin_self_eq IsGaussian.memLp_two_id ?_,
    fun h ↦ (poincareInequality_stdGaussian E).mono h⟩
  intro v
  rw [covarianceBilin_stdGaussian, innerSL_apply_apply]
  exact real_inner_self_eq_norm_sq v

end TauCeti.Probability
