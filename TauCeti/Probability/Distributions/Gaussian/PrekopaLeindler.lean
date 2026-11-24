/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.MeasureTheory.Integral.PrekopaLeindler.Basic
import TauCeti.Probability.Distributions.Gaussian.Density
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Gaussian measures have the Prékopa–Leindler property

The standard Gaussian measure on a finite-dimensional real inner product space has a log-concave
density with respect to volume, so it inherits the Prékopa–Leindler property of volume at every
weight `0 ≤ θ ≤ 1`. A multivariate Gaussian measure is the image of a standard Gaussian under an
affine map, so it has the property as well; degenerate covariance matrices are allowed.

For a centered multivariate Gaussian measure, which is negation-invariant, this gives
**Anderson's inequality**: a measurable, convex set that is symmetric about the origin has at
least the Gaussian mass of each of its translates.

## Main results

* `TauCeti.Probability.hasPrekopaLeindler_stdGaussian`: the standard Gaussian measure has the
  Prékopa–Leindler property.
* `TauCeti.Probability.hasPrekopaLeindler_multivariateGaussian`: every multivariate Gaussian
  measure has the Prékopa–Leindler property.
* `TauCeti.Probability.multivariateGaussian_preimage_add_le`: Anderson's inequality for a
  centered multivariate Gaussian measure.

## References

* T. W. Anderson, *The integral of a symmetric unimodal function over a symmetric convex set and
  some probability inequalities*, Proc. Amer. Math. Soc. **6** (1955), 170–176.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemma 8.5.

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Asymptotics/LAN/GaussianAnderson.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TauCeti.Probability

/-- The standard Gaussian measure on a finite-dimensional real inner product space has the
Prékopa–Leindler property at every weight `0 ≤ θ ≤ 1`, including in dimension zero. -/
theorem hasPrekopaLeindler_stdGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : (stdGaussian E).HasPrekopaLeindler θ := by
  rw [stdGaussian_eq_withDensity_norm]
  refine (hasPrekopaLeindler_volume E hθ₀ hθ₁).withDensity hθ₀ hθ₁ (by fun_prop) ?_
  convert (logConcave_const (E := E)
    (ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)))).mul
    (logConcave_ofReal_exp_neg_mul_sq_norm (G := E) (c := 1 / 2) (by norm_num)) using 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 3
  ring

/-- A multivariate Gaussian measure has the Prékopa–Leindler property at every weight
`0 ≤ θ ≤ 1`. The covariance matrix may be degenerate. -/
theorem hasPrekopaLeindler_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (multivariateGaussian μ S).HasPrekopaLeindler θ := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hA : MeasurePreserving (fun x ↦ μ + A x) (stdGaussian (EuclideanSpace ℝ ι))
      (multivariateGaussian μ S) :=
    ⟨by fun_prop, by simp only [multivariateGaussian, A]⟩
  refine (hasPrekopaLeindler_stdGaussian _ hθ₀ hθ₁).map (fun x ↦ μ + A x) hA fun x y ↦ ?_
  simp only [map_add, map_smul, smul_add]
  module

/-- **Anderson's inequality** for a centered multivariate Gaussian measure: translating a
measurable, convex set that is symmetric about the origin cannot increase its mass. The
covariance matrix may be degenerate. -/
theorem multivariateGaussian_preimage_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) {C : Set (EuclideanSpace ℝ ι)} (hC : MeasurableSet C)
    (hCc : Convex ℝ C) (hneg : ∀ x ∈ C, -x ∈ C) (a : EuclideanSpace ℝ ι) :
    multivariateGaussian 0 S ((a + ·) ⁻¹' C) ≤ multivariateGaussian 0 S C := by
  have : (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).IsNegInvariant :=
    ⟨IsGaussian.map_neg_eq_self _ (by rw [integral_id_multivariateGaussian])⟩
  exact hCc.measure_preimage_add_le
    (fun _ hθ₀ hθ₁ ↦ hasPrekopaLeindler_multivariateGaussian 0 S hθ₀ hθ₁) hC hneg a

end TauCeti.Probability
