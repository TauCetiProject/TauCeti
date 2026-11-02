/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic
import TauCeti.Analysis.Complex.Euclidean.Matrix
import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Affine images of proper complex Gaussians

A complex affine map `z ↦ L *ᵥ z + c` sends a proper complex Gaussian with mean `m`
and positive semidefinite covariance `C` to the proper complex Gaussian with mean
`L *ᵥ m + c` and covariance `L * C * Lᴴ`. Rectangular maps allow singular images
and coordinate restrictions. Multiplication by a unit complex scalar preserves a
centered proper complex Gaussian law.

The affine identity follows by realification from
`TauCeti.Probability.map_affine_multivariateGaussian`.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A rectangular complex affine image of a proper complex Gaussian is proper complex
Gaussian, with the mean and covariance transformed by the same matrix. -/
@[simp]
theorem map_affine_properComplexGaussianMeasure (m : ι → ℂ) {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (L : Matrix κ ι ℂ) (c : κ → ℂ) :
    (properComplexGaussianMeasure m C).map (fun z ↦ L *ᵥ z + c) =
      properComplexGaussianMeasure (L *ᵥ m + c) (L * C * Lᴴ) := by
  have hcov : L.realify * complexGaussianRealCovariance C * L.realifyᵀ =
      complexGaussianRealCovariance (L * C * Lᴴ) := by
    simp [complexGaussianRealCovariance_def, Matrix.realify_mul,
      Matrix.realify_conjTranspose, Matrix.mul_smul, Matrix.smul_mul]
  have hmap (x : EuclideanSpace ℝ (ι ⊕ ι)) :
      L *ᵥ (complexToRealEuclidean ι).symm x + c =
        (complexToRealEuclidean κ).symm
          (L.realify.toEuclideanLin x + complexToRealEuclidean κ c) := by
    apply (complexToRealEuclidean κ).injective
    simp [complexToRealEuclidean_mulVec]
  rw [properComplexGaussianMeasure_def, properComplexGaussianMeasure_def, map_add,
    complexToRealEuclidean_mulVec, ← hcov,
    ← map_affine_multivariateGaussian _ ((posSemidef_complexGaussianRealCovariance_iff C).2 hC),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact congrArg (fun f ↦ Measure.map f _) (funext hmap)

/-- Restricting or repeating coordinates of a proper complex Gaussian restricts its mean
and covariance along the same map. In particular this gives singleton coordinate marginals. -/
theorem map_comp_properComplexGaussianMeasure (m : ι → ℂ) {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (f : κ → ι) :
    (properComplexGaussianMeasure m C).map (fun z ↦ z ∘ f) =
      properComplexGaussianMeasure (m ∘ f) (C.submatrix f f) := by
  let L : Matrix κ ι ℂ := (1 : Matrix ι ι ℂ).submatrix f id
  have hL (z : ι → ℂ) : L *ᵥ z = z ∘ f := by
    ext k
    simp [L, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hcov : L * C * Lᴴ = C.submatrix f f := by
    ext i j
    simp [L, Matrix.mul_apply, Matrix.one_apply]
  simpa only [hL, hcov, add_zero] using map_affine_properComplexGaussianMeasure m hC L 0

/-- A centered proper complex Gaussian is invariant under multiplication by any unit
complex scalar, including singular and invalid covariance parameters. -/
theorem properComplexGaussianMeasure_centered_rotation (C : Matrix ι ι ℂ)
    {u : ℂ} (hu : ‖u‖ = 1) :
    (properComplexGaussianMeasure 0 C).map (fun z ↦ u • z) =
      properComplexGaussianMeasure 0 C := by
  by_cases hC : C.PosSemidef
  · have hu' : star u * u = 1 := by
      rw [Complex.star_def]
      simpa only [hu, one_pow, Complex.ofReal_one] using Complex.conj_mul' u
    have hcov : (u • (1 : Matrix ι ι ℂ)) * C * (u • (1 : Matrix ι ι ℂ))ᴴ = C := by
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hu', one_smul]
    have h := map_affine_properComplexGaussianMeasure (0 : ι → ℂ) hC
      (u • (1 : Matrix ι ι ℂ)) 0
    rw [hcov] at h
    simpa only [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_zero, add_zero] using h
  · simp [properComplexGaussianMeasure_of_not_posSemidef _ hC,
      Measure.map_dirac' (by fun_prop : Measurable (fun z : ι → ℂ ↦ u • z))]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ}
  {C : Matrix ι ι ℂ}

/-- Complex affine transport for a random vector with a proper complex Gaussian law. -/
theorem HasLaw.affine_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef)
    (L : Matrix κ ι ℂ) (c : κ → ℂ) :
    HasLaw (fun ω ↦ L *ᵥ Z ω + c)
      (properComplexGaussianMeasure (L *ᵥ m + c) (L * C * Lᴴ)) P :=
  (HasLaw.mk (by fun_prop) (map_affine_properComplexGaussianMeasure m hC L c)).comp hZ

/-- Coordinate restrictions of a proper complex Gaussian random vector remain proper
complex Gaussian, with the restricted mean and covariance. -/
theorem HasLaw.comp_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef)
    (f : κ → ι) :
    HasLaw (fun ω ↦ Z ω ∘ f)
      (properComplexGaussianMeasure (m ∘ f) (C.submatrix f f)) P :=
  (HasLaw.mk (Measurable.of_eval (fun k ↦ measurable_pi_apply (f k))).aemeasurable
    (map_comp_properComplexGaussianMeasure m hC f)).comp hZ

end ProbabilityTheory
