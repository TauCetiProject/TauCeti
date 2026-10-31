/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic

import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Support of proper complex Gaussian laws

A proper complex Gaussian is supported on the inverse image, under real-imaginary coordinate
splitting, of the affine range of its real covariance. Consequently, a covariance that is not
positive definite gives a law singular with respect to real Lebesgue volume on the complex
coordinate space. The Radon–Nikodym derivative then vanishes almost everywhere.

This is the singular half of the density dichotomy for proper complex Gaussian laws. It includes
positive-semidefinite singular covariances, invalid covariance parameters, and empty coordinate
types.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder

namespace TauCeti.Probability

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- The support of a proper complex Gaussian with positive-semidefinite covariance, expressed in
the real coordinates used to define the law. -/
@[simp]
theorem support_properComplexGaussianMeasure {C : Matrix iota iota ℂ} (hC : C.PosSemidef)
    (m : iota → ℂ) :
    (properComplexGaussianMeasure m C).support =
      complexToRealEuclidean iota ⁻¹'
        (AffineSubspace.mk' (complexToRealEuclidean iota m)
          (LinearMap.range (Matrix.toEuclideanLin (complexGaussianRealCovariance C))) :
            Set (EuclideanSpace ℝ (iota ⊕ iota))) := by
  rw [properComplexGaussianMeasure_def, ← (complexToRealEuclidean iota).symm.coe_toHomeomorph,
    Measure.support_map_homeomorph,
    support_multivariateGaussian ((posSemidef_complexGaussianRealCovariance_iff C).mpr hC)]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    exact ⟨complexToRealEuclidean iota z, hz,
      (complexToRealEuclidean iota).symm_apply_apply z⟩

/-- A proper complex Gaussian with positive-semidefinite covariance lies almost surely in its
realified affine range. -/
theorem ae_mem_affineRange_properComplexGaussianMeasure {C : Matrix iota iota ℂ}
    (hC : C.PosSemidef) (m : iota → ℂ) :
    ∀ᵐ z ∂properComplexGaussianMeasure m C,
      complexToRealEuclidean iota z ∈
        AffineSubspace.mk' (complexToRealEuclidean iota m)
          (LinearMap.range (Matrix.toEuclideanLin (complexGaussianRealCovariance C))) := by
  filter_upwards [(properComplexGaussianMeasure m C).support_mem_ae] with z hz
  rw [support_properComplexGaussianMeasure hC m] at hz
  exact hz

/-- An invalid covariance parameter gives singleton support at the mean. -/
@[simp]
theorem support_properComplexGaussianMeasure_of_not_posSemidef (m : iota → ℂ)
    {C : Matrix iota iota ℂ} (hC : ¬ C.PosSemidef) :
    (properComplexGaussianMeasure m C).support = {m} := by
  rw [properComplexGaussianMeasure_of_not_posSemidef m hC, Measure.support_dirac,
    closure_singleton]

/-- Every proper complex Gaussian whose covariance is not positive definite is singular with
respect to real Lebesgue volume on the complex coordinate space. -/
theorem mutuallySingular_properComplexGaussianMeasure_volume {C : Matrix iota iota ℂ}
    (hC : ¬ C.PosDef) (m : iota → ℂ) :
    properComplexGaussianMeasure m C ⟂ₘ (volume : Measure (iota → ℂ)) := by
  have hR : ¬ (complexGaussianRealCovariance C).PosDef := by
    simpa using hC
  have hsing :=
    (complexToRealEuclidean iota).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      |>.mutuallySingular_map
        (mutuallySingular_multivariateGaussian_volume hR (complexToRealEuclidean iota m))
  obtain ⟨c, hc, hmap⟩ :=
    (complexToRealEuclidean iota).symm.toLinearMap.exists_map_addHaar_eq_smul_addHaar
      (volume : Measure (EuclideanSpace ℝ (iota ⊕ iota))) (volume : Measure (iota → ℂ))
      (complexToRealEuclidean iota).symm.surjective
  have hmap' :
      Measure.map
          (complexToRealEuclidean iota).symm.toHomeomorph.toMeasurableEquiv
          (volume : Measure (EuclideanSpace ℝ (iota ⊕ iota))) =
        c • (volume : Measure (iota → ℂ)) := by
    simpa using hmap
  rw [properComplexGaussianMeasure_def]
  rcases hsing with ⟨s, hs, hμs, hνs⟩
  refine ⟨s, hs, hμs, ?_⟩
  rw [hmap'] at hνs
  simp only [Measure.smul_apply, smul_eq_mul] at hνs
  exact (mul_eq_zero.mp hνs).resolve_left hc.ne'

/-- The Radon–Nikodym derivative of a degenerate proper complex Gaussian with respect to volume
vanishes almost everywhere. -/
theorem rnDeriv_properComplexGaussianMeasure_of_not_posDef {C : Matrix iota iota ℂ}
    (hC : ¬ C.PosDef) (m : iota → ℂ) :
    (properComplexGaussianMeasure m C).rnDeriv volume =ᵐ[volume] 0 :=
  Measure.MutuallySingular.rnDeriv_ae_eq_zero
    (mutuallySingular_properComplexGaussianMeasure_volume hC m)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {iota Ω : Type*} [Fintype iota] [DecidableEq iota] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → iota → ℂ} {m : iota → ℂ} {C : Matrix iota iota ℂ}

/-- A random vector with a proper complex Gaussian law and positive-semidefinite covariance lies
almost surely in the realified affine range of that covariance. -/
theorem HasLaw.ae_mem_affineRange_properComplexGaussianMeasure
    (hX : HasLaw X (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef) :
    ∀ᵐ ω ∂P, complexToRealEuclidean iota (X ω) ∈
      AffineSubspace.mk' (complexToRealEuclidean iota m)
        (LinearMap.range (Matrix.toEuclideanLin (complexGaussianRealCovariance C))) := by
  exact (hX.ae_iff (measurableSet_setOfPred.mp
    ((AffineSubspace.closed_of_finiteDimensional _).measurableSet.preimage (by fun_prop)))).2
      (TauCeti.Probability.ae_mem_affineRange_properComplexGaussianMeasure hC m)

end ProbabilityTheory
