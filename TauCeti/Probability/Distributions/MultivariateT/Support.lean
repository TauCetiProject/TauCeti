/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateT.Basic
import TauCeti.Probability.Distributions.ChiSquared.Support

/-!
# Support and singularity of multivariate t laws

For positive degrees of freedom and positive semidefinite scale, the topological support of a
multivariate t law is the affine range of its scale matrix. Thus singular scales give laws
singular with respect to ambient Euclidean volume. In positive dimension this includes the
point mass at zero scale; the support formula also applies to empty coordinate types.

The affine carrier is `m + range S`. For a positive semidefinite scale that is not positive
definite, this is a proper affine subspace of zero ambient volume. The ambient Radon--Nikodym
derivative therefore vanishes almost everywhere, even when the law has total mass one.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

/- The support calculation uses `support_multivariateGaussian` and `support_chiSquaredMeasure`:
the Gaussian--chi-squared mixture reaches every point of the affine range at a positive mixing
value, where its defining map is continuous. Singularity uses the existing almost-sure
concentration theorem and Mathlib's `Measure.addHaar_affineSubspace`. -/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The topological support of a multivariate t law with valid parameters is the affine range
of its scale matrix, including singular and zero scales. -/
@[simp]
theorem support_multivariateTMeasure (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} {ν : ℝ}
    (hν : 0 < ν) (hS : S.PosSemidef) :
    (multivariateTMeasure m S ν).support =
      (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
        Set (EuclideanSpace ℝ ι)) := by
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed (AffineSubspace.closed_of_finiteDimensional _)
      (ae_mem_affineRange_multivariateTMeasure m S ν)
  · intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro U hxU hU
    have hxG : x - m ∈ (multivariateGaussian 0 S).support := by
      rw [support_multivariateGaussian hS]
      simpa only [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, sub_zero] using hx
    have hνC : ν ∈ (chiSquaredMeasure ν).support := by
      simp [support_chiSquaredMeasure, hν.ne', hν, hν.le]
    -- At mixing value `ν`, the scale factor is one and the mixture attains `x`.
    have hcont : ContinuousAt
        (fun z : EuclideanSpace ℝ ι × ℝ => m + √(ν / z.2) • z.1) (x - m, ν) := by
      fun_prop (disch := exact hν.ne')
    have hpre : (fun z : EuclideanSpace ℝ ι × ℝ => m + √(ν / z.2) • z.1) ⁻¹' U ∈
        𝓝 (x - m, ν) := hcont.preimage_mem_nhds (by
      simpa [div_self hν.ne'] using hU.mem_nhds hxU)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hpre
    rw [multivariateTMeasure_of_posSemidef m hν hS,
      Measure.map_apply (by fun_prop) hU.measurableSet]
    apply lt_of_lt_of_le _ (measure_mono hVW)
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos ((Measure.mem_support_iff_forall _).mp hxG V hV).ne'
      ((Measure.mem_support_iff_forall _).mp hνC W hW).ne'

/-- A multivariate t law with scale that is not positive definite is singular with respect to
ambient Euclidean volume. Invalid parameters give the zero measure, which is also singular. -/
theorem mutuallySingular_multivariateTMeasure_volume (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (ν : ℝ) (hS : ¬ S.PosDef) :
    multivariateTMeasure m S ν ⟂ₘ (volume : Measure (EuclideanSpace ℝ ι)) := by
  by_cases hν : 0 < ν
  swap
  · simp [multivariateTMeasure_of_nonpos m S (le_of_not_gt hν)]
  by_cases hSS : S.PosSemidef
  swap
  · simp [multivariateTMeasure_of_not_posSemidef m ν hSS]
  have hdet : S.det = 0 := by
    by_contra hdet
    exact hS (hSS.posDef_iff_det_ne_zero.mpr hdet)
  have hrange : LinearMap.range S.toEuclideanLin ≠ ⊤ :=
    (LinearMap.range_lt_top_of_det_eq_zero (by
      rwa [LinearMap.det_toLpLin])).ne
  let A : AffineSubspace ℝ (EuclideanSpace ℝ ι) :=
    AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin)
  have hA : A ≠ ⊤ := by
    intro h
    apply hrange
    rw [← AffineSubspace.direction_mk' m (LinearMap.range S.toEuclideanLin)]
    simpa only [AffineSubspace.direction_top] using congrArg AffineSubspace.direction h
  refine ⟨(A : Set (EuclideanSpace ℝ ι))ᶜ,
    A.closed_of_finiteDimensional.measurableSet.compl, ?_, ?_⟩
  · exact mem_ae_iff.mp
      (Filter.eventually_mem_set.mp (ae_mem_affineRange_multivariateTMeasure m S ν))
  · rw [compl_compl]
    exact Measure.addHaar_affineSubspace volume A hA

/-- The ambient Radon--Nikodym derivative of a multivariate t law with scale that is not
positive definite vanishes almost everywhere. -/
theorem rnDeriv_multivariateTMeasure_of_not_posDef (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (ν : ℝ) (hS : ¬ S.PosDef) :
    (multivariateTMeasure m S ν).rnDeriv volume =ᵐ[volume] 0 :=
  (mutuallySingular_multivariateTMeasure_volume m ν hS).rnDeriv_ae_eq_zero

end TauCeti.Probability
