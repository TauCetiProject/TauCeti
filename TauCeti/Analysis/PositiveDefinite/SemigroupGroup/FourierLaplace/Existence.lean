/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Kernel
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Kernel
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.PositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Uniqueness
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Density

/-!
# The Berg--Christensen--Ressel representation theorem

A bounded continuous positive-definite function on the involutive semigroup `ℝ≥0 × V`, with `V` a
finite-dimensional real inner-product space, is the Laplace--Fourier transform of a unique finite
measure on `ℝ≥0 × V`. This file proves the existence half and packages it with the uniqueness half
of `TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Uniqueness` into the
equivalence `TauCeti.bcr_semigroup_bochner`.

Every ingredient is already in place, and the proof here is the assembly.

* Freezing the time variable and applying Bochner's theorem on `V` turns `F` into a family of
  finite spatial measures, and the representation holds exactly when that family is the family of
  Laplace-weighted spatial slices of a single measure
  (`TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`). Disintegrating over the spatial
  marginal reduces this to producing a *kernel* from `V` to `ℝ≥0` whose fibrewise Laplace
  transforms are the densities of the spatial measures against the one at time `0`
  (`TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel`).
* Almost every fibre of `TauCeti.timeSliceDensity`, the right-continuous version of that family of
  densities, is a completely monotone function of time
  (`TauCeti.ae_isContinuousCompletelyMonotoneOnIoi_timeSliceDensity`), normalized at time `0`.
* The Hausdorff--Bernstein--Widder theorem therefore represents each such fibre by a finite measure
  on `ℝ≥0`, and those measures depend measurably on the fibre, so they assemble into
  `TauCeti.bernsteinMeasureKernel`.

The only step needing care is that "almost every fibre" is not "every fibre", while a kernel must
be defined at every point: the density is corrected to `0` on a measurable null set containing the
exceptional fibres (`TauCeti.exists_isContinuousCompletelyMonotoneOnIoi_ae_eq`), which changes
neither the Bernstein measures elsewhere nor the resulting representation.

## Main declarations

* `TauCeti.exists_representsLaplaceFourier`: **the existence half** of the
  Berg--Christensen--Ressel representation.
* `TauCeti.bcr_semigroup_bochner`: the representation theorem as an equivalence, with uniqueness.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {F : ℝ≥0 × V → ℂ}

/-- **The existence half of the Berg--Christensen--Ressel representation theorem.** A bounded
continuous positive-definite function on the involutive semigroup `ℝ≥0 × V` is the Laplace--Fourier
transform of a finite measure on `ℝ≥0 × V`.

The representing measure is assembled from the spatial Bochner measure at time `0` and the
Bernstein measures of the fibres of `TauCeti.timeSliceDensity`. -/
theorem exists_representsLaplaceFourier (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) :
    ∃ μ : Measure (ℝ≥0 × V), RepresentsLaplaceFourier μ F := by
  have h0 := ae_timeSliceDensity_zero_eq_one hFpd hFcont hFbdd
  -- The time profiles are completely monotone and normalized for almost every frequency; correct
  -- them on a null set.
  obtain ⟨g, hcm, hmeas, hmass, hg⟩ := exists_isContinuousCompletelyMonotoneOnIoi_ae_eq
    (fun q s => (timeSliceDensity F s.toNNReal q).toReal)
    (((ae_isContinuousCompletelyMonotoneOnIoi_timeSliceDensity hFpd hFcont hFbdd).and h0).mono
      fun q h => ⟨h.1, by simp [h.2]⟩) fun n => by fun_prop
  have _ : IsFiniteKernel (bernsteinMeasureKernel g hcm hmeas) :=
    isFiniteKernel_bernsteinMeasureKernel hcm hmeas hmass
  refine ⟨_, representsLaplaceFourier_swapCompProd_of_ae_rnDeriv hFpd hFcont hFbdd
    (bernsteinMeasureKernel g hcm hmeas) fun t => ?_⟩
  filter_upwards [timeSliceDensity_ae_eq_rnDeriv hFpd hFcont hFbdd t, hg, h0] with q hq hgq hq0
  have hle : timeSliceDensity F t q ≤ 1 :=
    hq0 ▸ timeSliceDensity_antitone F q (zero_le : (0 : ℝ≥0) ≤ t)
  rw [← hq, Kernel.laplaceTransform_apply,
    (representsLaplace_bernsteinMeasureKernel hcm hmeas q).laplaceTransformENN_eq t, congrFun hgq,
    Real.toNNReal_coe, ENNReal.ofReal_toReal (hle.trans_lt ENNReal.one_lt_top).ne]

/-- **The Berg--Christensen--Ressel representation theorem** (Berg--Christensen--Ressel 4.1.13).
A function on the involutive semigroup `ℝ≥0 × V`, for `V` a finite-dimensional real inner-product
space, is positive definite, continuous and bounded **if and only if** it is the Laplace--Fourier
transform of a unique finite measure on `ℝ≥0 × V`:

`F (t, a) = ∫ (p, q), exp (-t p) * exp (-2πi⟪a, q⟫) dμ (p, q)`.

The forward direction is `TauCeti.exists_representsLaplaceFourier` together with the transform
injectivity of `TauCeti.RepresentsLaplaceFourier.unique`; the converse direction is the elementary
fact that such a transform is positive definite, continuous, and bounded by the total mass. -/
theorem bcr_semigroup_bochner (F : ℝ≥0 × V → ℂ) :
    (IsSemigroupGroupPD F ∧ Continuous F ∧ Bornology.IsBounded (range F))
      ↔ ∃! μ : Measure (ℝ≥0 × V), RepresentsLaplaceFourier μ F := by
  constructor
  · rintro ⟨hFpd, hFcont, hFbdd⟩
    obtain ⟨μ, hμ⟩ := exists_representsLaplaceFourier hFpd hFcont hFbdd
    exact ⟨μ, hμ, fun ν hν => hν.unique hμ⟩
  · rintro ⟨μ, hμ, -⟩
    have := hμ.isFiniteMeasure
    exact ⟨hμ.isSemigroupGroupPD, hμ.continuous, isBounded_iff_forall_norm_le.2
      ⟨μ.real univ, by rintro _ ⟨x, rfl⟩; exact hμ.norm_le_mass x⟩⟩

end TauCeti

end

end
