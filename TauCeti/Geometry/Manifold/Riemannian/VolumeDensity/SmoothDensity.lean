/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Measure.SmoothDensity

/-!
# The Riemannian volume has a smooth positive density

Let `M` be a boundaryless manifold modelled on a finite-dimensional real normed space `E`, with a
smooth Riemannian metric. In a chart `e` of the maximal smooth atlas of `M`, not only in a
preferred chart, the Riemannian volume reads as `ρ(y) dy` with

`ρ(y) = c · √(det ⟪∂ᵢ, ∂ⱼ⟫_{e⁻¹ y})`,

the square root of the Gram determinant of the coordinate vectors `d(e⁻¹)_y (bᵢ)` of a basis `b`
of `E` (the Riemannian Jacobian `TauCeti.riemannianJacobian b e.symm`), times the constant `c`
comparing the Haar measure of `b` with the measure `volume` on `E`. This density is smooth and
positive on the chart target, since `e⁻¹` is a diffeomorphism there. So the Riemannian volume has
a smooth positive density (`TauCeti.hasSmoothPositiveDensity_riemannianVolume`), and the results
on manifolds that are stated for such a measure, such as formal adjoints of pseudodifferential
operators and their realizations in `L²`, apply to the Riemannian volume.

## Main results

* `TauCeti.hasSmoothPositiveDensity_riemannianVolume`: the Riemannian volume of a smooth metric
  has a smooth positive density.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 (the Riemannian density in coordinates).
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- **The Riemannian volume has a smooth positive density.** For a smooth Riemannian metric on a
boundaryless manifold modelled on a finite-dimensional real normed space `E`, in every chart `e`
of the maximal atlas the Riemannian volume is `ρ(y) dy` for a smooth positive function `ρ` on the
chart target, where `dy` is any additive Haar measure `volume` on `E`: `ρ` is a constant multiple
of the Riemannian Jacobian of `e⁻¹`. -/
theorem hasSmoothPositiveDensity_riemannianVolume [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] :
    HasSmoothPositiveDensity E (riemannianVolume 𝓘(ℝ, E) M) := by
  refine hasSmoothPositiveDensity_iff.2 fun e he ↦ ?_
  -- On the chart target, `e⁻¹` is differentiable with invertible differentials.
  have hd (y : E) (hy : y ∈ e.target) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp)
  have hinj (y : E) (hy : y ∈ e.target) :
      Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y) := by
    obtain ⟨L, hL⟩ :=
      (e.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas he hy).isInvertible_mfderiv (by simp)
    rw [← hL]
    exact L.injective
  let b := Module.finBasis ℝ E
  -- The Haar measure of `b` is `c • volume`.
  let c := b.addHaar.addHaarScalarFactor volume
  refine ⟨fun y ↦ c * riemannianJacobian (I := 𝓘(ℝ, E)) b e.symm y,
    contDiffOn_const.mul (contDiffOn_riemannianJacobian b
      (contMDiffOn_symm_of_mem_maximalAtlas he) le_rfl e.open_target hinj),
    fun y hy ↦ mul_pos (NNReal.coe_pos.2
      (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _))
      (riemannianJacobian_pos b (hinj y hy)),
    fun f _ _ hfs ↦ ?_⟩
  -- Change variables along `e⁻¹ : e.target → e.source`, whose Jacobian density is that of `b`.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfs h),
    ← e.symm_image_target_eq_source,
    b.setIntegral_riemannianVolume_image_of_injOn rfl e.open_target.measurableSet e.symm.injOn hd,
    Measure.isAddLeftInvariant_eq_smul b.addHaar volume, Measure.restrict_smul,
    integral_smul_nnreal_measure, NNReal.smul_def, ← integral_smul]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y _ ↦ ?_
  simp only [Complex.real_smul, Complex.ofReal_mul]
  exact (mul_assoc _ _ _).symm

end TauCeti
