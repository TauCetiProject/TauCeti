/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Function
public import TauCeti.Analysis.PDE.PoissonIntegral.HalfSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Boundary values of the Poisson integral at points of continuity

For a bounded measurable `h : ℝ → ℂ` continuous at `x₀`, the Poisson integral
`P[h](z) = ∫ P(z, x) h(x) dx` tends to `h(x₀)` as `z → x₀` through the open upper half-plane,
without any restriction on the approach (`TauCeti.tendsto_upperHalfPlanePoissonIntegralFun`).

This is the two-dimensional case of `TauCeti.tendsto_halfSpacePoissonIntegral`, transported along
the coordinates `Complex.orthonormalBasisOneI`: the upper half-plane Poisson kernel is the
half-space kernel with inward normal `i` (`TauCeti.upperHalfPlanePoissonKernel_def`), and the
bounding line `(ℝ ∙ i)ᗮ` carries Lebesgue measure as the image of `t ↦ t • 1`
(`MeasureTheory.volume_eq_of_finrank_eq_one`). The real form is
`TauCeti.tendsto_integral_upperHalfPlanePoissonKernel_mul`; the complex form applies it to the
real and imaginary parts.

## Main declarations

* `TauCeti.upperHalfPlaneLineCoord`: the real coordinate of the bounding line, which preserves
  Lebesgue measure (`TauCeti.measurePreserving_upperHalfPlaneLineCoord`); integrals over the line
  are integrals over `ℝ` (`TauCeti.integral_upperHalfPlaneLine_eq`).
* `TauCeti.integral_upperHalfPlanePoissonKernel_mul_eq_halfSpacePoissonIntegral`: the Poisson
  integral of the upper half-plane is the two-dimensional half-space Poisson integral.
* `TauCeti.tendsto_integral_upperHalfPlanePoissonKernel_mul`: boundary values of the Poisson
  integral of bounded real data at a point of continuity.
* `TauCeti.tendsto_upperHalfPlanePoissonIntegralFun`: the same for bounded complex data.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology Module

open scoped InnerProductSpace

namespace TauCeti

/-- The point `1` of the real axis, as a unit vector of the bounding line `(ℝ ∙ i)ᗮ`. -/
def upperHalfPlaneLineUnit : (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ :=
  ⟨Complex.orthonormalBasisOneI.repr 1, Submodule.mem_orthogonal_singleton_iff_inner_right.2 <| by
    simp⟩

/-- The defining formula of `TauCeti.upperHalfPlaneLineUnit`. -/
theorem coe_upperHalfPlaneLineUnit :
    (upperHalfPlaneLineUnit : EuclideanSpace ℝ (Fin 2)) = Complex.orthonormalBasisOneI.repr 1 := by
  rw [upperHalfPlaneLineUnit]

/-- The point `t` of the real axis is `t` times the unit vector of the bounding line. -/
theorem coe_smul_upperHalfPlaneLineUnit (t : ℝ) :
    ((t • upperHalfPlaneLineUnit : (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ) :
      EuclideanSpace ℝ (Fin 2)) = Complex.orthonormalBasisOneI.repr t := by
  rw [Submodule.coe_smul, upperHalfPlaneLineUnit, ← map_smul, Complex.real_smul, mul_one]

/-- The unit vector of the bounding line has norm one. -/
@[simp]
theorem norm_upperHalfPlaneLineUnit :
    ‖(upperHalfPlaneLineUnit : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  simp [upperHalfPlaneLineUnit]

/-- Lebesgue measure on the bounding line is the image of Lebesgue measure on `ℝ`. -/
theorem volume_upperHalfPlaneLine :
    (volume : Measure (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ) =
      (volume : Measure ℝ).map (· • upperHalfPlaneLineUnit) := by
  have hv : (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)) ≠ 0 := fun h ↦ by
    simpa [h] using upperHalfPlaneNormal.property
  rw [volume_eq_of_finrank_eq_one (by
      rw [Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one hv,
        finrank_euclideanSpace_fin])
    (v := upperHalfPlaneLineUnit) fun h ↦ by simpa [h] using norm_upperHalfPlaneLineUnit]
  simp [← ofReal_norm]

private theorem isometry_smul_upperHalfPlaneLineUnit :
    Isometry fun t : ℝ ↦ t • upperHalfPlaneLineUnit :=
  AddMonoidHomClass.isometry_of_norm ((LinearMap.lsmul ℝ _).flip upperHalfPlaneLineUnit) fun t ↦ by
    simp [norm_smul]

/-- An integral over the bounding line is the integral over `ℝ` along its unit vector. -/
theorem integral_upperHalfPlaneLine_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ → G) :
    ∫ y, F y = ∫ t : ℝ, F (t • upperHalfPlaneLineUnit) := by
  rw [volume_upperHalfPlaneLine,
    isometry_smul_upperHalfPlaneLineUnit.isClosedEmbedding.measurableEmbedding.integral_map]

/-- The real coordinate on the bounding line `(ℝ ∙ i)ᗮ`. -/
def upperHalfPlaneLineCoord (y : (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ) : ℝ :=
  (Complex.orthonormalBasisOneI.repr.symm (y : EuclideanSpace ℝ (Fin 2))).re

/-- The defining formula of `TauCeti.upperHalfPlaneLineCoord`. -/
theorem upperHalfPlaneLineCoord_apply
    (y : (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ) :
    upperHalfPlaneLineCoord y =
      (Complex.orthonormalBasisOneI.repr.symm (y : EuclideanSpace ℝ (Fin 2))).re := by
  rw [upperHalfPlaneLineCoord]

/-- The real coordinate of `t` times the unit vector of the bounding line is `t`. -/
@[simp]
theorem upperHalfPlaneLineCoord_smul (t : ℝ) :
    upperHalfPlaneLineCoord (t • upperHalfPlaneLineUnit) = t := by
  rw [upperHalfPlaneLineCoord_apply, coe_smul_upperHalfPlaneLineUnit,
    LinearIsometryEquiv.symm_apply_apply, ofReal_re]

/-- A point of the bounding line is its real coordinate times the unit vector of the line. -/
@[simp]
theorem upperHalfPlaneLineCoord_smul_upperHalfPlaneLineUnit
    (y : (ℝ ∙ (upperHalfPlaneNormal : EuclideanSpace ℝ (Fin 2)))ᗮ) :
    upperHalfPlaneLineCoord y • upperHalfPlaneLineUnit = y := by
  have him : (Complex.orthonormalBasisOneI.repr.symm (y : EuclideanSpace ℝ (Fin 2))).im = 0 := by
    rw [← inner_upperHalfPlaneNormal_repr, LinearIsometryEquiv.apply_symm_apply]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 y.property
  ext1
  rw [coe_smul_upperHalfPlaneLineUnit, upperHalfPlaneLineCoord_apply,
    ← LinearIsometryEquiv.eq_symm_apply]
  exact Complex.ext (ofReal_re _) (by rw [ofReal_im, him])

/-- The real coordinate of the bounding line is continuous. -/
@[fun_prop]
theorem continuous_upperHalfPlaneLineCoord : Continuous upperHalfPlaneLineCoord :=
  continuous_re.comp (Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtypeVal)

/-- The real coordinate of the bounding line carries Lebesgue measure on the line to Lebesgue
measure on `ℝ`. -/
theorem measurePreserving_upperHalfPlaneLineCoord :
    MeasurePreserving upperHalfPlaneLineCoord := by
  refine ⟨continuous_upperHalfPlaneLineCoord.measurable, ?_⟩
  rw [volume_upperHalfPlaneLine, Measure.map_map continuous_upperHalfPlaneLineCoord.measurable
    isometry_smul_upperHalfPlaneLineUnit.continuous.measurable]
  simp [Function.comp_def, upperHalfPlaneLineCoord_smul]

/-- **The Poisson integral of the upper half-plane is the half-space Poisson integral** in
dimension two, with inward normal `i`, in the coordinates `Complex.orthonormalBasisOneI`, for
boundary data `f` read on the bounding line through its real coordinate. -/
theorem integral_upperHalfPlanePoissonKernel_mul_eq_halfSpacePoissonIntegral (f : ℝ → ℝ)
    (z : ℂ) :
    ∫ x, upperHalfPlanePoissonKernel z x * f x =
      halfSpacePoissonIntegral upperHalfPlaneNormal (f ∘ upperHalfPlaneLineCoord)
        (Complex.orthonormalBasisOneI.repr z) := by
  rw [halfSpacePoissonIntegral_def, integral_upperHalfPlaneLine_eq]
  simp only [Function.comp_apply, upperHalfPlaneLineCoord_smul, coe_smul_upperHalfPlaneLineUnit,
    upperHalfPlanePoissonKernel_def]

/-- **Boundary values at a point of continuity.** For bounded measurable real data `f`
continuous at `x₀`, the Poisson integral `∫ P(z, x) f(x) dx` tends to `f(x₀)` as `z → x₀` through
the open upper half-plane. -/
theorem tendsto_integral_upperHalfPlanePoissonKernel_mul {f : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f) (hC : ∀ x, |f x| ≤ C) {x₀ : ℝ} (hx₀ : ContinuousAt f x₀) :
    Tendsto (fun z ↦ ∫ x, upperHalfPlanePoissonKernel z x * f x)
      (𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ)) (𝓝 (f x₀)) := by
  have hT := tendsto_halfSpacePoissonIntegral upperHalfPlaneNormal
    (hf.comp_measurePreserving measurePreserving_upperHalfPlaneLineCoord) (fun y ↦ hC _)
    (ξ := x₀ • upperHalfPlaneLineUnit) (hx₀.comp_of_eq
      continuous_upperHalfPlaneLineCoord.continuousAt (upperHalfPlaneLineCoord_smul x₀))
  simp only [Function.comp_apply, upperHalfPlaneLineCoord_smul,
    coe_smul_upperHalfPlaneLineUnit] at hT
  simp_rw [integral_upperHalfPlanePoissonKernel_mul_eq_halfSpacePoissonIntegral]
  refine hT.comp (tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz ↦ ?_⟩)
  · exact (Complex.orthonormalBasisOneI.repr.continuous.tendsto (x₀ : ℂ)).mono_left
      nhdsWithin_le_nhds
  · simpa using hz

/-- **Boundary values at a point of continuity.** For bounded measurable `h : ℝ → ℂ` continuous
at `x₀`, `P[h](z) → h(x₀)` as `z → x₀` through the open upper half-plane, with no restriction on
the approach. -/
theorem tendsto_upperHalfPlanePoissonIntegralFun {h : ℝ → ℂ} {C : ℝ}
    (hh : AEStronglyMeasurable h) (hC : ∀ x, ‖h x‖ ≤ C) {x₀ : ℝ} (hx₀ : ContinuousAt h x₀) :
    Tendsto (upperHalfPlanePoissonIntegralFun h) (𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ))
      (𝓝 (h x₀)) := by
  have hint : Integrable h upperHalfPlanePoissonMeasure :=
    .of_bound (hh.mono_ac upperHalfPlanePoissonMeasure_absolutelyContinuous) C (.of_forall hC)
  have hre := tendsto_integral_upperHalfPlanePoissonKernel_mul
    (continuous_re.comp_aestronglyMeasurable hh)
    (fun x ↦ (abs_re_le_norm _).trans (hC x)) (continuous_re.continuousAt.comp hx₀)
  have him := tendsto_integral_upperHalfPlanePoissonKernel_mul
    (continuous_im.comp_aestronglyMeasurable hh)
    (fun x ↦ (abs_im_le_norm _).trans (hC x)) (continuous_im.continuousAt.comp hx₀)
  simp only [← re_upperHalfPlanePoissonIntegralFun hint] at hre
  simp only [← im_upperHalfPlanePoissonIntegralFun hint] at him
  have := (Complex.equivRealProdCLM.symm.continuous.tendsto _).comp (hre.prodMk_nhds him)
  simpa [Function.comp_def, Complex.equivRealProdCLM_symm_apply, re_add_im] using this

end TauCeti
