/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.FirstVariation.Measure
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.MeasureTheory.Function.AreaFormula.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The first variation of the unit circle

The unit circle `C ⊆ ℂ = ℝ²`, with its tangent line at each point, is a `1`-varifold `[C]` on the
plane: the image of Lebesgue measure on `[0, 2π]` under `θ ↦ (e^{iθ}, span {i e^{iθ}})`
(`TauCeti.Examples.CircleVarifold.circleVarifold`), whose weight is `‖[C]‖ = H¹⌞C`
(`weight_circleVarifold`). Its first variation is
`δ[C](X) = ∫_0^{2π} ⟪γ(θ), X(γ(θ))⟫ dθ` for `γ(θ) = e^{iθ}` (`firstVariation_circleVarifold_apply`):
along the circle the tangential divergence is `⟪τ, DX τ⟫ = g' + ⟪X(γ), γ⟫` for
`g(θ) = ⟪X(γ(θ)), τ(θ)⟫`, and `g'` integrates to `0` over a period. Against the weight this reads
`δ[C](X) = ∫_C ⟪x, X(x)⟫ dH¹(x)` (`firstVariation_circleVarifold_eq_integral`). The field
`x ↦ x` has norm one on `C`, so `[C]` has locally bounded first variation
(`hasLocallyBoundedFirstVariation_circleVarifold`), and its total variation measure, read in the
plane, is the length measure of the circle: `‖δ[C]‖ = H¹⌞C`
(`map_firstVariationMeasure_circleVarifold`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §39.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Complex Real Euclidean Metric
open scoped Distributions RealInnerProductSpace

namespace TauCeti.Examples.CircleVarifold

/-- The unit tangent `i e^{iθ}` of the unit circle at `e^{iθ}`. -/
private def circleTangent (θ : ℝ) : ℂ := circleMap 0 1 θ * I

/-- The unit tangent has norm one. -/
private theorem norm_circleTangent (θ : ℝ) : ‖circleTangent θ‖ = 1 := by
  simp [circleTangent]

/-- The unit tangent is nonzero. -/
private theorem circleTangent_ne_zero (θ : ℝ) : circleTangent θ ≠ 0 :=
  norm_ne_zero_iff.1 (by simp [norm_circleTangent])

/-- The tangent line `span {i e^{iθ}}` of the unit circle at `e^{iθ}`. -/
private def circleTangentLine (θ : ℝ) : grassmannian ℝ ℂ 1 :=
  grassmannian.spanLine ℝ (circleTangent θ) (circleTangent_ne_zero θ)

/-- The unit tangent depends continuously on the angle. -/
private theorem continuous_circleTangent : Continuous circleTangent :=
  (continuous_circleMap 0 1).mul continuous_const

/-- The tangent line depends continuously on the angle. -/
private theorem continuous_circleTangentLine : Continuous circleTangentLine :=
  grassmannian.continuous_spanLine continuous_circleTangent circleTangent_ne_zero

/-- The point `e^{iθ}` of the circle, in the plane `(⊤ : Opens ℂ)`. -/
private def circlePoint (θ : ℝ) : (⊤ : Opens ℂ) := ⟨circleMap 0 1 θ, by simp⟩

/-- The point `circlePoint θ` is `e^{iθ}`. -/
@[simp]
private theorem coe_circlePoint (θ : ℝ) : (circlePoint θ : ℂ) = circleMap 0 1 θ := (rfl)

/-- The point `e^{iθ}` depends continuously on the angle. -/
private theorem continuous_circlePoint : Continuous circlePoint :=
  (continuous_circleMap 0 1).subtype_mk _

/-- The parametrization `θ ↦ (e^{iθ}, span {i e^{iθ}})` of the circle varifold. -/
private def circleVarifoldParam (θ : ℝ) : (⊤ : Opens ℂ) × grassmannian ℝ ℂ 1 :=
  (circlePoint θ, circleTangentLine θ)

/-- The parametrization of the circle varifold is continuous. -/
private theorem continuous_circleVarifoldParam : Continuous circleVarifoldParam :=
  continuous_circlePoint.prodMk continuous_circleTangentLine

/-- The **varifold `[C]` of the unit circle**: the image of Lebesgue measure on `[0, 2π]` under
`θ ↦ (e^{iθ}, span {i e^{iθ}})`. -/
def circleVarifold : Measure ((⊤ : Opens ℂ) × grassmannian ℝ ℂ 1) :=
  (volume.restrict (Icc 0 (2 * π))).map circleVarifoldParam

/-- The circle varifold has finite mass. -/
instance isFiniteMeasure_circleVarifold : IsFiniteMeasure circleVarifold := by
  rw [circleVarifold]
  infer_instance

/-- The image of Lebesgue measure on `[0, 2π]` under `θ ↦ e^{iθ}`, a measure on the plane
`(⊤ : Opens ℂ)`. -/
private def circleMeasure : Measure (⊤ : Opens ℂ) :=
  (volume.restrict (Icc 0 (2 * π))).map circlePoint

/-- The image of Lebesgue measure on `[0, 2π]` under `θ ↦ e^{iθ}` is finite. -/
private instance isFiniteMeasure_circleMeasure : IsFiniteMeasure circleMeasure := by
  rw [circleMeasure]
  infer_instance

/-- The weight of the circle varifold is the image of Lebesgue measure on `[0, 2π]` under
`θ ↦ e^{iθ}`. -/
private theorem weight_circleVarifold_eq_map :
    weight circleVarifold = (volume.restrict (Icc 0 (2 * π))).map (circleMap 0 1) := by
  have hγ : (fun p : (⊤ : Opens ℂ) × grassmannian ℝ ℂ 1 ↦ (p.1 : ℂ)) ∘ circleVarifoldParam =
      circleMap 0 1 := funext coe_circlePoint
  rw [weight_def, circleVarifold, Measure.map_map (by fun_prop)
    continuous_circleVarifoldParam.measurable, hγ]

/-- **`‖[C]‖ = H¹⌞C`**: the weight of the circle varifold is the one-dimensional Hausdorff measure
on the unit circle. -/
theorem weight_circleVarifold : weight circleVarifold = μHE[1].restrict (sphere (0 : ℂ) 1) := by
  rw [weight_circleVarifold_eq_map]
  simpa using TauCeti.smul_map_volume_restrict_circleMap 0 1

/-- The derivative of `g(θ) = ⟪X(γ(θ)), τ(θ)⟫`. -/
private theorem hasDerivAt_inner_circleTangent {X : ℂ → ℂ} (hX : Differentiable ℝ X) (θ : ℝ) :
    HasDerivAt (fun t => ⟪X (circleMap 0 1 t), circleTangent t⟫)
      (⟪circleTangent θ, fderiv ℝ X (circleMap 0 1 θ) (circleTangent θ)⟫ -
        ⟪circleMap 0 1 θ, X (circleMap 0 1 θ)⟫) θ := by
  have hγ : HasDerivAt (circleMap 0 1) (circleTangent θ) θ := by
    simpa [circleTangent] using hasDerivAt_circleMap 0 1 θ
  have hτ : HasDerivAt circleTangent (-circleMap 0 1 θ) θ := by
    have := (hasDerivAt_circleMap 0 1 θ).mul_const I
    unfold circleTangent
    convert this using 1
    rw [mul_assoc, I_mul_I, mul_neg_one]
  have hXγ : HasDerivAt (fun t => X (circleMap 0 1 t))
      (fderiv ℝ X (circleMap 0 1 θ) (circleTangent θ)) θ :=
    (hX _).hasFDerivAt.comp_hasDerivAt θ hγ
  convert hXγ.inner ℝ hτ using 1
  rw [inner_neg_right, real_inner_comm (circleMap 0 1 θ), real_inner_comm (circleTangent θ)]
  ring

/-- **The first variation of the circle** as an integral over the parameter interval:
`δ[C](X) = ∫_0^{2π} ⟪γ(θ), X(γ(θ))⟫ dθ` with `γ(θ) = e^{iθ}`. -/
theorem firstVariation_circleVarifold_apply (X : 𝓓^{1}((⊤ : Opens ℂ), ℂ)) :
    firstVariation circleVarifold X =
      ∫ θ in Icc 0 (2 * π), ⟪circleMap 0 1 θ, X (circleMap 0 1 θ)⟫ := by
  have hX : Differentiable ℝ X := X.contDiff.differentiable one_ne_zero
  rw [firstVariation_apply, circleVarifold, integral_map
    continuous_circleVarifoldParam.aemeasurable
    (integrable_tangentialDivergence X).aestronglyMeasurable]
  simp only [circleVarifoldParam, circleTangentLine, coe_circlePoint,
    tangentialDivergence_spanLine _ _ _ (norm_circleTangent _)]
  have hD : Continuous fun θ =>
      ⟪circleTangent θ, fderiv ℝ X (circleMap 0 1 θ) (circleTangent θ)⟫ :=
    continuous_circleTangent.inner (((X.contDiff.continuous_fderiv one_ne_zero).comp
      (continuous_circleMap 0 1)).clm_apply continuous_circleTangent)
  have hI : Continuous fun θ => ⟪circleMap 0 1 θ, X (circleMap 0 1 θ)⟫ :=
    (continuous_circleMap 0 1).inner (X.continuous.comp (continuous_circleMap 0 1))
  have hFTC : ∫ θ in (0)..(2 * π),
      (⟪circleTangent θ, fderiv ℝ X (circleMap 0 1 θ) (circleTangent θ)⟫ -
        ⟪circleMap 0 1 θ, X (circleMap 0 1 θ)⟫) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hasDerivAt_inner_circleTangent hX θ) ((hD.sub hI).intervalIntegrable _ _)]
    have h1 : circleMap 0 1 (2 * π) = circleMap 0 1 0 := by
      simpa using periodic_circleMap 0 1 0
    simp only [circleTangent, h1, sub_self]
  rw [intervalIntegral.integral_sub (hD.intervalIntegrable _ _) (hI.intervalIntegrable _ _),
    sub_eq_zero, intervalIntegral.integral_of_le two_pi_pos.le,
    intervalIntegral.integral_of_le two_pi_pos.le] at hFTC
  rwa [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]

/-- The first variation of the circle as an integral against `circleMeasure`. -/
private theorem firstVariation_circleVarifold_eq_integral_circleMeasure
    (X : 𝓓^{1}((⊤ : Opens ℂ), ℂ)) :
    firstVariation circleVarifold X = ∫ x, ⟪(x : ℂ), X x⟫ ∂circleMeasure := by
  rw [firstVariation_circleVarifold_apply, circleMeasure,
    integral_map continuous_circlePoint.aemeasurable
      (continuous_subtypeVal.inner (X.continuous.comp continuous_subtypeVal)).aestronglyMeasurable]
  simp only [coe_circlePoint]

/-- **The first variation of the circle** against its weight `‖[C]‖ = H¹⌞C`:
`δ[C](X) = ∫_C ⟪x, X(x)⟫ dH¹(x)`. -/
theorem firstVariation_circleVarifold_eq_integral (X : 𝓓^{1}((⊤ : Opens ℂ), ℂ)) :
    firstVariation circleVarifold X = ∫ x, ⟪x, X x⟫ ∂weight circleVarifold := by
  rw [firstVariation_circleVarifold_apply, weight_circleVarifold_eq_map,
    integral_map (continuous_circleMap 0 1).aemeasurable
      (continuous_id.inner X.continuous).aestronglyMeasurable,
    integral_Icc_eq_integral_Ioc]

/-- The total variation measure of the circle varifold is `circleMeasure`. -/
private theorem firstVariationMeasure_circleVarifold_eq :
    firstVariationMeasure circleVarifold = circleMeasure := by
  rw [firstVariationMeasure_def]
  refine Distribution.massMeasure_eq_of_apply_eq_integral_inner
    (η := fun x : (⊤ : Opens ℂ) => (x : ℂ)) continuous_subtypeVal.aestronglyMeasurable ?_
    firstVariation_circleVarifold_eq_integral_circleMeasure
  rw [circleMeasure]
  refine (ae_map_iff continuous_circlePoint.aemeasurable ?_).2
    (Filter.Eventually.of_forall fun θ => by simp)
  exact (isClosed_eq (continuous_norm.comp continuous_subtypeVal) continuous_const).measurableSet

/-- The circle varifold has locally bounded first variation. -/
theorem hasLocallyBoundedFirstVariation_circleVarifold :
    HasLocallyBoundedFirstVariation circleVarifold := by
  by_contra h
  have h0 := firstVariationMeasure_of_not_hasLocallyBoundedFirstVariation h
  rw [firstVariationMeasure_circleVarifold_eq] at h0
  have := congrArg (fun μ : Measure (⊤ : Opens ℂ) => μ univ) h0
  simp only [circleMeasure, FunLike.coe_zero, Pi.zero_apply] at this
  rw [Measure.map_apply continuous_circlePoint.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Icc] at this
  simp only [ENNReal.ofReal_eq_zero, sub_zero] at this
  linarith [pi_pos]

/-- **`‖δ[C]‖ = H¹⌞C`**: the total variation measure of the first variation of the unit circle,
read in the plane, is the one-dimensional Hausdorff measure on the circle. -/
theorem map_firstVariationMeasure_circleVarifold :
    (firstVariationMeasure circleVarifold).map ((↑) : (⊤ : Opens ℂ) → ℂ) =
      μHE[1].restrict (sphere (0 : ℂ) 1) := by
  have hγ : Subtype.val ∘ circlePoint = circleMap 0 1 := funext coe_circlePoint
  rw [firstVariationMeasure_circleVarifold_eq, circleMeasure,
    Measure.map_map continuous_subtypeVal.measurable
      continuous_circlePoint.measurable, hγ, ← weight_circleVarifold_eq_map]
  exact weight_circleVarifold

end TauCeti.Examples.CircleVarifold
