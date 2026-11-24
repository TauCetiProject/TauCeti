/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Basic

/-!
# Joint measurability of the applied derivative

Mathlib proves that the derivative `fderiv 𝕜 f` of an arbitrary function is measurable
(`measurable_fderiv`), and that so is `x ↦ fderiv 𝕜 f x y` for a fixed vector `y`
(`measurable_fderiv_apply_const`). This file adds the joint statement in the point and the
vector, so that `fun_prop` can prove the measurability of expressions such as
`x ↦ fderiv 𝕜 f x (g x)` for a measurable `g`. It composes `measurable_fderiv` with the joint
measurability of evaluation, `ContinuousLinearMap.measurable_apply₂`, under the same
second-countability assumption.

For a self-map of a finite-dimensional space the Jacobian determinant `x ↦ det (fderiv 𝕜 f x)` is
measurable as well, being a continuous function of the derivative.

An arbitrary function is continuous on its regular set `{x | fderiv 𝕜 f x ≠ 0}`, which is
measurable, so the regular part of the preimage of a measurable set is measurable.

The derivative in a parameter, `x ↦ deriv (fun t ↦ f t x) θ`, of a family of almost everywhere
strongly measurable functions `f t` is almost everywhere strongly measurable where the family is
almost everywhere differentiable at `θ`: it is the almost everywhere limit of the difference
quotients along a sequence `θ + rⁿ`.

## Main results

* `TauCeti.measurable_fderiv_apply`: the map `(x, y) ↦ fderiv 𝕜 f x y` is measurable.
* `TauCeti.measurable_det_fderiv`: the Jacobian determinant `x ↦ det (fderiv 𝕜 f x)` is
  measurable.
* `TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero`: the regular part
  `f⁻¹(I) ∩ {Df ≠ 0}` of the preimage of a measurable set is measurable.
* `TauCeti.aestronglyMeasurable_deriv_of_ae_differentiableAt`: the derivative in a parameter of
  an almost everywhere differentiable family of measurable functions is measurable.
-/

public section

open MeasureTheory

namespace TauCeti

/-- The derivative `x ↦ deriv (fun t ↦ f t x) θ` in a parameter of a family of almost everywhere
strongly measurable functions `f t` is almost everywhere strongly measurable, when the family is
almost everywhere differentiable in the parameter at `θ`. -/
theorem aestronglyMeasurable_deriv_of_ae_differentiableAt {𝕜 α F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace α]
    {μ : Measure α} {f : 𝕜 → α → F} {θ : 𝕜} (hf : ∀ t, AEStronglyMeasurable (f t) μ)
    (hd : ∀ᵐ x ∂μ, DifferentiableAt 𝕜 (fun t ↦ f t x) θ) :
    AEStronglyMeasurable (fun x ↦ deriv (fun t ↦ f t x) θ) μ := by
  obtain ⟨r, hr₀, hr₁⟩ := NormedField.exists_norm_lt_one 𝕜
  have hr : Filter.Tendsto (fun n : ℕ ↦ r ^ n) Filter.atTop (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr₁,
      Filter.Eventually.of_forall fun n ↦ pow_ne_zero n (norm_pos_iff.1 hr₀)⟩
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun (n : ℕ) x ↦ (r ^ n)⁻¹ • (f (θ + r ^ n) x - f θ x))
    (fun n ↦ ((hf _).sub (hf θ)).const_smul _) ?_
  filter_upwards [hd] with x hx
  exact (hasDerivAt_iff_tendsto_slope_zero.1 hx.hasDerivAt).comp hr

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopologyEither (E →L[𝕜] F) E]

/-- The derivative of an arbitrary function, applied to a vector, is jointly measurable in the
point and the vector. No differentiability is assumed, the derivative being `0` where `f` is not
differentiable. -/
@[fun_prop]
theorem measurable_fderiv_apply (f : E → F) : Measurable fun p : E × E ↦ fderiv 𝕜 f p.1 p.2 := by
  borelize (E →L[𝕜] F)
  exact ContinuousLinearMap.measurable_apply₂.comp ((measurable_fderiv 𝕜 f).prodMap measurable_id)

/-- The Jacobian determinant of an arbitrary self-map of a finite-dimensional space is measurable.
No differentiability is assumed, the derivative being `0` where `f` is not differentiable. -/
@[fun_prop]
theorem measurable_det_fderiv [CompleteSpace 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    [FiniteDimensional 𝕜 E] (f : E → E) : Measurable fun x ↦ (fderiv 𝕜 f x).det := by
  have := FiniteDimensional.completeSpace 𝕜 E
  borelize (E →L[𝕜] E)
  exact ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv 𝕜 f)

variable {𝕜}

omit [SecondCountableTopologyEither (E →L[𝕜] F) E] in
/-- The regular part `f⁻¹(I) ∩ {Df ≠ 0}` of the preimage of a measurable set is measurable, for
every function `f`: the function is continuous on its regular set, which is measurable. -/
theorem measurableSet_preimage_inter_setOf_fderiv_ne_zero {f : E → F} {I : Set F}
    (hI : MeasurableSet I) : MeasurableSet (f ⁻¹' I ∩ {x | fderiv 𝕜 f x ≠ 0}) := by
  classical
  have hR : MeasurableSet {x | fderiv 𝕜 f x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv 𝕜 f)
  have hk : Measurable ({x | fderiv 𝕜 f x ≠ 0}.piecewise f 0) :=
    ContinuousOn.measurable_piecewise
      (fun x hx ↦ (differentiableAt_of_fderiv_ne_zero hx).continuousAt.continuousWithinAt)
      continuousOn_const hR
  convert (hk hI).inter hR using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
  intro hx
  rw [Set.piecewise_eq_of_mem _ _ _ hx]

end TauCeti
