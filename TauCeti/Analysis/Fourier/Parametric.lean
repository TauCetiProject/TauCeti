/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier integrals of compactly supported functions of two variables

Let `g : E × E → F` vanish for first variables outside a compact set `K`, on a finite-dimensional
real inner-product space `E`. Its Fourier integral in the first variable,
`(η, ξ) ↦ ∫ exp(-2πi ⟪y, η⟫) g(y, ξ) dy`, is jointly continuous in the dual variable `η` and the
second variable `ξ` when `g` is continuous, and, when `g` is smooth, may be differentiated in `ξ`
under the integral sign: the integrand and its derivatives in `ξ` are dominated near every `ξ₀` by
a multiple of the indicator of `K`.

These are the regularity properties of the Fourier transform `b̂(η, ξ)` of the position slices of a
symbol with compact spatial support, used in the composition calculus of pseudodifferential
operators.

## Main declarations

* `TauCeti.exists_norm_fderiv_snd_le_indicator`: the domination of the derivatives in the second
  variable by a multiple of the indicator of `K`.
* `TauCeti.hasFDerivAt_integral_fourierChar_smul`: differentiation in `ξ` under the Fourier
  integral, with `TauCeti.integral_fourierChar_smul_fderiv_apply` evaluating the derivative in a
  direction.
* `TauCeti.continuous_integral_fourierChar_smul`: joint continuity of the Fourier integral.
-/

public section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {g : E × E → F} {K : Set E}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivatives in the second variable of a smooth `g` vanishing for first variables outside a
compact set `K` are bounded on `E × closedBall ξ₀ 1` by a multiple of the indicator of `K`. -/
theorem exists_norm_fderiv_snd_le_indicator (hg : ContDiff ℝ ∞ g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) (ξ₀ : E) :
    ∃ B, ∀ y, ∀ ξ ∈ Metric.closedBall ξ₀ 1,
      ‖fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ‖ ≤ K.indicator (fun _ ↦ B) y := by
  have hD : Continuous fun q : E × E ↦ fderiv ℝ (fun ξ ↦ g (q.1, ξ)) q.2 :=
    (ContDiff.fderiv (f := fun (q : E × E) ξ ↦ g (q.1, ξ))
      (hg.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (n := 0) (by simp)).continuous
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall ξ₀ 1)).exists_bound_of_continuousOn
    hD.continuousOn
  refine ⟨B, fun y ξ hξ ↦ ?_⟩
  by_cases hy : y ∈ K
  · rw [Set.indicator_of_mem hy]
    exact hB (y, ξ) ⟨hy, hξ⟩
  · have h0 : (fun ξ ↦ g (y, ξ)) = fun _ ↦ 0 := funext (hKg y hy)
    rw [Set.indicator_of_notMem hy, h0]
    simp

/-- The integrand `y ↦ exp(-2πi ⟪y, η⟫) ∂_ξ g(y, ξ)` of the derivative of the Fourier integral is
integrable. -/
theorem integrable_fourierChar_smul_fderiv (hg : ContDiff ℝ ∞ g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) (η ξ : E) :
    Integrable fun y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ := by
  obtain ⟨B, hB⟩ := exists_norm_fderiv_snd_le_indicator hg hK hKg ξ
  exact ((integrable_indicator_iff hK.measurableSet).2
    (integrableOn_const (C := B) hK.measure_lt_top.ne)).mono'
    ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))).smul
      (ContDiff.fderiv (f := fun (y : E) ξ ↦ g (y, ξ)) hg contDiff_const (n := 0)
        (by simp)).continuous).aestronglyMeasurable
    (.of_forall fun y ↦ by
      rw [norm_smul, Circle.norm_coe, one_mul]
      exact hB y ξ (Metric.mem_closedBall_self zero_le_one))

/-- **Differentiation under the Fourier integral.** For a smooth `g` vanishing for first variables
outside a compact set, the Fourier integral in the first variable is differentiable in the second
variable, with the Fourier integral of the derivative as derivative. -/
theorem hasFDerivAt_integral_fourierChar_smul (hg : ContDiff ℝ ∞ g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) (η ξ₀ : E) :
    HasFDerivAt (fun ξ ↦ ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ))
      (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀) ξ₀ := by
  obtain ⟨B, hB⟩ := exists_norm_fderiv_snd_le_indicator hg hK hKg ξ₀
  have he : Continuous fun y : E ↦ (𝐞 (-⟪y, η⟫) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hslice (ξ : E) : Continuous fun y ↦ g (y, ξ) :=
    hg.continuous.comp (continuous_id.prodMk continuous_const)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun ξ y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ)
    (bound := K.indicator fun _ ↦ B)
    (Metric.ball_mem_nhds ξ₀ one_pos)
    (.of_forall fun ξ ↦ (he.smul (hslice ξ)).aestronglyMeasurable)
    ((he.smul (hslice ξ₀)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy ↦ by simp [hKg y hy]))
    (integrable_fourierChar_smul_fderiv hg hK hKg η ξ₀).aestronglyMeasurable
    (.of_forall fun y ξ hξ ↦ ?_)
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (.of_forall fun y ξ _ ↦ ?_)
  · rw [norm_smul, Circle.norm_coe, one_mul]
    exact hB y ξ (Metric.ball_subset_closedBall hξ)
  · exact (((hg.comp (contDiff_prodMk_right y)).differentiable (by simp) ξ).hasFDerivAt).const_smul
      ((𝐞 (-⟪y, η⟫) : ℂ))

/-- The derivative of the Fourier integral in a direction `v` is the Fourier integral of the
derivative of `g` in the direction `v`. -/
theorem integral_fourierChar_smul_fderiv_apply (hg : ContDiff ℝ ∞ g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) (η ξ v : E) :
    (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ) v =
      ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ v := by
  rw [ContinuousLinearMap.integral_apply (integrable_fourierChar_smul_fderiv hg hK hKg η ξ)]
  simp only [smul_apply]

/-- The Fourier integral in the first variable of a continuous `g` vanishing for first variables
outside a compact set is jointly continuous in the dual variable and the second variable. -/
theorem continuous_integral_fourierChar_smul (hg : Continuous g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) :
    Continuous fun q : E × E ↦ ∫ y, (𝐞 (-⟪y, q.1⟫) : ℂ) • g (y, q.2) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall q₀.2 1)).exists_bound_of_continuousOn
    hg.continuousOn
  have he : Continuous fun q : E × E ↦ (𝐞 (-⟪q.1, q.2⟫) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  refine continuousAt_of_dominated (bound := K.indicator fun _ ↦ B)
    (.of_forall fun q ↦ ((he.comp (continuous_id.prodMk continuous_const)).smul
      (hg.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable) ?_
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (.of_forall fun y ↦ ((he.comp (continuous_const.prodMk continuous_fst)).smul
      (hg.comp (continuous_const.prodMk continuous_snd))).continuousAt)
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (Metric.closedBall_mem_nhds q₀.2 one_pos)] with q hq
  refine .of_forall fun y ↦ ?_
  rw [norm_smul, Circle.norm_coe, one_mul]
  by_cases hy : y ∈ K
  · rw [Set.indicator_of_mem hy]
    exact hB (y, q.2) ⟨hy, hq⟩
  · rw [Set.indicator_of_notMem hy, hKg y hy, norm_zero]

end TauCeti
