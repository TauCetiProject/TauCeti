/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Fourier transforms depending on a parameter

For a function `f(y, ξ)` of a position `y` in a finite-dimensional real inner product space and a
parameter `ξ`, which vanishes for positions outside a fixed compact set, this file studies the
Fourier transforms `f̂(θ, ξ) = 𝓕 (fun y ↦ f (y, ξ)) θ` of the position slices. They are jointly
continuous in `(θ, ξ)` when `f` is continuous, and for a `C¹` function of a parameter in `ℝⁿ` they
are differentiable in the parameter, the partial derivatives being the Fourier transforms of the
partial derivatives of `f`.

These are the regularity statements used for the Fourier transform `b̂(θ, ξ)` of a symbol with
compact spatial support in the composition of pseudodifferential operators.

## Main declarations

* `TauCeti.continuous_fourier_slice`: `(θ, ξ) ↦ f̂(θ, ξ)` is continuous.
* `TauCeti.hasFDerivAt_fourier_slice`: `∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`.

## Implementation notes

The target is an abstract complex normed space `G` rather than a space of operators such as
`V →L[ℂ] W`: for the latter, the instance searches for the measurability and the norms of
`CoordinateSpace n →L[ℝ] (V →L[ℂ] W)`-valued functions time out.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped RealInnerProductSpace

namespace TauCeti

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℂ G] {K : Set E}

/-- The Fourier transform `f̂(θ, ξ)` of the position slices `y ↦ f(y, ξ)` of a continuous function
vanishing for positions outside a compact set is jointly continuous in `(θ, ξ)`. -/
theorem continuous_fourier_slice {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P] {f : E × P → G} (hf : Continuous f) (hK : IsCompact K)
    (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) :
    Continuous fun q : E × P ↦ 𝓕 (fun y ↦ f (y, q.2)) q.1 := by
  have hF : (fun q : E × P ↦ 𝓕 (fun y ↦ f (y, q.2)) q.1) =
      fun q ↦ ∫ y in K, 𝐞 (-⟪y, q.1⟫) • f (y, q.2) := by
    funext q
    rw [Real.fourier_eq]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [hfK y hy, smul_zero]).symm
  rw [hF]
  exact continuous_parametric_integral_of_continuous
    ((Real.continuous_fourierChar.comp (by fun_prop)).smul (hf.comp (by fun_prop))) hK

/-- **Differentiation of `f̂(θ, ξ)` in the parameter.** For a `C¹` function `f` of a position and
a parameter in `ℝⁿ`, vanishing for positions outside a compact set, the Fourier transform of the
position slices is differentiable in the parameter, with partial derivatives the Fourier
transforms of the partial derivatives: `∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`. -/
theorem hasFDerivAt_fourier_slice {n : ℕ} {f : E × CoordinateSpace n → G} (hf : ContDiff ℝ 1 f)
    (hK : IsCompact K) (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) (θ : E) (ξ : CoordinateSpace n) :
    HasFDerivAt (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ)
      (∑ j, (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
        (𝓕 (fun y ↦ coordinateDeriv [j] (fun η ↦ f (y, η)) ξ) θ)) ξ := by
  -- The phase factor, as a real-linear map, so that no complex scalars act on derivatives.
  set e : E → G →L[ℝ] G := fun y ↦
    ContinuousLinearMap.lsmul ℝ ℂ (𝐞 (-⟪y, θ⟫) : ℂ) with he_def
  have he : Continuous e := (ContinuousLinearMap.lsmul ℝ ℂ).continuous.comp
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop)))
  have he_norm (y : E) : ‖e y‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_lsmul_apply_le _).trans (by simp)
  -- The partial derivative of `f` in the frequency is jointly continuous.
  have hD : Continuous fun q : E × CoordinateSpace n ↦
      fderiv ℝ (fun η ↦ f (q.1, η)) q.2 :=
    (ContDiff.fderiv (f := fun (q : E × CoordinateSpace n) η ↦ f (q.1, η))
      (hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd
      (n := 0) (by simp)).continuous
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall ξ 1)).exists_bound_of_continuousOn
    hD.continuousOn
  have hdiff (y : E) (η : CoordinateSpace n) : HasFDerivAt (fun η ↦ e y (f (y, η)))
      ((e y).comp (fderiv ℝ (fun η ↦ f (y, η)) η)) η :=
    (e y).hasFDerivAt.comp η
      ((hf.comp (contDiff_prodMk_right y)).differentiable one_ne_zero η).hasFDerivAt
  have hcont (η : CoordinateSpace n) : Continuous fun y ↦ e y (f (y, η)) :=
    he.clm_apply (hf.continuous.comp (continuous_id.prodMk continuous_const))
  have hcont' : Continuous fun y ↦ (e y).comp (fderiv ℝ (fun η ↦ f (y, η)) ξ) :=
    he.clm_comp (hD.comp (continuous_id.prodMk continuous_const))
  have hsupp (η : CoordinateSpace n) : HasCompactSupport fun y ↦ e y (f (y, η)) :=
    HasCompactSupport.intro hK fun y hy ↦ by simp [hfK y hy]
  have hzero (y : E) (hy : y ∉ K) (η : CoordinateSpace n) :
      fderiv ℝ (fun η ↦ f (y, η)) η = 0 := by
    have h0 : (fun η ↦ f (y, η)) = 0 := funext fun η ↦ hfK y hy η
    simp [h0]
  have hsupp' : HasCompactSupport fun y ↦ (e y).comp (fderiv ℝ (fun η ↦ f (y, η)) ξ) :=
    HasCompactSupport.intro hK fun y hy ↦ by simp [hzero y hy]
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun η y ↦ e y (f (y, η)))
    (F' := fun η y ↦ (e y).comp (fderiv ℝ (fun η ↦ f (y, η)) η))
    (bound := K.indicator fun _ ↦ C) (Metric.ball_mem_nhds ξ one_pos)
    (Filter.Eventually.of_forall fun η ↦ (hcont η).aestronglyMeasurable)
    ((hcont ξ).integrable_of_hasCompactSupport (hsupp ξ)) hcont'.aestronglyMeasurable
    (ae_of_all _ fun y η hη ↦ ?_)
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (ae_of_all _ fun y η _ ↦ hdiff y η)
  · have hF : (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ) = fun η ↦ ∫ y, e y (f (y, η)) := by
      funext η
      simp only [Real.fourier_eq, Circle.smul_def, he_def, ContinuousLinearMap.lsmul_apply]
    rw [hF]
    convert key using 1
    refine ContinuousLinearMap.ext fun h ↦ ?_
    have hint := hcont'.integrable_of_hasCompactSupport (μ := volume) hsupp'
    rw [ContinuousLinearMap.integral_apply hint]
    conv_rhs => enter [2, y]; rw [ContinuousLinearMap.apply_eq_sum_single _ h]
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    rw [integral_finsetSum (f := fun j y ↦
      h j • e y (fderiv ℝ (fun η ↦ f (y, η)) ξ (EuclideanSpace.single j 1))) _
      fun j _ ↦ (hint.apply_continuousLinearMap _).smul (h j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_smul]
    congr 1
    simp only [Real.fourier_eq, Circle.smul_def, coordinateDeriv_cons, coordinateDeriv_nil, he_def,
      ContinuousLinearMap.lsmul_apply]
  · refine ((e y).opNorm_comp_le _).trans ?_
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact (mul_le_of_le_one_left (norm_nonneg _) (he_norm y)).trans
        (hC _ (Set.mk_mem_prod hy (Metric.ball_subset_closedBall hη)))
    · simp [hzero y hy, Set.indicator_of_notMem hy]

end TauCeti
