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
parameter `ξ ∈ ℝⁿ`, which vanishes for positions outside a fixed compact set, this file
differentiates the Fourier transforms `f̂(θ, ξ) = 𝓕 (fun y ↦ f (y, ξ)) θ` of the position slices
in the parameter.

## Main declarations

* `TauCeti.hasFDerivAt_fourier_slice`: for `C¹` functions `f`, `ξ ↦ f̂(θ, ξ)` is differentiable,
  with partial derivatives `∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped RealInnerProductSpace

namespace TauCeti

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℂ G] {K : Set E}

/-- **Differentiation of a Fourier transform in a parameter.** For a `C¹` function `f` of a
position and a parameter in `ℝⁿ`, vanishing for positions outside a compact set, the Fourier
transform `f̂(θ, ξ)` of the position slices is differentiable in the parameter, with partial
derivatives the Fourier transforms of the partial derivatives:
`∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`. -/
theorem hasFDerivAt_fourier_slice {n : ℕ} {f : E × CoordinateSpace n → G} (hf : ContDiff ℝ 1 f)
    (hK : IsCompact K) (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) (θ : E) (ξ : CoordinateSpace n) :
    HasFDerivAt (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ)
      (∑ j, (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
        (𝓕 (fun y ↦ coordinateDeriv [j] (fun η ↦ f (y, η)) ξ) θ)) ξ := by
  -- The partial derivative `D(y, η)` of `f` in the parameter is jointly continuous, and vanishes
  -- for positions outside `K`.
  set D : E × CoordinateSpace n → CoordinateSpace n →L[ℝ] G :=
    fun q ↦ fderiv ℝ (fun η ↦ f (q.1, η)) q.2 with hD_def
  have hD : Continuous D :=
    (ContDiff.fderiv (f := fun (q : E × CoordinateSpace n) η ↦ f (q.1, η))
      (hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd
      (n := 0) (by simp)).continuous
  have hzero : ∀ y ∉ K, ∀ η, D (y, η) = 0 := fun y hy η ↦ by
    have h0 : (fun η ↦ f (y, η)) = 0 := funext fun η ↦ hfK y hy η
    simp [hD_def, h0]
  have hphase : Continuous fun y : E ↦ (𝐞 (-⟪y, θ⟫) : ℂ) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).subtype_val
  have hint' : Integrable fun y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • D (y, ξ) :=
    (hphase.smul (hD.comp (by fun_prop))).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy ↦ by simp [hzero y hy])
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall ξ 1)).exists_bound_of_continuousOn
    hD.continuousOn
  simp only [Real.fourier_eq, Circle.smul_def]
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Metric.ball ξ 1)
    (F := fun η y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • f (y, η))
    (F' := fun η y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • D (y, η))
    (bound := K.indicator fun _ ↦ C) (Metric.ball_mem_nhds ξ one_pos)
    (.of_forall fun η ↦ (hphase.smul (hf.continuous.comp (by fun_prop))).aestronglyMeasurable)
    ((hphase.smul (hf.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy ↦ by simp [hfK y hy]))
    hint'.aestronglyMeasurable (.of_forall fun y η hη ↦ ?_)
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (.of_forall fun y η _ ↦ ?_)).congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  · by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, norm_smul, Circle.norm_coe, one_mul]
      exact hC (y, η) ⟨hy, Metric.ball_subset_closedBall hη⟩
    · simp [Set.indicator_of_notMem hy, hzero y hy]
  · exact (((hf.comp (contDiff_prodMk_right y)).differentiable one_ne_zero
      η).hasFDerivAt).const_smul _
  · -- Expand `D(y, ξ) h` in the coordinates of `h`.
    have hpt : ∀ y, D (y, ξ) h = ∑ j, h j • D (y, ξ) (EuclideanSpace.single j 1) := fun y ↦ by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
      simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, map_sum, map_smul]
    have hj : ∀ j, Integrable fun y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) •
        (h j • D (y, ξ) (EuclideanSpace.single j 1)) := fun j ↦
      (hphase.smul (((hD.comp (by fun_prop)).clm_apply continuous_const).const_smul
        _)).integrable_of_hasCompactSupport
          (HasCompactSupport.intro hK fun y hy ↦ by simp [hzero y hy])
    rw [ContinuousLinearMap.integral_apply hint']
    simp only [smul_apply, hpt, sum_apply,
      ContinuousLinearMap.smulRight_apply, Finset.smul_sum, coordinateDeriv_cons,
      coordinateDeriv_nil, PiLp.proj_apply]
    rw [integral_finsetSum _ fun j _ ↦ hj j]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← integral_smul]
    exact integral_congr_ae (.of_forall fun y ↦ smul_comm _ _ _)

end TauCeti
