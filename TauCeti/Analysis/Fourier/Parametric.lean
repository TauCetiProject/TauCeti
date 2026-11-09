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
parameter `ξ` in a real normed space, which vanishes for positions outside a fixed compact set,
this file differentiates the Fourier transforms `f̂(θ, ξ) = 𝓕 (fun y ↦ f (y, ξ)) θ` of the position
slices in the parameter.

## Main declarations

* `TauCeti.hasFDerivAt_fourier_slice`: for `C¹` functions `f`, `ξ ↦ f̂(θ, ξ)` is differentiable,
  and its derivative is the Fourier transform of the partial derivative of `f` in the parameter.
* `TauCeti.hasFDerivAt_fourier_slice_coordinateDeriv`: for a parameter in `ℝⁿ`, the partial
  derivatives are `∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped RealInnerProductSpace

namespace TauCeti

variable {E P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup G]
  [NormedSpace ℂ G] {K : Set E} {f : E × P → G}

/-- The partial derivative of `f` in the parameter vanishes at positions where `f` does. -/
private theorem fderiv_slice_eq_zero (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) {y : E} (hy : y ∉ K)
    (ξ : P) : fderiv ℝ (fun η ↦ f (y, η)) ξ = 0 := by
  have h0 : (fun η ↦ f (y, η)) = 0 := funext fun η ↦ hfK y hy η
  simp [h0]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The partial derivative `(y, η) ↦ ∂_η f(y, η)` of a `C¹` function in its second variable is
continuous. -/
private theorem continuous_fderiv_slice (hf : ContDiff ℝ 1 f) :
    Continuous fun q : E × P ↦ fderiv ℝ (fun η ↦ f (q.1, η)) q.2 :=
  (ContDiff.fderiv (f := fun (q : E × P) η ↦ f (q.1, η))
    (hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd
    (n := 0) (by simp)).continuous

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Differentiation of a Fourier transform in a parameter.** For a `C¹` function `f` of a
position and a parameter, vanishing for positions outside a compact set, the Fourier transform
`f̂(θ, ξ)` of the position slices is differentiable in the parameter, and its derivative is the
Fourier transform of the partial derivative `∂_ξ f` of `f` in the parameter. -/
theorem hasFDerivAt_fourier_slice (hf : ContDiff ℝ 1 f) (hK : IsCompact K)
    (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) (θ : E) (ξ : P) :
    HasFDerivAt (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ)
      (𝓕 (fun y ↦ fderiv ℝ (fun η ↦ f (y, η)) ξ) θ) ξ := by
  set D : E × P → P →L[ℝ] G := fun q ↦ fderiv ℝ (fun η ↦ f (q.1, η)) q.2
  have hD : Continuous D := continuous_fderiv_slice hf
  have hphase : Continuous fun y : E ↦ (𝐞 (-⟪y, θ⟫) : ℂ) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).subtype_val
  -- `D` is bounded on `K × V` for a neighbourhood `V` of `ξ`.
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun y ↦ D (y, ξ))
    (hD.comp (by fun_prop)).continuousOn
  obtain ⟨U, V, -, hV, hKU, hξV, hUV⟩ := generalized_tube_lemma hK (isCompact_singleton (x := ξ))
    (isOpen_lt hD.norm continuous_const : IsOpen {q : E × P | ‖D q‖ < C + 1})
    fun ⟨y, η⟩ ⟨hy, hη⟩ ↦ by
      obtain rfl : η = ξ := hη
      exact (hC y hy).trans_lt (lt_add_one C)
  simp only [Real.fourier_eq, Circle.smul_def]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := V)
    (F := fun η y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • f (y, η))
    (F' := fun η y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • D (y, η))
    (bound := K.indicator fun _ ↦ C + 1) (hV.mem_nhds (hξV rfl))
    (.of_forall fun η ↦ (hphase.smul (hf.continuous.comp (by fun_prop))).aestronglyMeasurable)
    ((hphase.smul (hf.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy ↦ by simp [hfK y hy]))
    (hphase.smul (hD.comp (by fun_prop))).aestronglyMeasurable (.of_forall fun y η hη ↦ ?_)
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (.of_forall fun y η _ ↦ ?_)
  · by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, norm_smul, Circle.norm_coe, one_mul]
      exact (hUV ⟨hKU hy, hη⟩ : ‖D (y, η)‖ < C + 1).le
    · simp [Set.indicator_of_notMem hy, D, fderiv_slice_eq_zero hfK hy]
  · exact (((hf.comp (contDiff_prodMk_right y)).differentiable one_ne_zero
      η).hasFDerivAt).const_smul _

/-- **Differentiation of a Fourier transform in a parameter in `ℝⁿ`.** For a `C¹` function `f` of a
position and a parameter in `ℝⁿ`, vanishing for positions outside a compact set, the partial
derivatives of the Fourier transform `f̂(θ, ξ)` of the position slices are the Fourier transforms
of the partial derivatives: `∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`. -/
theorem hasFDerivAt_fourier_slice_coordinateDeriv {n : ℕ} {f : E × CoordinateSpace n → G}
    (hf : ContDiff ℝ 1 f) (hK : IsCompact K) (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) (θ : E)
    (ξ : CoordinateSpace n) :
    HasFDerivAt (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ)
      (∑ j, (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
        (𝓕 (fun y ↦ coordinateDeriv [j] (fun η ↦ f (y, η)) ξ) θ)) ξ := by
  have hc : Continuous fun y ↦ fderiv ℝ (fun η ↦ f (y, η)) ξ :=
    (continuous_fderiv_slice hf).comp (continuous_id.prodMk continuous_const)
  have hint : Integrable fun y ↦ fderiv ℝ (fun η ↦ f (y, η)) ξ :=
    hc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy ↦ fderiv_slice_eq_zero hfK hy ξ)
  refine (hasFDerivAt_fourier_slice hf hK hfK θ ξ).congr_fderiv
    (ContinuousLinearMap.ext fun h ↦ ?_)
  -- Expand `h` in the coordinate basis.
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h, map_sum]
  simp only [map_smul, sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, coordinateDeriv_cons,
    coordinateDeriv_nil]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Real.fourier_continuousLinearMap_apply hint]

end TauCeti
