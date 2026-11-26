/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Linear images of curves

A curve whose derivative on a closed interval is killed by a continuous linear map has constant
image under that map on that interval. The derivative of the image of a curve under a continuous
linear equivalence is the image of its derivative, with no differentiability hypothesis.

## Main results

* `ContinuousLinearMap.apply_eq_apply_left_of_hasDerivWithinAt`: the image under a continuous
  linear map of such a curve agrees with its value at the left endpoint.
* `ContinuousLinearEquiv.comp_deriv`: `deriv (L ∘ f) x = L (deriv f x)` for a continuous linear
  equivalence `L`, whether or not `f` is differentiable at `x`.
-/

public section

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A curve whose derivative on a closed interval is sent to zero by a continuous linear map `L`
has constant image under `L` on that interval. -/
theorem ContinuousLinearMap.apply_eq_apply_left_of_hasDerivWithinAt (L : E →L[ℝ] F)
    {γ γ' : ℝ → E} {a b : ℝ} (h : ∀ t ∈ Icc a b, HasDerivWithinAt γ (γ' t) (Icc a b) t)
    (h₁ : ∀ t ∈ Icc a b, L (γ' t) = 0) {t : ℝ} (ht : t ∈ Icc a b) : L (γ t) = L (γ a) := by
  rcases lt_or_ge a b with hab | hab
  · have hβ : ∀ t ∈ Icc a b, HasDerivWithinAt (L ∘ γ) 0 (Icc a b) t := fun t ht => by
      simpa [h₁ t ht] using L.hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
    exact constant_of_derivWithin_zero (fun t ht => (hβ t ht).differentiableWithinAt)
      (fun t ht => (hβ t (Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt (Ico_subset_Icc_self ht))) t ht
  · rw [le_antisymm (ht.2.trans hab) ht.1]

/-- The derivative of the image of a curve under a continuous linear equivalence `L` is `L` applied
to its derivative, whether or not the curve is differentiable. -/
theorem ContinuousLinearEquiv.comp_deriv {𝕜 G G' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
    (L : G ≃L[𝕜] G') (f : 𝕜 → G) (x : 𝕜) : deriv (L ∘ f) x = L (deriv f x) := by
  rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv, L.comp_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
