/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic

/-!
# Diagonal complex interpolation

For `0 ≤ θ ≤ 1`, the complex interpolation space `[X, X]_θ` of a constant couple is isometrically
isomorphic to `X` (`CompatibleCouple.ComplexMethodSpace.reflEquiv`).

## Main definitions and results

* `CompatibleCouple.ComplexMethodSpace.reflEquiv`: isometric equivalence `[X, X]_θ ≃ₗᵢ[ℂ] X` for
  `θ ∈ [0, 1]`.
* `CompatibleCouple.ComplexMethodSpace.reflEquiv_apply`,
  `CompatibleCouple.ComplexMethodSpace.reflEquiv_symm_apply`, and
  `CompatibleCouple.ComplexMethodSpace.toSum_reflEquiv_symm`: evaluation and inverse lemmas.
-/

public noncomputable section

open Set

namespace TauCeti.CompatibleCouple.ComplexMethodSpace

/-- For `0 ≤ θ ≤ 1`, `[X, X]_θ ≃ₗᵢ[ℂ] X` via evaluation in the ambient space. -/
def reflEquiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (hθ : θ ∈ Icc 0 1) : (refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] X where
  toFun u := (refl ℂ X).sumSpaceEmbed (toSum u)
  invFun x := ofInter θ ⟨(x, x), by simp⟩
  left_inv u := by ext; simp [toSum_ofInter hθ]
  right_inv x := by simp [toSum_ofInter hθ]
  map_add' u v := by simp
  map_smul' c u := by simp
  norm_map' u := (norm_refl_sumSpaceEmbed (toSum u)).trans (norm_refl u).symm

/-- Applying `reflEquiv` evaluates `toSum u` in `X`. -/
@[simp]
theorem reflEquiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) (u : (refl ℂ X).ComplexMethodSpace θ) :
    reflEquiv hθ u = (refl ℂ X).sumSpaceEmbed (toSum u) :=
  (rfl)

/-- The inverse of `reflEquiv` sends `x : X` to the class of `(x, x) ∈ (refl ℂ X).inter`. -/
theorem reflEquiv_symm_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : X) :
    (reflEquiv hθ).symm x = ofInter θ ⟨(x, x), by simp⟩ :=
  (rfl)

/-- In `(refl ℂ X).SumSpace`, `(reflEquiv hθ).symm x` lies over `fstToSum x`. -/
@[simp]
theorem toSum_reflEquiv_symm {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : X) :
    toSum ((reflEquiv hθ).symm x) = (refl ℂ X).fstToSum x := by
  simp [reflEquiv_symm_apply, toSum_ofInter hθ]

end TauCeti.CompatibleCouple.ComplexMethodSpace
