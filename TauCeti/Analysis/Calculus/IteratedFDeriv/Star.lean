/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Iterated Fréchet derivatives under the star operation

When the scalar field `𝕜` carries a trivial star operation (`[TrivialStar 𝕜]`), `star` on a normed
`𝕜`-star-module is a `𝕜`-linear continuous equivalence (`starL' 𝕜`), and a `𝕜`-linear isometric
equivalence when `[NormedStarGroup _]` holds. Composing with `star` on the left or on the right
therefore preserves the operator norm of every iterated Fréchet derivative `iteratedFDeriv 𝕜 m`
without any differentiability hypothesis on the underlying function.

## Main results

* `TauCeti.norm_iteratedFDeriv_star`: post-composition `x ↦ star (f x)` preserves the operator
  norm of every iterated Fréchet derivative.
* `TauCeti.norm_iteratedFDeriv_comp_star`: pre-composition `x ↦ f (star x)` preserves the
  operator norm of every iterated Fréchet derivative at `star x`.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section PostComposition

variable [StarAddMonoid F] [StarModule 𝕜 F]

/-- Post-composing with `star` preserves the operator norm of every iterated Fréchet derivative in
a normed star group, without any differentiability hypothesis. -/
@[simp]
theorem norm_iteratedFDeriv_star [NormedStarGroup F] (f : E → F) (m : ℕ) (x : E) :
    ‖iteratedFDeriv 𝕜 m (fun y ↦ star (f y)) x‖ = ‖iteratedFDeriv 𝕜 m f x‖ := by
  let σ : F ≃ₗᵢ[𝕜] F := { (starL' 𝕜 : F ≃L[𝕜] F).toLinearEquiv with norm_map' := norm_star }
  have hcomp : (fun y ↦ star (f y)) = σ ∘ f := by
    funext y
    rw [Function.comp_apply, ← LinearIsometryEquiv.coe_toLinearEquiv]
    simp [σ]
  rw [hcomp, σ.norm_iteratedFDeriv_comp_left]

end PostComposition

section PreComposition

variable [StarAddMonoid E] [StarModule 𝕜 E]

/-- Pre-composing with `star` preserves the operator norm of every iterated Fréchet derivative in
a normed star group, without any differentiability hypothesis. -/
@[simp]
theorem norm_iteratedFDeriv_comp_star [NormedStarGroup E] (f : E → F) (m : ℕ) (x : E) :
    ‖iteratedFDeriv 𝕜 m (fun y ↦ f (star y)) x‖ = ‖iteratedFDeriv 𝕜 m f (star x)‖ := by
  let σ : E ≃ₗᵢ[𝕜] E := { (starL' 𝕜 : E ≃L[𝕜] E).toLinearEquiv with norm_map' := norm_star }
  have hσ (y : E) : σ y = star y := by
    rw [← LinearIsometryEquiv.coe_toLinearEquiv]
    simp [σ]
  have hcomp : (fun y ↦ f (star y)) = f ∘ σ := by
    funext y
    simp [hσ]
  rw [hcomp, σ.norm_iteratedFDeriv_comp_right, hσ]

end PreComposition

end TauCeti
