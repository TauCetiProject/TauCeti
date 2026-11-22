/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

/-!
# Iterated Fréchet derivatives under the star operation

When the scalar field `𝕜` carries a trivial star operation (`[TrivialStar 𝕜]`), `star` on a normed
`𝕜`-star-module is a `𝕜`-linear continuous equivalence (`starL' 𝕜`) — and a `𝕜`-linear isometric
equivalence when `[NormedStarGroup _]` holds. Composing with `star` on the left, on the right, or
on both sides therefore transforms every iterated Fréchet derivative `iteratedFDeriv 𝕜 m` without
any differentiability hypothesis on the underlying function.

## Main results

* `TauCeti.iteratedFDeriv_star`, `TauCeti.iteratedFDeriv_star_apply`,
  `TauCeti.norm_iteratedFDeriv_star`: post-composition `x ↦ star (f x)` conjugates the output of
  every iterated derivative and preserves its operator norm.
* `TauCeti.iteratedFDeriv_comp_star`, `TauCeti.iteratedFDeriv_comp_star_apply`,
  `TauCeti.norm_iteratedFDeriv_comp_star`: pre-composition `x ↦ f (star x)` evaluates the iterated
  derivative at `star x` with conjugated tangent inputs and preserves its operator norm.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section PostComposition

variable [StarAddMonoid F] [StarModule 𝕜 F]

/-- Post-composing with `star` composes every iterated Fréchet derivative on the left with
`starL' 𝕜`, without any differentiability hypothesis. -/
theorem iteratedFDeriv_star [ContinuousStar F] (f : E → F) (m : ℕ) (x : E) :
    iteratedFDeriv 𝕜 m (fun y ↦ star (f y)) x =
      (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv 𝕜 m f x) := by
  let σ : F ≃L[𝕜] F := starL' 𝕜
  have hcomp : (fun y ↦ star (f y)) = σ ∘ f := by
    funext y
    simp [σ]
  rw [hcomp, σ.iteratedFDeriv_comp_left]

/-- Post-composing with `star` applies `star` to the output of every iterated Fréchet derivative,
without any differentiability hypothesis. -/
theorem iteratedFDeriv_star_apply [ContinuousStar F] (f : E → F) (m : ℕ) (x : E) (v : Fin m → E) :
    iteratedFDeriv 𝕜 m (fun y ↦ star (f y)) x v = star (iteratedFDeriv 𝕜 m f x v) := by
  rw [iteratedFDeriv_star, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply]
  simp

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

/-- Pre-composing with `star` evaluates every iterated Fréchet derivative at `star x` and
precomposes every slot with `starL' 𝕜`, without any differentiability hypothesis. -/
theorem iteratedFDeriv_comp_star [ContinuousStar E] (f : E → F) (m : ℕ) (x : E) :
    iteratedFDeriv 𝕜 m (fun y ↦ f (star y)) x =
      (iteratedFDeriv 𝕜 m f (star x)).compContinuousLinearMap fun _ ↦
        (starL' 𝕜 : E ≃L[𝕜] E).toContinuousLinearMap := by
  let σ : E ≃L[𝕜] E := starL' 𝕜
  have hcomp : (fun y ↦ f (star y)) = f ∘ σ := by
    funext y
    simp [σ]
  rw [hcomp, σ.iteratedFDeriv_comp_right]
  simp [σ]

/-- Pre-composing with `star` evaluates every iterated Fréchet derivative at `star x` on the
conjugated tangent inputs, without any differentiability hypothesis. -/
theorem iteratedFDeriv_comp_star_apply [ContinuousStar E] (f : E → F) (m : ℕ) (x : E)
    (v : Fin m → E) :
    iteratedFDeriv 𝕜 m (fun y ↦ f (star y)) x v =
      iteratedFDeriv 𝕜 m f (star x) (fun i ↦ star (v i)) := by
  rw [iteratedFDeriv_comp_star, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp

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
