/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.Complex.Basic

/-!
# The canonical real star-algebra embedding of an `RCLike` field into `ℂ`

Every `RCLike` scalar field `𝕜` (`ℝ` or `ℂ`) embeds canonically into `ℂ` via the continuous real
linear map `RCLike.map 𝕜 ℂ`, sending `z` to `(re z : ℂ) + (im z : ℂ) * Complex.I`. Because the
`RCLike` axioms prescribe the real and imaginary parts of `1`, products, and conjugates by the same
formulas as in `ℂ`, `RCLike.map 𝕜 ℂ` is an injective unital `ℝ`-star-algebra homomorphism
(`RCLike.toComplexStarAlgHom`) and an isometry (`RCLike.norm_toComplexStarAlgHom`).

Pushing square matrices forward entrywise along `RCLike.toComplexStarAlgHom` transfers identities
and order inequalities from complex C⋆-algebras to matrices over an arbitrary `RCLike` scalar field.

## Main definitions and results

* `RCLike.toComplexStarAlgHom`: `RCLike.map 𝕜 ℂ` bundled as `𝕜 →⋆ₐ[ℝ] ℂ`.
* `RCLike.toComplexStarAlgHom_injective`: the canonical embedding into `ℂ` is injective.
* `RCLike.norm_toComplexStarAlgHom`: the canonical embedding preserves norms.
-/

public section

namespace RCLike

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The canonical continuous `ℝ`-linear map `RCLike.map 𝕜 ℂ` bundled as a unital `ℝ`-star-algebra
homomorphism `𝕜 →⋆ₐ[ℝ] ℂ`. -/
noncomputable def toComplexStarAlgHom : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun := map 𝕜 ℂ
  map_one' := by simp
  map_mul' z w := by
    apply Complex.ext <;> simp [mul_re, mul_im]
  map_zero' := by simp
  map_add' := (map 𝕜 ℂ).map_add
  commutes' r := by
    apply Complex.ext <;> simp
  map_star' z := by
    apply Complex.ext <;> simp [star_def]

variable {𝕜}

@[simp]
theorem coe_toComplexStarAlgHom : ⇑(toComplexStarAlgHom 𝕜) = map 𝕜 ℂ :=
  (rfl)

theorem toComplexStarAlgHom_apply (z : 𝕜) :
    toComplexStarAlgHom 𝕜 z = (re z : ℂ) + (im z : ℂ) * Complex.I :=
  (rfl)

theorem re_toComplexStarAlgHom (z : 𝕜) : (toComplexStarAlgHom 𝕜 z).re = re z := by
  simp [toComplexStarAlgHom_apply]

theorem im_toComplexStarAlgHom (z : 𝕜) : (toComplexStarAlgHom 𝕜 z).im = im z := by
  simp [toComplexStarAlgHom_apply]

/-- The canonical embedding of an `RCLike` field into `ℂ` is injective. -/
theorem toComplexStarAlgHom_injective : Function.Injective (toComplexStarAlgHom 𝕜) := by
  intro z w h
  apply RCLike.ext
  · simpa only [re_toComplexStarAlgHom] using congrArg Complex.re h
  · simpa only [im_toComplexStarAlgHom] using congrArg Complex.im h

@[fun_prop]
theorem continuous_toComplexStarAlgHom : Continuous (toComplexStarAlgHom 𝕜) :=
  (map 𝕜 ℂ).continuous

theorem norm_toComplexStarAlgHom (z : 𝕜) : ‖toComplexStarAlgHom 𝕜 z‖ = ‖z‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, re_toComplexStarAlgHom,
    im_toComplexStarAlgHom, ← normSq_apply, normSq_eq_def']

end RCLike
