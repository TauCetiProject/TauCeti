/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic lemmas for normed algebras

This file collects basic constructions and lemmas for normed algebras:

* `TauCeti.normedAlgebraRatOfReal`: much of Mathlib's API for `NormedSpace.exp` (for example
  `NormedSpace.exp_continuous`) assumes a normed `ℚ`-algebra; this names the restriction of scalars
  that makes every real normed algebra a normed `ℚ`-algebra so files can enable it locally.
* `AlgEquiv.norm_map` and `AlgEquiv.isometry`: every `𝕜`-algebra equivalence `F ≃ₐ[𝕜] 𝕜` from a
  seminormed `𝕜`-algebra with `‖1‖ = 1` to its base normed field preserves the norm and is an
  isometry.
-/

public section

namespace TauCeti

variable {R : Type*} [SeminormedRing R] [NormedAlgebra ℝ R]

/-- A real normed algebra regarded as a rational normed algebra, by restricting scalars along
`ℚ → ℝ`.

This is not a global instance: algebras such as `ℂ` already carry a `ℚ`-algebra structure
(for example through Mathlib's `normedAlgebraRat`) that is not reducibly defeq to this one, so
a global instance would create a diamond. Enable it where needed with
`attribute [local instance] TauCeti.normedAlgebraRatOfReal`. -/
noncomputable abbrev normedAlgebraRatOfReal : NormedAlgebra ℚ R :=
  .restrictScalars ℚ ℝ R

end TauCeti

namespace AlgEquiv

variable {𝕜 F : Type*} [NormedField 𝕜] [SeminormedRing F] [NormOneClass F] [NormedAlgebra 𝕜 F]

/-- Every `𝕜`-algebra equivalence from a seminormed `𝕜`-algebra `F` with `‖1‖ = 1` to its base
normed field `𝕜` preserves the norm. -/
@[simp]
theorem norm_map (e : F ≃ₐ[𝕜] 𝕜) (x : F) : ‖e x‖ = ‖x‖ := by
  have hx : algebraMap 𝕜 F (e x) = x := by
    rw [← e.symm.commutes (e x), Algebra.algebraMap_self_apply, e.symm_apply_apply]
  nth_rw 2 [← hx]
  rw [norm_algebraMap']

/-- Every `𝕜`-algebra equivalence from a seminormed `𝕜`-algebra `F` with `‖1‖ = 1` to its base
normed field `𝕜` is an isometry. -/
theorem isometry (e : F ≃ₐ[𝕜] 𝕜) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_map

end AlgEquiv
