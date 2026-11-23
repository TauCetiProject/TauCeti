/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorField.Constant
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Vector fields on the real line

Scalar coordinate functions `TauCeti.realFieldCoord` for `C^n` vector fields on `ℝ` and the
pointwise Lie bracket formula `TauCeti.mlieBracket_realField_apply`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti
/-- Scalar coordinate function of a `C^n` vector field on `ℝ`, identifying `T_x ℝ` with `ℝ`. -/
noncomputable def realFieldCoord {n : ℕ∞ω}
    (u : Cₛ^n⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) : C^n⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯ :=
  ⟨fun x ↦ NormedSpace.fromTangentSpace x (u x),
    (contMDiff_vectorSpace_iff_contDiff.mp u.contMDiff).contMDiff⟩

/-- Under `NormedSpace.fromTangentSpace`, `realFieldCoord u` evaluates to `u x` at `x`. -/
@[simp] theorem realFieldCoord_apply {n : ℕ∞ω}
    (u : Cₛ^n⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) (x : ℝ) :
    realFieldCoord u x = NormedSpace.fromTangentSpace x (u x) := (rfl)

/-- Every `C^n` vector field on `ℝ` is its scalar coordinate times `constVectorFieldSection n 1`. -/
theorem eq_realFieldCoord_smul {n : ℕ∞ω}
    (u : Cₛ^n⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) :
    u = realFieldCoord u • constVectorFieldSection n (1 : ℝ) := by
  ext x; apply (NormedSpace.fromTangentSpace x).injective; simp [ContMDiffSection.smul_apply]

/-- Taking the scalar coordinate of `f • constVectorFieldSection n 1` recovers `f`. -/
@[simp] theorem realFieldCoord_smul_constVectorFieldSection {n : ℕ∞ω} (f : C^n⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) :
    realFieldCoord (f • constVectorFieldSection n (1 : ℝ)) = f := by
  ext x; simp [ContMDiffSection.smul_apply]

/-- Pointwise Lie bracket formula for `C^n` vector fields on `ℝ`:
`[f ∂_x, g ∂_x]_x = (f(x) g'(x) - g(x) f'(x)) ∂_x`. -/
theorem mlieBracket_realField_apply {n : ℕ∞ω}
    (u v : Cₛ^n⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) (x : ℝ) :
    VectorField.mlieBracket 𝓘(ℝ, ℝ) u v x = (realFieldCoord u x * fderiv ℝ (realFieldCoord v) x 1 -
      realFieldCoord v x * fderiv ℝ (realFieldCoord u) x 1) •
        constVectorFieldSection n (1 : ℝ) x := by
  rw [VectorField.mlieBracket_eq_lieBracket]; apply (NormedSpace.fromTangentSpace x).injective
  simp only [map_smul, constVectorFieldSection_apply, ContinuousLinearEquiv.apply_symm_apply,
    smul_eq_mul, mul_one]; change fderiv ℝ (realFieldCoord v) x (realFieldCoord u x) -
    fderiv ℝ (realFieldCoord u) x (realFieldCoord v x) = _
  rw [← mul_one (realFieldCoord u x), ← mul_one (realFieldCoord v x), ← smul_eq_mul _ 1,
    ← smul_eq_mul _ 1, map_smul, map_smul]; simp only [smul_eq_mul, mul_one]
end TauCeti
