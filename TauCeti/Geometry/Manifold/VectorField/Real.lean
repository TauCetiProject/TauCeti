/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorField.Constant
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
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
    (contMDiff_vectorSpace_iff_contDiff.mp u.contMDiff).contMDiff.congr
      (fun x ↦ NormedSpace.fromTangentSpace_apply x (u x))⟩

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
  have hcoe (w : Cₛ^n⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) :
      (realFieldCoord w : ℝ → ℝ) = ⇑w :=
    funext fun y ↦ (realFieldCoord_apply w y).trans (NormedSpace.fromTangentSpace_apply y (w y))
  have hmlie : NormedSpace.fromTangentSpace x (VectorField.mlieBracket 𝓘(ℝ, ℝ) u v x) =
      fderiv ℝ (realFieldCoord v) x (realFieldCoord u x) -
        fderiv ℝ (realFieldCoord u) x (realFieldCoord v x) := by
    calc NormedSpace.fromTangentSpace x (VectorField.mlieBracket 𝓘(ℝ, ℝ) u v x)
        = VectorField.lieBracket ℝ (⇑u) (⇑v) x :=
          (NormedSpace.fromTangentSpace_apply x _).trans
            (congrFun VectorField.mlieBracket_eq_lieBracket x)
      _ = fderiv ℝ (⇑v) x (u x) - fderiv ℝ (⇑u) x (v x) :=
          congrFun VectorField.lieBracket_eq x
      _ = fderiv ℝ (realFieldCoord v) x (realFieldCoord u x) -
            fderiv ℝ (realFieldCoord u) x (realFieldCoord v x) := by
          rw [← hcoe u, ← hcoe v]
  have hlin (f : ℝ → ℝ) (c : ℝ) : fderiv ℝ f x c = c * fderiv ℝ f x 1 := by
    simpa only [smul_eq_mul, mul_one] using (fderiv ℝ f x).map_smul c 1
  apply (NormedSpace.fromTangentSpace x).injective
  rw [hmlie, hlin, hlin]
  simp
end TauCeti
