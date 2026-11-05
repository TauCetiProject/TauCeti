/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Differentiation along a smooth vector field

Differentiating smooth scalar functions along a smooth vector field `X` on a smooth manifold is a
derivation of the ring `C^∞(M, 𝕜)`: `f ↦ (x ↦ df_x(X_x))`. No finite-dimensionality, separation
or boundary hypothesis is needed.

## Main declarations

* `ContMDiffSection.toDerivation`: differentiation along a smooth section of the tangent bundle,
  as a derivation of `C^∞(M, 𝕜)`.
* `ContMDiffSection.toDerivation_apply`: its evaluation `(X.toDerivation f)(x) = df_x(X_x)`.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ContMDiffSection

/-- Differentiation along a smooth vector field `X`: the derivation of `C^∞(M, 𝕜)` sending `f` to
`x ↦ df_x(X_x)`. -/
def toDerivation (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ :=
  -- In each proof below, both sides evaluated at `x` unfold definitionally to the corresponding
  -- identity for `mvfderiv` applied to `X x`.
  Derivation.mk'
    { toFun f := ⟨fun x ↦ mvfderiv I f x (X x),
        (f.contMDiff.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp X.contMDiff⟩
      map_add' f g := by
        ext x
        exact congr($(mvfderiv_add ((f.contMDiff x).mdifferentiableAt (by simp))
          ((g.contMDiff x).mdifferentiableAt (by simp))) (X x))
      map_smul' c f := by
        ext x
        exact congr($(TauCeti.mvfderiv_const_smul_field (f : M → 𝕜) x c) (X x)) }
    fun f g ↦ by
      ext x
      exact congr($(mvfderiv_mul ((f.contMDiff x).mdifferentiableAt (by simp))
        ((g.contMDiff x).mdifferentiableAt (by simp))) (X x))

/-- The derivation of a smooth vector field `X` differentiates along `X`. -/
@[simp]
theorem toDerivation_apply (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; 𝕜⟯) (x : M) :
    X.toDerivation f x = mvfderiv I f x (X x) :=
  (rfl)

end ContMDiffSection

end
