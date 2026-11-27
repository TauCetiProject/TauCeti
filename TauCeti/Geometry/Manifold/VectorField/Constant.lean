/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Constant vector fields on a normed model space

Defines the constant vector field `TauCeti.constVectorField` on a real normed space `E`, its
smoothness, differentiability, vanishing Lie bracket (`TauCeti.mlieBracket_constVectorField`), and
the bundled `C^n` section `TauCeti.constVectorFieldSection`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constant vector field with value `v` on the model space. -/
noncomputable def constVectorField (v : E) : (z : E) → TangentSpace 𝓘(ℝ, E) z := fun _ ↦ v
/-- Under `NormedSpace.fromTangentSpace`, `constVectorField` evaluates to `v`. -/
theorem constVectorField_apply (v z : E) :
    constVectorField v z = (NormedSpace.fromTangentSpace z).symm v := (rfl)
/-- The constant vector field with value `v` is the constant function `v`, each tangent space of
`E` being `E` itself. -/
theorem constVectorField_eq (v : E) : constVectorField v = fun _ ↦ v := (rfl)
/-- The section `z ↦ ⟨z, v⟩` of `T E` is smooth (bare-pair form). -/
theorem contMDiff_tangentBundle_mk_const (v : E) {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n (fun z ↦ (⟨z, v⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
  contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
/-- The constant vector field is smooth as a map on the model space. -/
theorem contDiff_constVectorField (v : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (constVectorField v) := contDiff_const
/-- The constant vector field is smooth. -/
theorem contMDiff_constVectorField (v : E) {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n
      (fun z ↦ (⟨z, constVectorField v z⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
  contMDiff_tangentBundle_mk_const v
/-- The constant vector field is differentiable. -/
theorem mdifferentiable_constVectorField (v : E) :
    MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun z ↦ (⟨z, constVectorField v z⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
  (contMDiff_constVectorField v (n := 1)).mdifferentiable one_ne_zero
/-- Two constant vector fields on the model space have zero Lie bracket. -/
@[simp] theorem mlieBracket_constVectorField (v w : E) :
    VectorField.mlieBracket 𝓘(ℝ, E) (constVectorField v) (constVectorField w) = 0 :=
  funext (VectorField.mlieBracket_const_model_space v w)
/-- The constant vector field with value `v` on the model space, bundled as a `C^n` section. -/
noncomputable def constVectorFieldSection (n : ℕ∞ω) (v : E) :
    Cₛ^n⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : E → Type _)⟯ :=
  ⟨constVectorField v, contMDiff_constVectorField v⟩
/-- Under `NormedSpace.fromTangentSpace`, `constVectorFieldSection` evaluates to `v`. -/
@[simp] theorem constVectorFieldSection_apply {n : ℕ∞ω} (v z : E) :
    constVectorFieldSection n v z = (NormedSpace.fromTangentSpace z).symm v := (rfl)
end TauCeti
