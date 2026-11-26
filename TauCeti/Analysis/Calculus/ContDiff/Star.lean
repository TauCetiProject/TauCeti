/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Smooth maps and the star operation

The inclusion of the self-adjoint elements into a normed star module over a field with trivial
star is smooth at every order. This lets smooth ambient maps restrict to the self-adjoint
space, for example when constructing exponential coordinates on Hermitian matrices.
Over the same scalar field, taking the star of a smooth family preserves smoothness.
-/

public section

open scoped ContDiff

namespace ContDiff

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {k : ℕ∞ω}

/-- Taking the star of a smooth family preserves smoothness over scalars with trivial star. -/
@[fun_prop]
protected theorem star {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F]
    [StarModule 𝕜 F] [ContinuousStar F] {f : E → F} (hf : ContDiff 𝕜 k f) :
    ContDiff 𝕜 k (fun x ↦ star (f x)) := by
  simpa only [Function.comp_def, starL'_apply] using
    (starL' 𝕜 : F ≃L[𝕜] F).contDiff.comp hf

/-- Multiplying a smooth family on the left by a smooth frame and on the right by the
star of that frame preserves smoothness. -/
theorem mul_mul_star {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [StarAddMonoid A]
    [StarModule 𝕜 A] [ContinuousStar A] {F D : E → A}
    (hF : ContDiff 𝕜 k F) (hD : ContDiff 𝕜 k D) :
    ContDiff 𝕜 k (fun x ↦ F x * D x * star (F x)) :=
  (hF.mul hD).mul hF.star

end ContDiff

/-- The inclusion of the self-adjoint elements into a normed star module is smooth at every
order over a scalar field with trivial star. -/
theorem selfAdjoint.contDiff_subtype_val (𝕜 : Type*) {A : Type*}
    [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
    [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A] [StarModule 𝕜 A]
    {k : ℕ∞ω} : ContDiff 𝕜 k (Subtype.val : selfAdjoint A → A) :=
  -- The subgroup and submodule have the same carrier and induced normed structure.
  (selfAdjoint.submodule 𝕜 A).subtypeL.contDiff
