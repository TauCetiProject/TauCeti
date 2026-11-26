/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth inversion of operator families on manifolds

A family of continuous linear equivalences whose underlying operators depend `C^n` on a
manifold parameter has a `C^n` family of inverse operators. These lemmas apply smooth operator
inversion at each equivalence, without requiring a manifold structure on the space of equivalences.

More generally, a family `f : M → F₁ →L[𝕜'] F₂` of continuous linear maps between Banach spaces
over `𝕜'` that is `C^n` over a subfield `𝕜` has `C^n` inverses `y ↦ (f y).inverse` wherever it is
invertible (`ContMDiffWithinAt.clm_inverse`, `ContMDiffOn.clm_inverse`): inversion is `C^n` at
every invertible operator (`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`), also over
`𝕜`. The main example is a family of complex-linear maps on a real manifold.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {A : M → E ≃L[𝕜] F} {n : WithTop ℕ∞} {x : M}

/-- A family of inverse continuous linear equivalences is `C^n` at a point whenever the
forward operators are `C^n` there. -/
theorem ContMDiffAt.continuousLinearEquiv_symm
    (hA : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) n (fun y ↦ (A y : E →L[𝕜] F)) x) :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] E) n (fun y ↦ ((A y).symm : F →L[𝕜] E)) x := by
  have heq : (fun y ↦ ((A y).symm : F →L[𝕜] E)) =
      ContinuousLinearMap.inverse ∘ fun y ↦ (A y : E →L[𝕜] F) := by
    ext1 y
    simp
  rw [heq]
  exact ContDiffAt.comp_contMDiffAt (contDiffAt_map_inverse (A x)) hA

/-- A `C^n` family of continuous linear equivalences has a `C^n` family of inverse operators. -/
theorem ContMDiff.continuousLinearEquiv_symm
    (hA : ContMDiff I 𝓘(𝕜, E →L[𝕜] F) n fun y ↦ (A y : E →L[𝕜] F)) :
    ContMDiff I 𝓘(𝕜, F →L[𝕜] E) n fun y ↦ ((A y).symm : F →L[𝕜] E) :=
  fun y ↦ (hA y).continuousLinearEquiv_symm

section ClmInverse

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜' F₁] [NormedSpace 𝕜 F₁]
  [IsScalarTower 𝕜 𝕜' F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜' F₂] [NormedSpace 𝕜 F₂]
  [IsScalarTower 𝕜 𝕜' F₂] {f : M → F₁ →L[𝕜'] F₂} {s : Set M}

/-- The inverses of an operator family that is `C^n` within `s` at a point where it is invertible
are `C^n` within `s` at that point. -/
theorem ContMDiffWithinAt.clm_inverse [CompleteSpace F₁]
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜'] F₂) n f s x) (hx : (f x).IsInvertible) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜'] F₁) n (fun y ↦ (f y).inverse) s x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜')).restrict_scalars 𝕜).contMDiffAt.comp_contMDiffWithinAt x hf

/-- The inverses of an operator family that is `C^n` on `s` and invertible at every point of `s`
are `C^n` on `s`. -/
theorem ContMDiffOn.clm_inverse [CompleteSpace F₁]
    (hf : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜'] F₂) n f s) (hinv : ∀ y ∈ s, (f y).IsInvertible) :
    ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜'] F₁) n (fun y ↦ (f y).inverse) s :=
  fun y hy ↦ (hf y hy).clm_inverse (hinv y hy)

end ClmInverse
