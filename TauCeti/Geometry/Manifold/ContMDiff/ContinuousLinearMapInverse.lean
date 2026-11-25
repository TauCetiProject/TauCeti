/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Inverting `C^n` operator families on manifolds

A family `f : M → F →L[𝕜'] G` of continuous linear maps between Banach spaces over `𝕜'` that is
`C^n` over a subfield `𝕜` has `C^n` inverses `y ↦ (f y).inverse` wherever it is invertible:
inversion is `C^n` at every invertible operator
(`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`), also over `𝕜`, and composing a `C^n`
map with it preserves `C^n` regularity. The main example is a
family of complex-linear maps on a real manifold.

## Main results

* `ContMDiffWithinAt.clm_inverse`, `ContMDiffOn.clm_inverse`: the inverses of a `C^n` operator
  family are `C^n` within a set at an invertible point, and on a set of invertible points.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G]
  {f : M → F →L[𝕜'] G} {s : Set M} {x : M} {n : WithTop ℕ∞}

/-- The inverses of an operator family that is `C^n` within `s` at a point where it is invertible
are `C^n` within `s` at that point. -/
theorem ContMDiffWithinAt.clm_inverse [CompleteSpace F]
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜'] G) n f s x) (hx : (f x).IsInvertible) :
    ContMDiffWithinAt I 𝓘(𝕜, G →L[𝕜'] F) n (fun y ↦ (f y).inverse) s x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜')).restrict_scalars 𝕜).contMDiffAt.comp_contMDiffWithinAt x hf

/-- The inverses of an operator family that is `C^n` on `s` and invertible at every point of `s`
are `C^n` on `s`. -/
theorem ContMDiffOn.clm_inverse [CompleteSpace F]
    (hf : ContMDiffOn I 𝓘(𝕜, F →L[𝕜'] G) n f s) (hinv : ∀ y ∈ s, (f y).IsInvertible) :
    ContMDiffOn I 𝓘(𝕜, G →L[𝕜'] F) n (fun y ↦ (f y).inverse) s :=
  fun y hy ↦ (hf y hy).clm_inverse (hinv y hy)
