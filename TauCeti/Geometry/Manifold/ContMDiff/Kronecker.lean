/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Kronecker
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth families of Kronecker products

Kronecker products of `C^r` families of finite-coordinate operators are `C^r`.
These lemmas apply in particular to transition functions and morphisms of tensor-product
vector bundles. They use the continuous bilinear map `ContinuousLinearMap.kroneckerL`,
so no completeness of the scalar field or regularity of the source atlas is needed.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] {r : ℕ∞ω}
  {m n m' n' : ℕ}
  {f : M → (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)}
  {g : M → (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)} {s : Set M} {x : M}

/-- Kronecker products preserve `C^r` regularity within a set at a point. -/
theorem ContMDiffWithinAt.clm_kronecker
    (hf : ContMDiffWithinAt I 𝓘(𝕜, (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) r f s x)
    (hg : ContMDiffWithinAt I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r g s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (f y).kronecker (g y)) s x := by
  simpa only [Function.comp_def, ContinuousLinearMap.kroneckerL_apply] using
    ((ContinuousLinearMap.kroneckerL 𝕜 m n m' n').contMDiffAt.comp_contMDiffWithinAt
      x hf).clm_apply hg

/-- Kronecker products preserve `C^r` regularity at a point. -/
theorem ContMDiffAt.clm_kronecker
    (hf : ContMDiffAt I 𝓘(𝕜, (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) r f x)
    (hg : ContMDiffAt I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r g x) :
    ContMDiffAt I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (f y).kronecker (g y)) x :=
  ContMDiffWithinAt.clm_kronecker hf hg

/-- Kronecker products of operator families that are `C^r` on a set are `C^r` there. -/
theorem ContMDiffOn.clm_kronecker
    (hf : ContMDiffOn I 𝓘(𝕜, (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) r f s)
    (hg : ContMDiffOn I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r g s) :
    ContMDiffOn I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (f y).kronecker (g y)) s :=
  fun y hy ↦ (hf y hy).clm_kronecker (hg y hy)

/-- Kronecker products of `C^r` operator families are `C^r`. -/
theorem ContMDiff.clm_kronecker
    (hf : ContMDiff I 𝓘(𝕜, (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) r f)
    (hg : ContMDiff I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r g) :
    ContMDiff I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (f y).kronecker (g y)) :=
  fun y ↦ (hf y).clm_kronecker (hg y)
