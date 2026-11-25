/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Kronecker
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth families of Kronecker products and operator conjugations

Kronecker products of `C^r` families of finite-coordinate operators are `C^r`, and so are
the operator conjugations `ContinuousLinearMap.homCoordConj S R` of two `C^r` families.
These lemmas apply in particular to transition functions and morphisms of tensor-product
and Hom vector bundles. They use the continuous bilinear map `ContinuousLinearMap.kroneckerL`
and, for conjugations, the coordinates `ContinuousLinearEquiv.finProdCLM` together with pre- and
postcomposition, so no completeness of the scalar field or regularity of the source atlas is
needed.
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

section HomCoordConj

variable {S : M → (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)} {R : M → (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)}

/-- Operator conjugations of two families of operators preserve `C^r` regularity within a set at
a point. -/
theorem ContMDiffWithinAt.clm_homCoordConj
    (hS : ContMDiffWithinAt I 𝓘(𝕜, (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) r S s x)
    (hR : ContMDiffWithinAt I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r R s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (S y).homCoordConj (R y)) s x := by
  -- In the coordinates `finProdCLM`, conjugation is `T ↦ R ∘ T ∘ S`.
  let φ := ContinuousLinearEquiv.finProdCLM 𝕜 m n
  let ψ := ContinuousLinearEquiv.finProdCLM 𝕜 m' n'
  have h := (contMDiffWithinAt_const (c := ψ.symm.toContinuousLinearMap)).clm_comp
    (((hR.clm_postcomp (F₁ := Fin m' → 𝕜)).clm_comp
      (hS.clm_precomp (F₃ := Fin n → 𝕜))).clm_comp
        (contMDiffWithinAt_const (c := φ.toContinuousLinearMap)))
  refine h.congr (fun y _ ↦ ?_) ?_ <;>
  · refine ContinuousLinearMap.ext fun v ↦ ψ.injective ?_
    simp [φ, ψ]

/-- Operator conjugations of two families of operators preserve `C^r` regularity at a point. -/
theorem ContMDiffAt.clm_homCoordConj
    (hS : ContMDiffAt I 𝓘(𝕜, (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) r S x)
    (hR : ContMDiffAt I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r R x) :
    ContMDiffAt I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (S y).homCoordConj (R y)) x :=
  ContMDiffWithinAt.clm_homCoordConj hS hR

/-- Operator conjugations of two families of operators that are `C^r` on a set are `C^r`
there. -/
theorem ContMDiffOn.clm_homCoordConj
    (hS : ContMDiffOn I 𝓘(𝕜, (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) r S s)
    (hR : ContMDiffOn I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r R s) :
    ContMDiffOn I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (S y).homCoordConj (R y)) s :=
  fun y hy ↦ (hS y hy).clm_homCoordConj (hR y hy)

/-- Operator conjugations of two `C^r` families of operators are `C^r`. -/
theorem ContMDiff.clm_homCoordConj
    (hS : ContMDiff I 𝓘(𝕜, (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) r S)
    (hR : ContMDiff I 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) r R) :
    ContMDiff I 𝓘(𝕜, (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜)) r
      (fun y ↦ (S y).homCoordConj (R y)) :=
  fun y ↦ (hS y).clm_homCoordConj (hR y)

end HomCoordConj
