/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Smoothness of continuous-linear-map coproducts on manifolds

Two families of continuous linear maps `g : M → F₁ →L[𝕜] F₃` and `f : M → F₂ →L[𝕜] F₃` on a
manifold combine into the family `x ↦ (g x).coprod (f x)` on `F₁ × F₂` by composing `(g, f)` with
the continuous linear equivalence `ContinuousLinearMap.coprodEquivL`. Consequently, `C^n`
regularity is preserved at a point within a set, at a point, on a set, and globally.

## Main results

* `ContMDiffWithinAt.clm_coprod`, `ContMDiffAt.clm_coprod`, `ContMDiffOn.clm_coprod`,
  `ContMDiff.clm_coprod`: `C^n` regularity of `x ↦ (g x).coprod (f x)`.

## Formal sources

These lemmas parallel `ContMDiffWithinAt.clm_prodMap` in
`Mathlib.Geometry.Manifold.ContMDiff.NormedSpace`, by Sébastien Gouëzel and Floris van Doorn,
replacing `ContinuousLinearMap.prodMapL` by `ContinuousLinearMap.coprodEquivL`.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {s : Set M} {x : M} {n : ℕ∞ω}

/-- Taking the coproduct `(g x).coprod (f x)` of two operator families that are `C^n` within `s` at
`x` yields an operator family that is `C^n` within `s` at `x`. -/
theorem ContMDiffWithinAt.clm_coprod {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₃}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ × F₂) →L[𝕜] F₃) n (fun x ↦ (g x).coprod (f x)) s x :=
  (ContinuousLinearMap.coprodEquivL (𝕜 := 𝕜) (E := F₁) (F := F₂) (G := F₃)
    𝕜).contDiff.comp_contMDiffWithinAt (hg.prodMk_space hf)

/-- Taking the coproduct `(g x).coprod (f x)` of two operator families that are `C^n` at `x` yields
an operator family that is `C^n` at `x`. -/
nonrec theorem ContMDiffAt.clm_coprod {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₃}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x)
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ × F₂) →L[𝕜] F₃) n (fun x ↦ (g x).coprod (f x)) x :=
  hg.clm_coprod hf

/-- Taking the coproduct `(g x).coprod (f x)` of two operator families that are `C^n` on `s` yields
an operator family that is `C^n` on `s`. -/
theorem ContMDiffOn.clm_coprod {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₃}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s)
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ × F₂) →L[𝕜] F₃) n (fun x ↦ (g x).coprod (f x)) s :=
  fun x hx ↦ (hg x hx).clm_coprod (hf x hx)

/-- Taking the coproduct `(g x).coprod (f x)` of two `C^n` operator families yields a `C^n`
operator family. -/
theorem ContMDiff.clm_coprod {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₃}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g)
    (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f) :
    ContMDiff I 𝓘(𝕜, (F₁ × F₂) →L[𝕜] F₃) n (fun x ↦ (g x).coprod (f x)) :=
  fun x ↦ (hg x).clm_coprod (hf x)

end
