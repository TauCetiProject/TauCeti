/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Applying `C^n` families of continuous multilinear maps

Let `g : M → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂` be a `C^n` family of continuous
multilinear maps on a manifold `M`, and `f i : M → F₁` be `C^n` families of vectors. Then
`x ↦ g x (fun i ↦ f i x)` is `C^n`, since evaluation of continuous multilinear maps is a
continuous polynomial, hence smooth, function of the map and its arguments.

These are the multilinear counterparts of Mathlib's `ContMDiffWithinAt.clm_apply` and
`ContMDiffWithinAt.continuousAlternatingMap_apply`; the versions for sections of the bundle of
continuous multilinear maps are `ContMDiffWithinAt.continuousMultilinearMap_apply_of_inCoordinates`
and `ContMDiffWithinAt.continuousMultilinearMap_bundle_apply`.
-/

public section

open Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {ι : Type*} [Fintype ι]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {g : M → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂} {f : ι → M → F₁}
  {s : Set M} {x : M}

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family, within a set at a point. -/
theorem ContMDiffWithinAt.continuousMultilinearMap_apply
    (hg : ContMDiffWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n g s x)
    (hf : ∀ i, ContMDiffWithinAt IM 𝓘(𝕜, F₁) n (f i) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) s x :=
  ContDiffWithinAt.comp_contMDiffWithinAt (t := univ)
    (g := fun p : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ × (ι → F₁) ↦ p.1 p.2)
    (f := fun x : M ↦ (g x, (f · x)))
    ContinuousMultilinearMap.cpolynomialAt_apply.contDiffAt.contDiffWithinAt
    (hg.prodMk_space (contMDiffWithinAt_pi_module_iff.mpr hf)) (by simp)

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family, at a point. -/
nonrec theorem ContMDiffAt.continuousMultilinearMap_apply
    (hg : ContMDiffAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n g x)
    (hf : ∀ i, ContMDiffAt IM 𝓘(𝕜, F₁) n (f i) x) :
    ContMDiffAt IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) x :=
  ContMDiffWithinAt.continuousMultilinearMap_apply hg hf

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family, on a set. -/
theorem ContMDiffOn.continuousMultilinearMap_apply
    (hg : ContMDiffOn IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n g s)
    (hf : ∀ i, ContMDiffOn IM 𝓘(𝕜, F₁) n (f i) s) :
    ContMDiffOn IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) s :=
  fun x hx ↦ (hg x hx).continuousMultilinearMap_apply fun i ↦ hf i x hx

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family. -/
theorem ContMDiff.continuousMultilinearMap_apply
    (hg : ContMDiff IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n g)
    (hf : ∀ i, ContMDiff IM 𝓘(𝕜, F₁) n (f i)) :
    ContMDiff IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) :=
  fun x ↦ (hg x).continuousMultilinearMap_apply fun i ↦ hf i x
