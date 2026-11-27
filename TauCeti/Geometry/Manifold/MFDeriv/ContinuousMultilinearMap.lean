/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Applying differentiable families of continuous multilinear maps

Let `g : M → ContinuousMultilinearMap 𝕜 F₁ F₂` be a differentiable family of continuous
multilinear maps on a manifold `M`, and `f i : M → F₁ i` be differentiable families of vectors.
Then `x ↦ g x (fun i ↦ f i x)` is differentiable, since evaluation of continuous multilinear maps
is a continuous polynomial, hence differentiable, function of the map and its arguments.

These are the multilinear counterparts of Mathlib's `MDifferentiableWithinAt.clm_apply` and
`MDifferentiableWithinAt.continuousAlternatingMap_apply`; the versions for sections of the bundle
of continuous multilinear maps are
`MDifferentiableWithinAt.continuousMultilinearMap_apply_of_inCoordinates` and
`MDifferentiableWithinAt.continuousMultilinearMap_bundle_apply`.
-/

public section

open Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {ι : Type*} [Fintype ι]
  {F₁ : ι → Type*} [∀ i, NormedAddCommGroup (F₁ i)] [∀ i, NormedSpace 𝕜 (F₁ i)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {g : M → ContinuousMultilinearMap 𝕜 F₁ F₂} {f : ∀ i, M → F₁ i}
  {s : Set M} {x : M}

/-- Applying a differentiable family of continuous multilinear maps to differentiable families of
vectors gives a differentiable family, within a set at a point. -/
theorem MDifferentiableWithinAt.continuousMultilinearMap_apply
    (hg : MDifferentiableWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) g s x)
    (hf : ∀ i, MDifferentiableWithinAt IM 𝓘(𝕜, F₁ i) (f i) s x) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F₂) (fun x ↦ g x (fun i ↦ f i x)) s x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun p : ContinuousMultilinearMap 𝕜 F₁ F₂ × (∀ i, F₁ i) ↦ p.1 p.2)
    (f := fun x : M ↦ (g x, fun i ↦ f i x))
    (ContinuousMultilinearMap.cpolynomialAt_apply.contDiffAt.differentiableWithinAt one_ne_zero)
    (hg.prodMk_space (mdifferentiableWithinAt_pi_space.mpr hf)) (by simp)

/-- Applying a differentiable family of continuous multilinear maps to differentiable families of
vectors gives a differentiable family, at a point. -/
nonrec theorem MDifferentiableAt.continuousMultilinearMap_apply
    (hg : MDifferentiableAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) g x)
    (hf : ∀ i, MDifferentiableAt IM 𝓘(𝕜, F₁ i) (f i) x) :
    MDifferentiableAt IM 𝓘(𝕜, F₂) (fun x ↦ g x (fun i ↦ f i x)) x :=
  MDifferentiableWithinAt.continuousMultilinearMap_apply hg hf

/-- Applying a differentiable family of continuous multilinear maps to differentiable families of
vectors gives a differentiable family, on a set. -/
theorem MDifferentiableOn.continuousMultilinearMap_apply
    (hg : MDifferentiableOn IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) g s)
    (hf : ∀ i, MDifferentiableOn IM 𝓘(𝕜, F₁ i) (f i) s) :
    MDifferentiableOn IM 𝓘(𝕜, F₂) (fun x ↦ g x (fun i ↦ f i x)) s :=
  fun x hx ↦ (hg x hx).continuousMultilinearMap_apply fun i ↦ hf i x hx

/-- Applying a differentiable family of continuous multilinear maps to differentiable families of
vectors gives a differentiable family. -/
theorem MDifferentiable.continuousMultilinearMap_apply
    (hg : MDifferentiable IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) g)
    (hf : ∀ i, MDifferentiable IM 𝓘(𝕜, F₁ i) (f i)) :
    MDifferentiable IM 𝓘(𝕜, F₂) (fun x ↦ g x (fun i ↦ f i x)) :=
  fun x ↦ (hg x).continuousMultilinearMap_apply fun i ↦ hf i x
