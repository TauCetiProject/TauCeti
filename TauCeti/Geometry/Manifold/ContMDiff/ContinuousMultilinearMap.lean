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

Let `g : M → ContinuousMultilinearMap 𝕜 F₁ F₂` be a `C^n` family of continuous multilinear maps
on a manifold `M`, and `f i : M → F₁ i` be `C^n` families of vectors. Then
`x ↦ g x (fun i ↦ f i x)` is `C^n`, since evaluation of continuous multilinear maps is a
continuous polynomial, hence smooth, function of the map and its arguments.

These are the multilinear counterparts of Mathlib's `ContMDiffWithinAt.clm_apply` and
`ContMDiffWithinAt.continuousAlternatingMap_apply`; the versions for sections of the bundle of
continuous multilinear maps are `ContMDiffWithinAt.continuousMultilinearMap_apply_of_inCoordinates`
and `ContMDiffWithinAt.continuousMultilinearMap_bundle_apply`.

Precomposing each variable of continuous multilinear maps with a `C^n` family of continuous linear
maps (`ContMDiffWithinAt.compContinuousLinearMapL`), and postcomposing them with a `C^n` family of
continuous linear maps (`ContMDiffWithinAt.compContinuousMultilinearMapL`), are `C^n` operations.
These are the multilinear counterparts of Mathlib's `ContMDiffWithinAt.compContinuousLinearMapCLM`
and `ContMDiffWithinAt.compContinuousAlternatingMapCLM`, and give the smoothness of the coordinate
changes of the bundle of continuous multilinear maps.
-/

public section

open Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {ι : Type*} [Fintype ι]
  {F₁ : ι → Type*} [∀ i, NormedAddCommGroup (F₁ i)] [∀ i, NormedSpace 𝕜 (F₁ i)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {g : M → ContinuousMultilinearMap 𝕜 F₁ F₂} {f : ∀ i, M → F₁ i}
  {s : Set M} {x : M}

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family, within a set at a point. -/
theorem ContMDiffWithinAt.continuousMultilinearMap_apply
    (hg : ContMDiffWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) n g s x)
    (hf : ∀ i, ContMDiffWithinAt IM 𝓘(𝕜, F₁ i) n (f i) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) s x :=
  ContDiffWithinAt.comp_contMDiffWithinAt (t := univ)
    (g := fun p : ContinuousMultilinearMap 𝕜 F₁ F₂ × (∀ i, F₁ i) ↦ p.1 p.2)
    (f := fun x : M ↦ (g x, (f · x)))
    ContinuousMultilinearMap.cpolynomialAt_apply.contDiffAt.contDiffWithinAt
    (hg.prodMk_space (contMDiffWithinAt_pi_module_iff.mpr hf)) (by simp)

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family, at a point. -/
nonrec theorem ContMDiffAt.continuousMultilinearMap_apply
    (hg : ContMDiffAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) n g x)
    (hf : ∀ i, ContMDiffAt IM 𝓘(𝕜, F₁ i) n (f i) x) :
    ContMDiffAt IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) x :=
  ContMDiffWithinAt.continuousMultilinearMap_apply hg hf

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family, on a set. -/
theorem ContMDiffOn.continuousMultilinearMap_apply
    (hg : ContMDiffOn IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) n g s)
    (hf : ∀ i, ContMDiffOn IM 𝓘(𝕜, F₁ i) n (f i) s) :
    ContMDiffOn IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) s :=
  fun x hx ↦ (hg x hx).continuousMultilinearMap_apply fun i ↦ hf i x hx

/-- Applying a `C^n` family of continuous multilinear maps to `C^n` families of vectors gives a
`C^n` family. -/
theorem ContMDiff.continuousMultilinearMap_apply
    (hg : ContMDiff IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂) n g)
    (hf : ∀ i, ContMDiff IM 𝓘(𝕜, F₁ i) n (f i)) :
    ContMDiff IM 𝓘(𝕜, F₂) n (fun x ↦ g x (fun i ↦ f i x)) :=
  fun x ↦ (hg x).continuousMultilinearMap_apply fun i ↦ hf i x

section Comp

variable {E E' : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Precomposing each variable of continuous multilinear maps with a `C^n` family of continuous
linear maps is `C^n`, within a set at a point. -/
theorem ContMDiffWithinAt.compContinuousLinearMapL {L : ∀ i, M → E i →L[𝕜] E' i}
    (hL : ∀ i, ContMDiffWithinAt IM 𝓘(𝕜, E i →L[𝕜] E' i) n (L i) s x) :
    ContMDiffWithinAt IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 E' F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 E F₂) n
      (fun y ↦ ContinuousMultilinearMap.compContinuousLinearMapL (F := F₂) fun i ↦ L i y) s x :=
  (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 E E' F₂).contDiff
    |>.comp_contMDiffWithinAt (contMDiffWithinAt_pi_module_iff.mpr hL)

/-- Precomposing each variable of continuous multilinear maps with a `C^n` family of continuous
linear maps is `C^n`, at a point. -/
nonrec theorem ContMDiffAt.compContinuousLinearMapL {L : ∀ i, M → E i →L[𝕜] E' i}
    (hL : ∀ i, ContMDiffAt IM 𝓘(𝕜, E i →L[𝕜] E' i) n (L i) x) :
    ContMDiffAt IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 E' F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 E F₂) n
      (fun y ↦ ContinuousMultilinearMap.compContinuousLinearMapL (F := F₂) fun i ↦ L i y) x :=
  ContMDiffWithinAt.compContinuousLinearMapL hL

/-- Precomposing each variable of continuous multilinear maps with a `C^n` family of continuous
linear maps is `C^n`, on a set. -/
theorem ContMDiffOn.compContinuousLinearMapL {L : ∀ i, M → E i →L[𝕜] E' i}
    (hL : ∀ i, ContMDiffOn IM 𝓘(𝕜, E i →L[𝕜] E' i) n (L i) s) :
    ContMDiffOn IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 E' F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 E F₂) n
      (fun y ↦ ContinuousMultilinearMap.compContinuousLinearMapL (F := F₂) fun i ↦ L i y) s :=
  fun x hx ↦ ContMDiffWithinAt.compContinuousLinearMapL fun i ↦ hL i x hx

/-- Precomposing each variable of continuous multilinear maps with a `C^n` family of continuous
linear maps is `C^n`. -/
theorem ContMDiff.compContinuousLinearMapL {L : ∀ i, M → E i →L[𝕜] E' i}
    (hL : ∀ i, ContMDiff IM 𝓘(𝕜, E i →L[𝕜] E' i) n (L i)) :
    ContMDiff IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 E' F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 E F₂) n
      (fun y ↦ ContinuousMultilinearMap.compContinuousLinearMapL (F := F₂) fun i ↦ L i y) :=
  fun x ↦ ContMDiffAt.compContinuousLinearMapL fun i ↦ hL i x

/-- Postcomposing continuous multilinear maps with a `C^n` family of continuous linear maps is
`C^n`, within a set at a point. -/
theorem ContMDiffWithinAt.compContinuousMultilinearMapL {L : M → F₂ →L[𝕜] G}
    (hL : ContMDiffWithinAt IM 𝓘(𝕜, F₂ →L[𝕜] G) n L s x) :
    ContMDiffWithinAt IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 F₁ G) n
      (fun y ↦ ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 F₁ F₂ G (L y)) s x :=
  ContDiff.comp_contMDiffWithinAt
    (g := ⇑(ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 F₁ F₂ G))
    (ContinuousLinearMap.contDiff _) hL

/-- Postcomposing continuous multilinear maps with a `C^n` family of continuous linear maps is
`C^n`, at a point. -/
nonrec theorem ContMDiffAt.compContinuousMultilinearMapL {L : M → F₂ →L[𝕜] G}
    (hL : ContMDiffAt IM 𝓘(𝕜, F₂ →L[𝕜] G) n L x) :
    ContMDiffAt IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 F₁ G) n
      (fun y ↦ ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 F₁ F₂ G (L y)) x :=
  ContMDiffWithinAt.compContinuousMultilinearMapL hL

/-- Postcomposing continuous multilinear maps with a `C^n` family of continuous linear maps is
`C^n`, on a set. -/
theorem ContMDiffOn.compContinuousMultilinearMapL {L : M → F₂ →L[𝕜] G}
    (hL : ContMDiffOn IM 𝓘(𝕜, F₂ →L[𝕜] G) n L s) :
    ContMDiffOn IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 F₁ G) n
      (fun y ↦ ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 F₁ F₂ G (L y)) s :=
  fun x hx ↦ (hL x hx).compContinuousMultilinearMapL

/-- Postcomposing continuous multilinear maps with a `C^n` family of continuous linear maps is
`C^n`. -/
theorem ContMDiff.compContinuousMultilinearMapL {L : M → F₂ →L[𝕜] G}
    (hL : ContMDiff IM 𝓘(𝕜, F₂ →L[𝕜] G) n L) :
    ContMDiff IM
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 F₁ F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 F₁ G) n
      (fun y ↦ ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 F₁ F₂ G (L y)) :=
  fun x ↦ (hL x).compContinuousMultilinearMapL

end Comp
