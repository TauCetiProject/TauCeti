/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Derivatives under local and linear equivalences

Mathlib's `OpenPartialHomeomorph.hasFDerivAt_symm` computes the derivative of the inverse from an
invertible derivative of the map. Without assuming that invertibility, this file records that when
both the map and its inverse are differentiable at corresponding points, their derivatives compose
to the identity. It does so for open partial homeomorphisms, and for a map `Φ` differentiable on an
open set `U` and mapping it into an open set `V`, with an inverse `Ψ` differentiable on `V`
(`Φ ∘ Ψ = id` on `V` and `Ψ ∘ Φ = id` on `U`).

## Main results

* `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`: the derivative of the inverse is a left inverse
  of the derivative.
* `OpenPartialHomeomorph.fderiv_comp_fderiv_symm`: the derivative of the inverse is a right
  inverse of the derivative.
* `OpenPartialHomeomorph.fderiv_symm_apply_fderiv_apply`,
  `OpenPartialHomeomorph.fderiv_apply_fderiv_symm_apply`: the same identities evaluated at a
  vector.
* `TauCeti.fderiv_comp_fderiv_eq_id_of_invOn`: `DΦ(y) ∘ DΨ(Φ y) = id`.
* `ContinuousLinearEquiv.image_vanishingFDeriv_comp`: precomposition by a continuous linear
  equivalence preserves the image of the vanishing-derivative locus.

Precomposition by a continuous linear equivalence preserves the image of the vanishing-derivative
locus, with no differentiability premise. This follows the totalized derivative calculation in
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Basic.lean`.
-/

public section

open Filter Set TopologicalSpace
open scoped Topology

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the inverse of an open partial homeomorphism at a point of its target is a
left inverse of the derivative at the corresponding point of its source. -/
theorem fderiv_symm_comp_fderiv (e : OpenPartialHomeomorph E F) {p : F} (hp : p ∈ e.target)
    (hd : DifferentiableAt 𝕜 e (e.symm p)) (hds : DifferentiableAt 𝕜 e.symm p) :
    (fderiv 𝕜 e.symm p).comp (fderiv 𝕜 e (e.symm p)) = ContinuousLinearMap.id 𝕜 E := by
  have hds' : HasFDerivAt e.symm (fderiv 𝕜 e.symm p) (e (e.symm p)) := by
    rw [e.right_inv hp]
    exact hds.hasFDerivAt
  refine (hds'.comp _ hd.hasFDerivAt).unique ((hasFDerivAt_id _).congr_of_eventuallyEq ?_)
  exact eventually_of_mem (e.open_source.mem_nhds (e.map_target hp)) fun r hr ↦ e.left_inv hr

/-- The derivative of the inverse of an open partial homeomorphism at a point of its target is a
right inverse of the derivative at the corresponding point of its source. -/
theorem fderiv_comp_fderiv_symm (e : OpenPartialHomeomorph E F) {p : F} (hp : p ∈ e.target)
    (hd : DifferentiableAt 𝕜 e (e.symm p)) (hds : DifferentiableAt 𝕜 e.symm p) :
    (fderiv 𝕜 e (e.symm p)).comp (fderiv 𝕜 e.symm p) = ContinuousLinearMap.id 𝕜 F :=
  (hd.hasFDerivAt.comp p hds.hasFDerivAt).unique
    ((hasFDerivAt_id p).congr_of_eventuallyEq
      (eventually_of_mem (e.open_target.mem_nhds hp) fun _ hr ↦ e.right_inv hr))

/-- Pointwise form of `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`. -/
theorem fderiv_symm_apply_fderiv_apply (e : OpenPartialHomeomorph E F) {p : F}
    (hp : p ∈ e.target) (hd : DifferentiableAt 𝕜 e (e.symm p))
    (hds : DifferentiableAt 𝕜 e.symm p) (v : E) :
    fderiv 𝕜 e.symm p (fderiv 𝕜 e (e.symm p) v) = v := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun (e.fderiv_symm_comp_fderiv hp hd hds) v

/-- Pointwise form of `OpenPartialHomeomorph.fderiv_comp_fderiv_symm`. -/
theorem fderiv_apply_fderiv_symm_apply (e : OpenPartialHomeomorph E F) {p : F}
    (hp : p ∈ e.target) (hd : DifferentiableAt 𝕜 e (e.symm p))
    (hds : DifferentiableAt 𝕜 e.symm p) (w : F) :
    fderiv 𝕜 e (e.symm p) (fderiv 𝕜 e.symm p w) = w := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun (e.fderiv_comp_fderiv_symm hp hd hds) w

end OpenPartialHomeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {U : Opens E} {V : Opens F}
  {Φ : E → F} {Ψ : F → E}

/-- **The derivative of the inverse.** If `Φ` is differentiable on `U` and maps it into `V`, and
`Ψ`, differentiable on `V`, is inverse to `Φ` (`Φ ∘ Ψ = id` on `V`, `Ψ ∘ Φ = id` on `U`), then
`DΦ(y) ∘ DΨ(Φ y) = id` at every `y ∈ U`. -/
theorem fderiv_comp_fderiv_eq_id_of_invOn (hΦ : DifferentiableOn 𝕜 Φ U) (hmaps : MapsTo Φ U V)
    (hΨ : DifferentiableOn 𝕜 Ψ V) (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    {y : E} (hy : y ∈ (U : Set E)) :
    fderiv 𝕜 Φ y ∘L fderiv 𝕜 Ψ (Φ y) = ContinuousLinearMap.id 𝕜 F := by
  have hx : Φ y ∈ (V : Set F) := hmaps hy
  have hcomp : HasFDerivAt (Φ ∘ Ψ) (fderiv 𝕜 Φ y ∘L fderiv 𝕜 Ψ (Φ y)) (Φ y) := by
    have hΦd := ((hΦ y hy).differentiableAt (U.isOpen.mem_nhds hy)).hasFDerivAt
    rw [← hΨΦ hy] at hΦd
    have := hΦd.comp (Φ y) ((hΨ _ hx).differentiableAt (V.isOpen.mem_nhds hx)).hasFDerivAt
    rwa [hΨΦ hy] at this
  have hid : Φ ∘ Ψ =ᶠ[𝓝 (Φ y)] id :=
    Filter.eventually_of_mem (V.isOpen.mem_nhds hx) fun x hxV => hΦΨ hxV
  exact (hcomp.congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id (Φ y))

end TauCeti

/-- Precomposition by a continuous linear equivalence preserves the image of the locus where
the totalized Fréchet derivative vanishes. No differentiability hypothesis is needed. -/
theorem ContinuousLinearEquiv.image_vanishingFDeriv_comp {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (e : E ≃L[𝕜] F) (u : F → G) :
    u '' {x | fderiv 𝕜 u x = 0} = (u ∘ e) '' {y | fderiv 𝕜 (u ∘ e) y = 0} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, ?_, by simp⟩
    have hx0 : fderiv 𝕜 u x = 0 := hx
    simp only [Set.mem_ofPred_eq, e.comp_right_fderiv, e.apply_symm_apply, hx0,
      ContinuousLinearMap.zero_comp]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, rfl⟩
    ext v
    have hzero : fderiv 𝕜 (u ∘ e) y = 0 := hy
    rw [e.comp_right_fderiv] at hzero
    have := congrArg (fun L : E →L[𝕜] G ↦ L (e.symm v)) hzero
    simpa using this
