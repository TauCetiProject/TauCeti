/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Derivatives under local and linear equivalences

Mathlib's `OpenPartialHomeomorph.hasFDerivAt_symm` computes the derivative of the inverse from an
invertible derivative of the map. Without assuming that invertibility, this file records that when
both the map and its inverse are differentiable at corresponding points, their derivatives compose
to the identity. It does so for a map `Φ` with a local right inverse `Ψ` (`Φ ∘ Ψ = id` near a
point), and in particular for open partial homeomorphisms.

## Main results

* `TauCeti.fderiv_comp_fderiv_eq_id_of_eventuallyEq`: if `Φ ∘ Ψ = id` near `x`, then
  `DΦ(Ψ x) ∘ DΨ(x) = id`.
* `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`: the derivative of the inverse is a left inverse
  of the derivative.
* `OpenPartialHomeomorph.fderiv_comp_fderiv_symm`: the derivative of the inverse is a right
  inverse of the derivative.
* `OpenPartialHomeomorph.fderiv_symm_apply_fderiv_apply`,
  `OpenPartialHomeomorph.fderiv_apply_fderiv_symm_apply`: the same identities evaluated at a
  vector.
* `ContinuousLinearEquiv.image_vanishingFDeriv_comp`: precomposition by a continuous linear
  equivalence preserves the image of the vanishing-derivative locus.

Precomposition by a continuous linear equivalence preserves the image of the vanishing-derivative
locus, with no differentiability premise. This follows the totalized derivative calculation in
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Basic.lean`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {Φ : E → F} {Ψ : F → E}

/-- **The derivative of a local right inverse.** If `Φ ∘ Ψ = id` near `x`, `Ψ` is differentiable
at `x` and `Φ` is differentiable at `Ψ x`, then `DΦ(Ψ x) ∘ DΨ(x) = id`. -/
theorem fderiv_comp_fderiv_eq_id_of_eventuallyEq {x : F} (hΦ : DifferentiableAt 𝕜 Φ (Ψ x))
    (hΨ : DifferentiableAt 𝕜 Ψ x) (h : Φ ∘ Ψ =ᶠ[𝓝 x] id) :
    fderiv 𝕜 Φ (Ψ x) ∘L fderiv 𝕜 Ψ x = ContinuousLinearMap.id 𝕜 F :=
  (hΦ.hasFDerivAt.comp x hΨ.hasFDerivAt).unique ((hasFDerivAt_id x).congr_of_eventuallyEq h)

end TauCeti

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the inverse of an open partial homeomorphism at a point of its target is a
left inverse of the derivative at the corresponding point of its source. -/
theorem fderiv_symm_comp_fderiv (e : OpenPartialHomeomorph E F) {p : F} (hp : p ∈ e.target)
    (hd : DifferentiableAt 𝕜 e (e.symm p)) (hds : DifferentiableAt 𝕜 e.symm p) :
    (fderiv 𝕜 e.symm p).comp (fderiv 𝕜 e (e.symm p)) = ContinuousLinearMap.id 𝕜 E := by
  have hds' : DifferentiableAt 𝕜 e.symm (e (e.symm p)) := by rwa [e.right_inv hp]
  have h := TauCeti.fderiv_comp_fderiv_eq_id_of_eventuallyEq hds' hd
    (eventually_of_mem (e.open_source.mem_nhds (e.map_target hp)) fun r hr ↦ e.left_inv hr)
  rwa [e.right_inv hp] at h

/-- The derivative of the inverse of an open partial homeomorphism at a point of its target is a
right inverse of the derivative at the corresponding point of its source. -/
theorem fderiv_comp_fderiv_symm (e : OpenPartialHomeomorph E F) {p : F} (hp : p ∈ e.target)
    (hd : DifferentiableAt 𝕜 e (e.symm p)) (hds : DifferentiableAt 𝕜 e.symm p) :
    (fderiv 𝕜 e (e.symm p)).comp (fderiv 𝕜 e.symm p) = ContinuousLinearMap.id 𝕜 F :=
  TauCeti.fderiv_comp_fderiv_eq_id_of_eventuallyEq hd hds
    (eventually_of_mem (e.open_target.mem_nhds hp) fun _ hr ↦ e.right_inv hr)

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
