/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The derivative of the inverse of a map

Mathlib's `OpenPartialHomeomorph.hasFDerivAt_symm` computes the derivative of the inverse from an
invertible derivative of the map. Without assuming that invertibility, this file records that when
both the map and its inverse are differentiable at corresponding points, their derivatives compose
to the identity. It does so for open partial homeomorphisms, and for a map `Φ` differentiable on an
open set `U` and mapping it into an open set `V`, with an inverse `Ψ` differentiable on `V`
(`Φ ∘ Ψ = id` on `V` and `Ψ ∘ Φ = id` on `U`); the Jacobians of such `Φ` and `Ψ` are then
reciprocal.

## Main results

* `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`: the derivative of the inverse is a left inverse
  of the derivative.
* `TauCeti.fderiv_comp_fderiv_eq_id_of_invOn`: `DΦ(y) ∘ DΨ(Φ y) = id`.
* `TauCeti.abs_det_mul_abs_det_of_invOn`: `|det DΦ(y)| |det DΨ(Φ y)| = 1`.
* `TauCeti.toEuclideanCLM_inv_fderiv_of_invOn`: on Euclidean space, the operator of the inverse
  Jacobian matrix `DΦ(y)⁻¹` is `DΨ(Φ y)`.
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

end OpenPartialHomeomorph

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U V : Opens E} {Φ Ψ : E → E}

/-- **The derivative of the inverse.** If `Φ` is differentiable on `U` and maps it into `V`, and
`Ψ`, differentiable on `V`, is inverse to `Φ` (`Φ ∘ Ψ = id` on `V`, `Ψ ∘ Φ = id` on `U`), then
`DΦ(y) ∘ DΨ(Φ y) = id` at every `y ∈ U`. -/
theorem fderiv_comp_fderiv_eq_id_of_invOn (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V)
    (hΨ : DifferentiableOn ℝ Ψ V) (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    {y : E} (hy : y ∈ (U : Set E)) :
    fderiv ℝ Φ y ∘L fderiv ℝ Ψ (Φ y) = ContinuousLinearMap.id ℝ E := by
  have hx : Φ y ∈ (V : Set E) := hmaps hy
  have hcomp : HasFDerivAt (Φ ∘ Ψ) (fderiv ℝ Φ y ∘L fderiv ℝ Ψ (Φ y)) (Φ y) := by
    have hΦd := ((hΦ y hy).differentiableAt (U.isOpen.mem_nhds hy)).hasFDerivAt
    rw [← hΨΦ hy] at hΦd
    have := hΦd.comp (Φ y) ((hΨ _ hx).differentiableAt (V.isOpen.mem_nhds hx)).hasFDerivAt
    rwa [hΨΦ hy] at this
  have hid : Φ ∘ Ψ =ᶠ[𝓝 (Φ y)] id :=
    Filter.eventually_of_mem (V.isOpen.mem_nhds hx) fun x hxV => hΦΨ hxV
  exact (hcomp.congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id (Φ y))

/-- The Jacobians of a map `Φ`, differentiable on `U` and mapping it into `V`, and of its inverse
`Ψ`, differentiable on `V`, are reciprocal: `|det DΦ(y)| |det DΨ(Φ y)| = 1` at every `y ∈ U`. -/
theorem abs_det_mul_abs_det_of_invOn (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V)
    (hΨ : DifferentiableOn ℝ Ψ V) (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    {y : E} (hy : y ∈ (U : Set E)) :
    |(fderiv ℝ Φ y).det| * |(fderiv ℝ Ψ (Φ y)).det| = 1 := by
  have hdet : (fderiv ℝ Φ y ∘L fderiv ℝ Ψ (Φ y)).det =
      (fderiv ℝ Φ y).det * (fderiv ℝ Ψ (Φ y)).det :=
    LinearMap.det_comp _ _
  rw [fderiv_comp_fderiv_eq_id_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ hy] at hdet
  rw [← abs_mul, ← hdet, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id,
    abs_one]

/-- For a map `Φ` of Euclidean space, differentiable on `U` and mapping it into `V`, with inverse
`Ψ` differentiable on `V`, the operator of the inverse Jacobian matrix of `Φ` at `y ∈ U` is
`DΨ(Φ y)`. -/
theorem toEuclideanCLM_inv_fderiv_of_invOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V) (hΨ : DifferentiableOn ℝ Ψ V)
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ =
      fderiv ℝ Ψ (Φ y) := by
  rw [Matrix.inv_eq_right_inv (B := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Ψ (Φ y))),
    StarAlgEquiv.apply_symm_apply]
  rw [← map_mul, ContinuousLinearMap.mul_def,
    fderiv_comp_fderiv_eq_id_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ hy, ← ContinuousLinearMap.one_def,
    map_one]

end TauCeti
