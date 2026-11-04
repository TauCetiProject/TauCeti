/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Topology.VectorBundle.Coordinates
public import TauCeti.Topology.VectorBundle.Dual

/-!
# Double-dual evaluation in vector bundles

The canonical evaluation map into the continuous double dual is defined fibrewise without choosing
norms on the fibres. Its formula is evaluation, and in every bundle frame it is Mathlib's
`NormedSpace.inclusionInDoubleDual` on the model fibre. This supplies the double-dual part of
canonical identifications of dual tensor bundles, without choosing a metric or an orientation.

The construction transports Mathlib's normed-space double-dual map through a bundle trivialization;
the evaluation formula proves that the result does not depend on that trivialization. In finite
dimensions over a complete field, `Module.evalEquiv` gives the inverse identification. Both
identifications have constant expressions in the induced bundle charts, including rank zero.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Topology

namespace TauCeti

variable {𝕜 M F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Canonical evaluation into the continuous double dual of a bundle fibre. No norm on the fibre
is chosen: continuity is transported from the model fibre. -/
def bundleDoubleDual (x : M) : V x →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x)) :=
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F V x)
  let d := e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let dd := d.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  dd.symm.toContinuousLinearMap.comp
    ((NormedSpace.inclusionInDoubleDual 𝕜 F).comp e.toContinuousLinearMap)

/-- The bundle double-dual map is evaluation on covectors. -/
@[simp]
theorem bundleDoubleDual_apply (x : M) (v : V x) (φ : StrongDual 𝕜 (V x)) :
    bundleDoubleDual (F := F) V x v φ = φ v := by
  simp [bundleDoubleDual, ContinuousLinearEquiv.arrowCongr_apply,
    (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x)]

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

/-- In any frame, double-dual evaluation is the model-fibre evaluation map. -/
theorem bundleDoubleDual_inCoordinates (a : M) {x : M}
    (hx : x ∈ (trivializationAt F V a).baseSet) :
    ContinuousLinearMap.inCoordinates F V
      (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun y ↦ StrongDual 𝕜 (StrongDual 𝕜 (V y))) a x a x
      (bundleDoubleDual (F := F) V x) = NormedSpace.inclusionInDoubleDual 𝕜 F := by
  ext v φ
  rw [inCoordinates_apply_eq₂ hx
    (by simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx)
    (by simp [Trivial.eq_trivialization]), bundleDoubleDual_apply]
  simpa [Trivial.eq_trivialization] using dual_trivializationAt_symm_apply V a hx φ v

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- Evaluation identifies each finite-dimensional bundle fibre with its continuous double dual.
The equivalence is canonical, although its construction uses a frame. -/
def bundleDoubleDualEquiv (x : M) : V x ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x)) :=
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F V x)
  let d := e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let dd := d.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let c : Module.Dual 𝕜 F ≃ₗ[𝕜] StrongDual 𝕜 F := LinearMap.toContinuousLinearMap
  let j := (Module.evalEquiv 𝕜 F).trans
    ((c.arrowCongr (LinearEquiv.refl 𝕜 𝕜)).trans LinearMap.toContinuousLinearMap)
  let j' := LinearEquiv.toContinuousLinearEquiv (𝕜 := 𝕜) (E := F)
    (F := StrongDual 𝕜 (StrongDual 𝕜 F)) j
  e.trans (j'.trans dd.symm)

/-- The finite-dimensional double-dual equivalence has the canonical evaluation formula. -/
@[simp]
theorem bundleDoubleDualEquiv_apply (x : M) (v : V x) (φ : StrongDual 𝕜 (V x)) :
    bundleDoubleDualEquiv (F := F) V x v φ = φ v := by
  simp [bundleDoubleDualEquiv, ContinuousLinearEquiv.arrowCongr_apply,
    (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x)]

/-- The finite-dimensional equivalence extends the canonical double-dual map. -/
@[simp]
theorem bundleDoubleDualEquiv_toContinuousLinearMap (x : M) :
    (bundleDoubleDualEquiv (𝕜 := 𝕜) (F := F) V x).toContinuousLinearMap =
      bundleDoubleDual (F := F) V x := by
  ext v φ
  simp

/-- Applying a covector after the inverse double-dual identification is evaluation in the
double dual. -/
@[simp]
theorem apply_bundleDoubleDualEquiv_symm (x : M) (Φ : StrongDual 𝕜 (StrongDual 𝕜 (V x)))
    (φ : StrongDual 𝕜 (V x)) :
    φ ((bundleDoubleDualEquiv (F := F) V x).symm Φ) = Φ φ := by
  rw [← bundleDoubleDualEquiv_apply (F := F) V x]
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse double-dual identification has the inverse of the constant model map in coordinates.
This pins its behaviour under changes of bundle frame. -/
theorem bundleDoubleDualEquiv_symm_inCoordinates (a : M) {x : M}
    (hx : x ∈ (trivializationAt F V a).baseSet) :
    ContinuousLinearMap.inCoordinates (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun y ↦ StrongDual 𝕜 (StrongDual 𝕜 (V y))) F V a x a x
      (bundleDoubleDualEquiv (𝕜 := 𝕜) (F := F) V x).symm.toContinuousLinearMap =
        (NormedSpace.inclusionInDoubleDual 𝕜 F).inverse := by
  have h := ContinuousLinearMap.inCoordinates_inverse (𝕜 := 𝕜)
    (F' := StrongDual 𝕜 (StrongDual 𝕜 F))
    (W := fun y ↦ StrongDual 𝕜 (StrongDual 𝕜 (V y)))
    (bundleDoubleDualEquiv (𝕜 := 𝕜) (F := F) V x).toContinuousLinearMap hx
    (by simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx)
  rw [ContinuousLinearMap.inverse_equiv] at h
  simpa only [bundleDoubleDualEquiv_toContinuousLinearMap,
    bundleDoubleDual_inCoordinates V a hx] using h

end FiniteDimensional

end TauCeti
