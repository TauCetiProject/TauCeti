/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Smooth bidual evaluation in vector bundles

The canonical evaluation map into the continuous bidual is defined fibrewise without choosing
norms on the fibres. Its formula is evaluation, and in every bundle frame it is Mathlib's
`NormedSpace.inclusionInDoubleDual` on the model fibre. Consequently it is a smooth bundle
homomorphism. This supplies the bidual part of canonical identifications of dual tensor bundles,
without choosing a metric or an orientation.

The construction transports Mathlib's normed-space bidual map through a bundle trivialization;
the evaluation formula proves that the result does not depend on that trivialization. In finite
dimensions over a complete field, `Module.evalEquiv` gives the inverse identification. Both
identifications are smooth in the induced bundle charts, including rank zero.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {𝕜 M F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Canonical evaluation into the continuous bidual of a bundle fibre. No norm on the fibre
is chosen: continuity is transported from the model fibre. -/
def bundleBidual (x : M) : V x →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x)) :=
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F V x)
  let d := e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let dd := d.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  dd.symm.toContinuousLinearMap.comp
    ((NormedSpace.inclusionInDoubleDual 𝕜 F).comp e.toContinuousLinearMap)

/-- The bundle bidual map is evaluation on covectors. -/
@[simp]
theorem bundleBidual_apply (x : M) (v : V x) (φ : StrongDual 𝕜 (V x)) :
    bundleBidual (F := F) V x v φ = φ v := by
  simp [bundleBidual, ContinuousLinearEquiv.arrowCongr_apply,
    (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x)]

-- Local caches of the native structures keep three nested hom spaces within the default
-- instance-search budget. Data instances must be public for elaborating public signatures;
-- none of these hints is registered globally.
/-- The native normed group on the bidual model, cached locally for nested hom spaces. -/
local instance bidualModelNormedAddCommGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
/-- The native normed scalar action on the bidual model, cached locally. -/
local instance bidualModelNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
private local instance : ∀ x, IsTopologicalAddGroup (StrongDual 𝕜 (V x)) := fun _ ↦ inferInstance
private local instance : ∀ x, ContinuousSMul 𝕜 (StrongDual 𝕜 (V x)) := fun _ ↦ inferInstance
private local instance : ∀ x, IsTopologicalAddGroup (StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
  fun _ ↦ inferInstance
private local instance : ∀ x, ContinuousSMul 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
  fun _ ↦ inferInstance
/-- The native additive group on each bidual fibre, cached locally. -/
local instance bidualFibreAddCommGroup :
    ∀ x, AddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 (V x))) := fun _ ↦ inferInstance
/-- The native scalar action on each bidual fibre, cached locally. -/
local instance bidualFibreModule :
    ∀ x, Module 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (V x))) := fun _ ↦ inferInstance
/-- The native strong topology on each bidual fibre, cached locally. -/
local instance bidualFibreTopologicalSpace :
    ∀ x, TopologicalSpace (StrongDual 𝕜 (StrongDual 𝕜 (V x))) := fun _ ↦ inferInstance
/-- The native dual-bundle topology, cached locally for iterated hom bundles. -/
local instance dualTotalSpaceTopology : TopologicalSpace
    (TotalSpace (StrongDual 𝕜 F) (fun x ↦ StrongDual 𝕜 (V x))) := inferInstance
/-- The native bidual-bundle topology, cached locally for iterated hom bundles. -/
local instance bidualTotalSpaceTopology : TopologicalSpace
    (TotalSpace (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))) := inferInstance
/-- The native bidual fibre bundle, cached locally. -/
local instance bidualFiberBundle : FiberBundle (StrongDual 𝕜 (StrongDual 𝕜 F))
    (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x))) := inferInstance
private local instance : VectorBundle 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F))
    (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x))) := inferInstance
/-- The native hom-bundle topology for maps into the bidual, cached locally. -/
local instance bidualHomTotalSpaceTopology : TopologicalSpace
    (TotalSpace (F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun x ↦ V x →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x)))) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜) F V
    (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))

/-- In any frame, bidual evaluation is the model-fibre evaluation map. -/
theorem bundleBidual_inCoordinates (a : M) {x : M}
    (hx : x ∈ (trivializationAt F V a).baseSet) :
    ContinuousLinearMap.inCoordinates F V
      (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun y ↦ StrongDual 𝕜 (StrongDual 𝕜 (V y))) a x a x
      (bundleBidual (F := F) V x) = NormedSpace.inclusionInDoubleDual 𝕜 F := by
  ext v φ
  rw [inCoordinates_apply_eq₂ hx
    (by simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx)
    (by simp [Trivial.eq_trivialization]), bundleBidual_apply]
  have hdual : x ∈ (trivializationAt (StrongDual 𝕜 F)
      (fun y ↦ StrongDual 𝕜 (V y)) a).baseSet := by
    simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx
  have hφ := (trivializationAt (StrongDual 𝕜 F) (fun y ↦ StrongDual 𝕜 (V y)) a
    ).continuousLinearMapAt_symmL (R := 𝕜) hdual φ
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hdual] at hφ
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivialization.symmL_apply _ hdual] at hφ
  simpa [Trivial.eq_trivialization, hx] using congrArg (fun f : StrongDual 𝕜 F ↦ f v) hφ

/-- The native hom fibre bundle for maps into the bidual, cached locally. -/
local instance bidualHomFiberBundle : FiberBundle (F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))
    (fun x ↦ V x →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜) F V
    (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))
private local instance : VectorBundle 𝕜 (F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))
    (fun x ↦ V x →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜) F V
    (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))

section Smooth

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}

/-- Canonical bidual evaluation is smooth in the induced hom-bundle charts. -/
theorem contMDiff_bundleBidual :
    ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) x
        (bundleBidual (𝕜 := 𝕜) (F := F) V x)) := by
  intro a
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,
    (contMDiffAt_const (c := NormedSpace.inclusionInDoubleDual 𝕜 F)
      ).congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F V a).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V a)] with x hx
  exact bundleBidual_inCoordinates V a hx

end Smooth

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- Evaluation identifies each finite-dimensional bundle fibre with its continuous bidual.
The equivalence is canonical, although its construction uses a frame. -/
def bundleBidualEquiv (x : M) : V x ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x)) :=
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F V x)
  let d := e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let dd := d.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let c : Module.Dual 𝕜 F ≃ₗ[𝕜] StrongDual 𝕜 F := LinearMap.toContinuousLinearMap
  let j := (Module.evalEquiv 𝕜 F).trans
    ((c.arrowCongr (LinearEquiv.refl 𝕜 𝕜)).trans LinearMap.toContinuousLinearMap)
  e.trans (j.toContinuousLinearEquiv.trans dd.symm)

/-- The finite-dimensional bidual equivalence has the canonical evaluation formula. -/
@[simp]
theorem bundleBidualEquiv_apply (x : M) (v : V x) (φ : StrongDual 𝕜 (V x)) :
    bundleBidualEquiv (F := F) V x v φ = φ v := by
  simp [bundleBidualEquiv, ContinuousLinearEquiv.arrowCongr_apply,
    (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x)]

/-- The finite-dimensional equivalence extends the canonical bidual map. -/
@[simp]
theorem bundleBidualEquiv_toContinuousLinearMap (x : M) :
    (bundleBidualEquiv (𝕜 := 𝕜) (F := F) V x).toContinuousLinearMap =
      bundleBidual (F := F) V x := by
  ext v φ
  simp

/-- Applying a covector after the inverse bidual identification is evaluation in the bidual. -/
@[simp]
theorem apply_bundleBidualEquiv_symm (x : M) (Φ : StrongDual 𝕜 (StrongDual 𝕜 (V x)))
    (φ : StrongDual 𝕜 (V x)) :
    φ ((bundleBidualEquiv (F := F) V x).symm Φ) = Φ φ := by
  rw [← bundleBidualEquiv_apply (F := F) V x]
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse bidual identification has the inverse of the constant model map in coordinates.
This pins its behaviour under changes of bundle frame. -/
theorem bundleBidualEquiv_symm_inCoordinates (a : M) {x : M}
    (hx : x ∈ (trivializationAt F V a).baseSet) :
    ContinuousLinearMap.inCoordinates (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun y ↦ StrongDual 𝕜 (StrongDual 𝕜 (V y))) F V a x a x
      (bundleBidualEquiv (F := F) V x).symm.toContinuousLinearMap =
        (NormedSpace.inclusionInDoubleDual 𝕜 F).inverse := by
  have h := ContinuousLinearMap.inCoordinates_inverse (𝕜 := 𝕜)
    (F' := StrongDual 𝕜 (StrongDual 𝕜 F))
    (W := fun y ↦ StrongDual 𝕜 (StrongDual 𝕜 (V y)))
    (bundleBidual (𝕜 := 𝕜) (F := F) V x) hx
    (by simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx)
  rw [← bundleBidualEquiv_toContinuousLinearMap, ContinuousLinearMap.inverse_equiv,
    bundleBidualEquiv_toContinuousLinearMap, bundleBidual_inCoordinates V a hx] at h
  exact h

section SmoothInverse

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The inverse finite-dimensional bidual identification is smooth in hom-bundle charts. -/
theorem contMDiff_bundleBidualEquiv_symm :
    ContMDiff I (I.prod 𝓘(𝕜, StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F) x
        (bundleBidualEquiv (𝕜 := 𝕜) (F := F) V x).symm.toContinuousLinearMap) := by
  intro a
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,
    (contMDiffAt_const (c := (NormedSpace.inclusionInDoubleDual 𝕜 F).inverse)
      ).congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F V a).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V a)] with x hx
  exact bundleBidualEquiv_symm_inCoordinates V a hx

end SmoothInverse

end FiniteDimensional

end TauCeti
