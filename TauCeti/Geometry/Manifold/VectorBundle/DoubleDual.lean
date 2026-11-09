/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.DoubleDual

/-!
# Smooth double-dual evaluation in vector bundles

The canonical evaluation map `bundleDoubleDual` is smooth in the induced hom-bundle charts,
because its expression in every frame is the constant map `NormedSpace.inclusionInDoubleDual`.
In finite dimensions over a complete field, the inverse of `bundleDoubleDualEquiv` is smooth too.
Neither identification requires a metric or an orientation, or excludes rank zero.
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
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}

-- Proposition-valued search hints for the nested hom bundles. The statement-level letI
-- bindings supply Mathlib's native data instances directly, avoiding exported aliases while
-- keeping three nested hom spaces within the default instance-search budget.
private local instance : ∀ x, IsTopologicalAddGroup (StrongDual 𝕜 (V x)) := fun _ ↦ inferInstance
private local instance : ∀ x, ContinuousSMul 𝕜 (StrongDual 𝕜 (V x)) := fun _ ↦ inferInstance
private local instance : ∀ x, IsTopologicalAddGroup (StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
  fun _ ↦ inferInstance
private local instance : ∀ x, ContinuousSMul 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
  fun _ ↦ inferInstance

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

/-- Canonical double-dual evaluation is smooth in the induced hom-bundle charts. -/
theorem contMDiff_bundleDoubleDual :
    letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : ∀ x, TopologicalSpace (V x →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (V x))) :=
      fun x ↦ ContinuousLinearMap.topologicalSpace (σ := RingHom.id 𝕜)
        (E := V x) (F := StrongDual 𝕜 (StrongDual 𝕜 (V x)))
    letI := Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜) F V
      (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))
    letI := Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜) F V
      (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))
    ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) x
        (bundleDoubleDual (𝕜 := 𝕜) (F := F) V x)) := by
  let : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  exact contMDiff_hom_bundle_of_inCoordinates_eq_const
    (F₁ := F) (F₂ := StrongDual 𝕜 (StrongDual 𝕜 F))
    (V := V) (W := fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x)))
    (c := fun _ ↦ NormedSpace.inclusionInDoubleDual 𝕜 F)
    (fun a x hx _ ↦ bundleDoubleDual_inCoordinates V a hx)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The inverse finite-dimensional double-dual identification is smooth in hom-bundle charts. -/
theorem contMDiff_bundleDoubleDualEquiv_symm :
    letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : ∀ x, TopologicalSpace (StrongDual 𝕜 (StrongDual 𝕜 (V x)) →L[𝕜] V x) :=
      fun x ↦ ContinuousLinearMap.topologicalSpace (σ := RingHom.id 𝕜)
        (E := StrongDual 𝕜 (StrongDual 𝕜 (V x))) (F := V x)
    letI := Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
      (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x))) F V
    letI := Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
      (StrongDual 𝕜 (StrongDual 𝕜 F)) (fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x))) F V
    ContMDiff I (I.prod 𝓘(𝕜, StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F) x
        (bundleDoubleDualEquiv (𝕜 := 𝕜) (F := F) V x).symm.toContinuousLinearMap) := by
  let : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  exact contMDiff_hom_bundle_of_inCoordinates_eq_const
    (F₁ := StrongDual 𝕜 (StrongDual 𝕜 F)) (F₂ := F)
    (V := fun x ↦ StrongDual 𝕜 (StrongDual 𝕜 (V x))) (W := V)
    (c := fun _ ↦ (NormedSpace.inclusionInDoubleDual 𝕜 F).inverse)
    (fun a x _ hx ↦ bundleDoubleDualEquiv_symm_inCoordinates V a hx)

end TauCeti
