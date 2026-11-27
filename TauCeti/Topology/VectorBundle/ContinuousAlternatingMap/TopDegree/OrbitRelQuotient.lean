/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap.TopDegree.Basic
import TauCeti.Topology.Algebra.Module.Determinant.OrbitRelQuotient

/-!
# Orbit-quotient descent for top-degree alternating forms

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with top-degree alternating-form
pullbacks along fibrewise endomorphisms
(`TauCeti.compContinuousLinearMap_orbitRelQuotientRec_eq_det_smul`).
-/

public section

open Bundle

namespace TauCeti

/-- On the top-degree scalar alternating line bundle (`Fintype.card ι = Module.finrank 𝕜 F`) over
`M ⧸ G`, pulling back a descended top form along a descended endomorphism multiplies the form by
the descended scalar determinant `MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det) ...`. -/
theorem compContinuousLinearMap_orbitRelQuotientRec_eq_det_smul
    {G M 𝕜 ι F : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
    [NontriviallyNormedField 𝕜] [Fintype ι] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    (hrank : Fintype.card ι = Module.finrank 𝕜 F)
    {α : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜] 𝕜}
    {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (q : MulAction.orbitRel.Quotient G M) : ContinuousAlternatingMap.compContinuousLinearMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q [⋀^ι]→L[𝕜] 𝕜) α hα q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ q) =
      MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_smul_eq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ) q •
        MulAction.orbitRelQuotientRec (V := fun q ↦ V q [⋀^ι]→L[𝕜] 𝕜) α hα q := by
  rw [fiber_compContinuousLinearMap_eq_det_smul hrank, det_orbitRelQuotientRec]

end TauCeti
