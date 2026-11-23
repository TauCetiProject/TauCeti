/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Orbit-quotient descent for Hom-bundle precomposition

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with fibrewise precomposition
`ContinuousLinearMap.precomp` (`TauCeti.precomp_orbitRelQuotientRec`).
-/

public section

namespace TauCeti

/-- Fibrewise precomposition into any third bundle `V₃` over `M ⧸ G` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem precomp_orbitRelQuotientRec {G M 𝕜 : Type*} [Group G] [MulAction G M]
    [NontriviallyNormedField 𝕜] {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    (V₃ : MulAction.orbitRel.Quotient G M → Type*)
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (q : MulAction.orbitRel.Quotient G M) :
    ContinuousLinearMap.precomp (V₃ q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) φ hφ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ (V₂ q →L[𝕜] V₃ q) →L[𝕜] V₁ q →L[𝕜] V₃ q)
        (fun x ↦ ContinuousLinearMap.precomp (V₃ (Quotient.mk (MulAction.orbitRel G M) x)) (φ x))
        (MulAction.apply_smul_heq (fun q A ↦ ContinuousLinearMap.precomp (V₃ q) A) hφ) q :=
  MulAction.apply_orbitRelQuotientRec (fun q A ↦ ContinuousLinearMap.precomp (V₃ q) A) hφ q

end TauCeti
