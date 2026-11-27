/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations

/-!
# Orbit-quotient descent for dual continuous linear precomposition

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with fibrewise dual precomposition
`ContinuousLinearMap.precomp 𝕜` (`TauCeti.dual_precomp_orbitRelQuotientRec`).
-/

public section

namespace TauCeti

variable {G M 𝕜 : Type*} [Group G] [MulAction G M] [NontriviallyNormedField 𝕜]

/-- Fibrewise dual precomposition `ContinuousLinearMap.precomp 𝕜` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem dual_precomp_orbitRelQuotientRec {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (q : MulAction.orbitRel.Quotient G M) :
    ContinuousLinearMap.precomp 𝕜 (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q)
        φ hφ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
        (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
        (MulAction.apply_smul_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) q :=
  MulAction.apply_orbitRelQuotientRec (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ q

end TauCeti
