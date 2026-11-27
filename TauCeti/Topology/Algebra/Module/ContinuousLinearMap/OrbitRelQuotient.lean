/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations

/-!
# Orbit-quotient descent for continuous linear precomposition and dual evaluation

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with fibrewise precomposition
`ContinuousLinearMap.precomp` (`TauCeti.precomp_orbitRelQuotientRec`), dual pairing
(`TauCeti.orbitRelQuotientRec_dual_apply`), and fibrewise dual precomposition
(`TauCeti.dual_precomp_orbitRelQuotientRec`).
-/

public section

namespace TauCeti

/-- Fibrewise precomposition into any third module family `V₃` over `M ⧸ G` commutes with
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

section Dual

variable {G M 𝕜 : Type*} [Group G] [MulAction G M] [NontriviallyNormedField 𝕜]

/-- Pairing a descended dual family with a descended module family over `M ⧸ G` agrees with the
scalar descent `MulAction.orbitRelQuotientLift` of their upstairs pairing. -/
theorem orbitRelQuotientRec_dual_apply {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    {α : ∀ x : M, StrongDual 𝕜 (V (Quotient.mk (MulAction.orbitRel G M) x))}
    {t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (q : MulAction.orbitRel.Quotient G M) : MulAction.orbitRelQuotientRec
        (V := fun q ↦ StrongDual 𝕜 (V q)) α hα q (MulAction.orbitRelQuotientRec t ht q) =
      MulAction.orbitRelQuotientLift (fun x ↦ α x (t x))
        (MulAction.apply₂_smul_eq (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht) q :=
  MulAction.apply₂_orbitRelQuotientRec_eq_orbitRelQuotientLift
    (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht q

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

end Dual

end TauCeti
