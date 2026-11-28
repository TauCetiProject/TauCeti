/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations

/-!
# Orbit-quotient descent for topological tensor-product bundles

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with fibrewise tensor-product
operations (`TauCeti.bundleTensorMap_smul_heq`, `TauCeti.bundleTensorMap_orbitRelQuotientRec`,
`TauCeti.bundleTensorLift_smul_heq`, and `TauCeti.bundleTensorLift_orbitRelQuotientRec`).
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

variable {G M : Type*} [Group G] [MulAction G M]

section Map

variable {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  {V₁ V₂ V₁' V₂' : MulAction.orbitRel.Quotient G M → Type*} [∀ q, AddCommGroup (V₁ q)]
  [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)] [∀ q, AddCommGroup (V₂ q)]
  [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)] [∀ q, AddCommGroup (V₁' q)]
  [∀ q, Module 𝕜 (V₁' q)] [∀ q, TopologicalSpace (V₁' q)] [∀ q, AddCommGroup (V₂' q)]
  [∀ q, Module 𝕜 (V₂' q)] [∀ q, TopologicalSpace (V₂' q)]
  [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
  [∀ q, TopologicalSpace (V₁' q ⊗[𝕜] V₂' q)] [∀ q, IsModuleTopology 𝕜 (V₁' q ⊗[𝕜] V₂' q)]
  {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
  {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₂' (Quotient.mk (MulAction.orbitRel G M) x)}

/-- If two linear families `φ₁` and `φ₂` upstairs are `G`-invariant, so is their fibrewise tensor
product `bundleTensorMap φ₁ φ₂`. -/
theorem bundleTensorMap_smul_heq (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (g : G) (x : M) :
    bundleTensorMap φ₁ φ₂ (g • x) ≍ bundleTensorMap φ₁ φ₂ x := by
  simp only [bundleTensorMap_eq]
  exact MulAction.apply₂_smul_heq
    (fun _ (A₁ : _ →L[𝕜] _) (A₂ : _ →L[𝕜] _) ↦ A₁.tensorMap A₂) hφ₁ hφ₂ g x

/-- Fibrewise tensor product `bundleTensorMap` commutes with `MulAction.orbitRelQuotientRec`. -/
theorem bundleTensorMap_orbitRelQuotientRec (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleTensorMap (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₁' q) φ₁ hφ₁)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q →L[𝕜] V₂' q) φ₂ hφ₂) q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
        (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) q := by
  induction q using Quotient.inductionOn with | h x =>
  simp only [MulAction.orbitRelQuotientRec_mk, bundleTensorMap_eq]

end Map

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
  [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]

section Lift

variable [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
  {Φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜] V₃ (Quotient.mk (MulAction.orbitRel G M) x)}

/-- If a bilinear family `Φ` upstairs is `G`-invariant, so is `bundleTensorLift Φ`. -/
theorem bundleTensorLift_smul_heq (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (g : G) (x : M) :
    bundleTensorLift Φ (g • x) ≍ bundleTensorLift Φ x := by
  simp only [bundleTensorLift_eq]
  exact MulAction.apply_smul_heq (fun _ (B : _ →L[𝕜] _ →L[𝕜] _) ↦ B.tensorLift) hΦ g x

/-- `bundleTensorLift` commutes with `MulAction.orbitRelQuotientRec`. -/
theorem bundleTensorLift_orbitRelQuotientRec
    (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleTensorLift (MulAction.orbitRelQuotientRec
        (V := fun q ↦ V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q) Φ hΦ) q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q)
        (bundleTensorLift Φ) (bundleTensorLift_smul_heq hΦ) q := by
  induction q using Quotient.inductionOn with | h x =>
  simp only [MulAction.orbitRelQuotientRec_mk, bundleTensorLift_eq]

end Lift

end NormedField

end TauCeti
