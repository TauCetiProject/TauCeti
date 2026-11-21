/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations

/-!
# Orbit-quotient descent for topological tensor-product bundles

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with fibrewise tensor-product
operations (`TauCeti.bundleTensorMap_smul_heq`, `TauCeti.bundleTensorMap_orbitRelQuotientRec`,
`TauCeti.bundleTensorLift_smul_heq`, `TauCeti.bundleTensorLift_orbitRelQuotientRec`, and
`TauCeti.bundleDualTensorHom_orbitRelQuotientRec`).
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

variable {G M : Type*} [Group G] [MulAction G M]

section Map

variable {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  {V₁ V₂ V₁' V₂' : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [∀ q, AddCommGroup (V₁' q)] [∀ q, Module 𝕜 (V₁' q)] [∀ q, TopologicalSpace (V₁' q)]
  [∀ q, AddCommGroup (V₂' q)] [∀ q, Module 𝕜 (V₂' q)] [∀ q, TopologicalSpace (V₂' q)]
  [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
  [∀ q, TopologicalSpace (V₁' q ⊗[𝕜] V₂' q)] [∀ q, IsModuleTopology 𝕜 (V₁' q ⊗[𝕜] V₂' q)]
  {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
  {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₂' (Quotient.mk (MulAction.orbitRel G M) x)}

/-- If two linear families `φ₁` and `φ₂` upstairs are `G`-invariant, so is their fibrewise tensor
product `bundleTensorMap φ₁ φ₂`. -/
theorem bundleTensorMap_smul_heq
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (g : G) (x : M) :
    bundleTensorMap φ₁ φ₂ (g • x) ≍ bundleTensorMap φ₁ φ₂ x := by
  let B : ∀ q, (V₁ q →L[𝕜] V₁' q) → (V₂ q →L[𝕜] V₂' q) → (V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q) :=
    fun q A₁ A₂ ↦ bundleTensorMap (B := Unit) (E₁ := fun _ ↦ V₁ q) (E₁' := fun _ ↦ V₁' q)
      (E₂ := fun _ ↦ V₂ q) (E₂' := fun _ ↦ V₂' q) (fun _ ↦ A₁) (fun _ ↦ A₂) ()
  have hB (y : M) :
      bundleTensorMap φ₁ φ₂ y = B (Quotient.mk (MulAction.orbitRel G M) y) (φ₁ y) (φ₂ y) :=
    ContinuousLinearMap.ext <| LinearMap.congr_fun <|
      _root_.TensorProduct.ext' fun v w ↦ by simp [B]
  rw [hB (g • x), hB x]
  exact MulAction.apply₂_smul_heq B hφ₁ hφ₂ g x

/-- Fibrewise tensor product `bundleTensorMap` commutes with `MulAction.orbitRelQuotientRec`. -/
theorem bundleTensorMap_orbitRelQuotientRec
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleTensorMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₁' q) φ₁ hφ₁)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q →L[𝕜] V₂' q) φ₂ hφ₂) q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
        (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) q := by
  induction q using Quotient.inductionOn with | h x =>
  exact ContinuousLinearMap.ext <| LinearMap.congr_fun <| _root_.TensorProduct.ext' fun _ _ ↦ by
    simp

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

/-- If a bilinear family `Φ` upstairs is `G`-invariant, so is its tensor-product lift
`bundleTensorLift Φ`. -/
theorem bundleTensorLift_smul_heq (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (g : G) (x : M) :
    bundleTensorLift Φ (g • x) ≍ bundleTensorLift Φ x := by
  let F : ∀ q, (V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q) → (V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q) :=
    fun q B ↦ bundleTensorLift (B := Unit)
      (E₁ := fun _ ↦ V₁ q) (E₂ := fun _ ↦ V₂ q) (E₃ := fun _ ↦ V₃ q) (fun _ ↦ B) ()
  have hF (y : M) : bundleTensorLift Φ y = F (Quotient.mk (MulAction.orbitRel G M) y) (Φ y) :=
    (eq_bundleTensorLift_iff.2 fun v w ↦ by simp [F]).symm
  rw [hF (g • x), hF x]
  exact MulAction.apply_smul_heq F hΦ g x

/-- The tensor-product universal property `bundleTensorLift` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem bundleTensorLift_orbitRelQuotientRec
    (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleTensorLift
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q) Φ hΦ) q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q)
        (bundleTensorLift Φ) (bundleTensorLift_smul_heq hΦ) q := by
  induction q using Quotient.inductionOn with | h x =>
  exact (eq_bundleTensorLift_iff.2 fun _ _ ↦ by simp).symm

end Lift

section DualTensorHom

variable [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
  [∀ q, TopologicalSpace (StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)]
  [∀ q, IsModuleTopology 𝕜 (StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)]

/-- Applying `bundleDualTensorHom` over `M ⧸ G` to the descent of an invariant section `τ` agrees
with the descent of `x ↦ bundleDualTensorHom ⟦x⟧ (τ x)`. -/
theorem bundleDualTensorHom_orbitRelQuotientRec
    {τ : ∀ x : M, StrongDual 𝕜 (V₁ (Quotient.mk (MulAction.orbitRel G M) x)) ⊗[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hτ : ∀ (g : G) (x : M), τ (g • x) ≍ τ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q
        (MulAction.orbitRelQuotientRec (V := fun q ↦ StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q) τ hτ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) (fun x ↦
        bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) (Quotient.mk (MulAction.orbitRel G M) x) (τ x))
        (MulAction.apply_smul_heq
          (fun q t ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q t) hτ) q :=
  MulAction.apply_orbitRelQuotientRec (fun q t ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q t) hτ q

end DualTensorHom

end NormedField

end TauCeti
