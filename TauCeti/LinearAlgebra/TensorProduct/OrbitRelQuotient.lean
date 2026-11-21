/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Orbit-quotient descent for pure tensors

Algebraic compatibility of `MulAction.orbitRelQuotientRec` with fibrewise pure tensors
(`TauCeti.tmul_orbitRelQuotientRec`).
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Fibrewise pure tensor `⊗ₜ[𝕜]` commutes with `MulAction.orbitRelQuotientRec`. -/
theorem tmul_orbitRelQuotientRec {G M 𝕜 : Type*} [Group G] [MulAction G M] [CommRing 𝕜]
    {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)]
    {t₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x)}
    {t₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (ht₁ : ∀ (g : G) (x : M), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : M), t₂ (g • x) ≍ t₂ x)
    (q : MulAction.orbitRel.Quotient G M) :
    MulAction.orbitRelQuotientRec t₁ ht₁ q ⊗ₜ[𝕜] MulAction.orbitRelQuotientRec t₂ ht₂ q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q)
        (fun x ↦ t₁ x ⊗ₜ[𝕜] t₂ x)
        (MulAction.apply₂_smul_heq (fun _ v w ↦ v ⊗ₜ[𝕜] w) ht₁ ht₂) q :=
  MulAction.apply₂_orbitRelQuotientRec (fun _ v w ↦ v ⊗ₜ[𝕜] w) ht₁ ht₂ q

end TauCeti
