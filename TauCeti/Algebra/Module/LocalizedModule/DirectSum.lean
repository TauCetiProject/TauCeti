/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Localization of modules commutes with direct sums

If each `fᵢ : Mᵢ →ₗ[R] M'ᵢ` is a localization of modules at a submonoid `S` of `R`, then so is
the componentwise map `⨁ i, Mᵢ →ₗ[R] ⨁ i, M'ᵢ`, for an arbitrary index type. This is the
direct-sum counterpart of Mathlib's `IsLocalizedModule.prodMap` and `IsLocalizedModule.pi`.
-/

public section

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

attribute [local instance] IsLocalizedModule.isScalarTower_module

/-- Localization of modules commutes with direct sums. -/
instance directSum {ι : Type*}
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (DirectSum.lmap f) := by
  let (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.directSum
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

end IsLocalizedModule
