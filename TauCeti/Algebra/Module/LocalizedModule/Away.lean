/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Tactic.Module

/-!
# Clearing denominators in a localization away from an element

Let `φ : N → N_f` be a localization of a module away from `f`. If an element `σ` of `N_f` is
written as `x / fᵏ`, then annihilation of `x` by a power of `f g` transfers to annihilation of
`σ` by the same power of `g`, because the factor `f` is invertible on `N_f`. On `Spec R` this says
that a section of `M^~` over `D(f)` vanishing on `D(f g)` is killed by a power of `g`.

## Main statements

* `IsLocalizedModule.Away.pow_smul_eq_zero_of_pow_smul_eq`: if `fᵏ σ = φ x` and `(f g)ⁿ x = 0`,
  then `gⁿ σ = 0`.
-/

public section

namespace IsLocalizedModule.Away

variable {A N N' : Type*} [CommSemiring A] [AddCommMonoid N] [Module A N] [AddCommMonoid N']
  [Module A N'] {f g : A} (φ : N →ₗ[A] N') [IsLocalizedModule.Away f φ]

/-- Clearing denominators in a localization `φ : N → N_f`: if `fᵏ σ = φ x` and `(f g)ⁿ` kills `x`,
then `gⁿ` kills `σ`. -/
theorem pow_smul_eq_zero_of_pow_smul_eq {x : N} {σ : N'} {k n : ℕ} (hk : f ^ k • σ = φ x)
    (hn : (f * g) ^ n • x = 0) : g ^ n • σ = 0 := by
  refine IsLocalizedModule.smul_injective φ ⟨f ^ (n + k), pow_mem (Submonoid.mem_powers f) _⟩ ?_
  simp only [Submonoid.mk_smul, smul_zero]
  have h : f ^ (n + k) • g ^ n • σ = (f * g) ^ n • f ^ k • σ := by module
  rw [h, hk, ← map_smul, hn, map_zero]

end IsLocalizedModule.Away
