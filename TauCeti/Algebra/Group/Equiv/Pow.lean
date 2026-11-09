/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Powers under a multiplicative equivalence

A multiplicative equivalence commutes with taking `n`-th powers, so the `n`-th power map is
injective on one side exactly when it is injective on the other.

## Main results

* `MulEquiv.injective_pow_iff` and its additive form `AddEquiv.injective_nsmul_iff`: taking `n`-th
  powers is injective on one side of an equivalence exactly when it is injective on the other.
-/

public section

namespace MulEquiv

/-- Taking `n`-th powers is injective on `M` exactly when it is injective on `N`, for a
multiplicative equivalence `M ≃* N`, since the equivalence commutes with it. -/
@[to_additive /-- Multiplication by `n` is injective on `M` exactly when it is injective on `N`,
for an additive equivalence `M ≃+ N`, since the equivalence commutes with it. -/]
theorem injective_pow_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (n : ℕ) :
    Function.Injective (fun x : M ↦ x ^ n) ↔ Function.Injective (fun y : N ↦ y ^ n) := by
  have h : (fun y : N ↦ y ^ n) = e ∘ (fun x : M ↦ x ^ n) ∘ e.symm := by
    ext y
    simp
  rw [h, EquivLike.comp_injective, EquivLike.injective_comp]

end MulEquiv

end
