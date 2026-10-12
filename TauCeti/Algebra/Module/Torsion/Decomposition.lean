/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Primary decomposition of torsion subgroups

For a nonzero natural number `N`, the prime-power factors `p ^ N.factorization p` are pairwise
coprime and multiply to `N`. Consequently the `N`-torsion subgroup of an additive commutative
group is the internal direct sum of its `p ^ N.factorization p`-torsion subgroups, one for each
prime factor `p` of `N`. This reduces questions about `N`-torsion to prime-power torsion.

## Main results

* `TauCeti.AddSubgroup.torsionBy_primeFactors_isInternal`: the `N`-torsion subgroup is the
  internal direct sum of its primary components.
-/

public section

namespace TauCeti

namespace AddSubgroup

open scoped DirectSum

/-- The primary torsion subgroups form an internal direct sum of the ambient `N`-torsion
subgroup. -/
theorem torsionBy_primeFactors_isInternal {A : Type*} [AddCommGroup A] (N : ℕ) (hN : N ≠ 0) :
    DirectSum.IsInternal fun p : N.primeFactors ↦
      Submodule.torsionBy ℤ (_root_.AddSubgroup.torsionBy A (N : ℤ))
        ((p ^ N.factorization p : ℕ) : ℤ) := by
  have hcoprime : (N.primeFactors : Set ℕ).Pairwise
      (Function.onFun IsCoprime fun p ↦ ((p ^ N.factorization p : ℕ) : ℤ)) := by
    intro p hp r hr hpr
    have hne : (⟨p, hp⟩ : N.primeFactors) ≠ ⟨r, hr⟩ :=
      fun h ↦ hpr (congrArg Subtype.val h)
    exact _root_.Nat.Coprime.cast <| N.pairwise_coprime_pow_primeFactors_factorization hne
  apply Submodule.torsionBy_isInternal hcoprime
  have hprod : ∏ p ∈ N.primeFactors, (((p ^ N.factorization p : ℕ) : ℤ)) = (N : ℤ) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hN).symm
  rw [hprod]
  exact Submodule.torsionBy_isTorsionBy (R := ℤ) (N : ℤ)

end AddSubgroup

end TauCeti
