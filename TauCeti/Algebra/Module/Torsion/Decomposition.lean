/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Primary decomposition of `N`-torsion modules

For a nonzero natural number `N`, the prime-power factors `p ^ N.factorization p` are pairwise
coprime and multiply to `N`. Consequently a module over a commutative ring that is killed by `N`
is the internal direct sum of its `p ^ N.factorization p`-torsion submodules, one for each prime
factor `p` of `N`. Applied to the `N`-torsion subgroup of an additive commutative group, viewed
as a `ℤ`-module, this reduces questions about `N`-torsion to prime-power torsion.

## Main results

* `TauCeti.Submodule.torsionBy_primeFactors_isInternal`: a module killed by `N` is the internal
  direct sum of its primary components.
-/

public section

namespace TauCeti

namespace Submodule

/-- A module killed by a nonzero natural number `N` is the internal direct sum of its
`p ^ N.factorization p`-torsion submodules, where `p` ranges over the prime factors of `N`. -/
theorem torsionBy_primeFactors_isInternal {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {N : ℕ} (hN : N ≠ 0) (hM : Module.IsTorsionBy R M (N : R)) :
    DirectSum.IsInternal fun p : N.primeFactors ↦
      _root_.Submodule.torsionBy R M ((p ^ N.factorization p : ℕ) : R) := by
  refine _root_.Submodule.torsionBy_isInternal
    (q := fun p ↦ ((p ^ N.factorization p : ℕ) : R)) (fun p hp r hr hpr ↦ ?_) ?_
  · exact _root_.Nat.Coprime.cast <| N.pairwise_coprime_pow_primeFactors_factorization
      (i := ⟨p, hp⟩) (j := ⟨r, hr⟩) (Subtype.coe_ne_coe.mp hpr)
  · rwa [← Nat.cast_prod, ← Nat.prod_primeFactors_pow_factorization hN]

end Submodule

end TauCeti
