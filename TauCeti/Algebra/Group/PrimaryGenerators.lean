/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Group.Generators
public import TauCeti.Algebra.Group.PrimaryDecomposition

/-!
# The generator number of a finite abelian group

The least number of generators of a finite abelian group is the maximum of the least
numbers for its prime-primary components. We use the canonical primary decomposition
and Mathlib's `Submodule.spanFinrank` over `ℤ`, without introducing another invariant.
The maximum is taken over the prime divisors of the group order; for the trivial group
this set is empty and the maximum is zero.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace TauCeti.AddCommGroup

/-- The least number of generators of a finite abelian group is the maximum of the
least numbers for its prime-primary components. -/
theorem spanFinrank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    (⊤ : Submodule ℤ A).spanFinrank =
      Finset.univ.sup (fun p : (Nat.card A).primeFactors ↦
        (⊤ : Submodule ℤ (_root_.AddCommGroup.primaryComponent A p.1)).spanFinrank) := by
  classical
  let M : (Nat.card A).primeFactors → Type _ :=
    fun p ↦ _root_.AddCommGroup.primaryComponent A p.1
  have hcop : Pairwise fun p q ↦ (Nat.card (M p)).Coprime (Nat.card (M q)) := by
    intro p q hpq
    have : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have : Fact q.1.Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    exact IsPGroup.coprime_card_of_ne p.1 q.1 (by simpa using hpq)
      (_root_.CommGroup.primaryComponent (Multiplicative A) p.1)
      (_root_.CommGroup.primaryComponent (Multiplicative A) q.1)
      (_root_.CommGroup.primaryComponent.isPGroup (G := Multiplicative A))
      (_root_.CommGroup.primaryComponent.isPGroup (G := Multiplicative A))
  let e : (∀ p, M p) ≃ₗ[ℤ] A := (primaryDecomposition A).toIntLinearEquiv
  have he := Submodule.spanFinrank_map_eq_of_injective e.toLinearMap e.injective
    (p := ⊤)
  rw [Submodule.map_top, LinearEquiv.range] at he
  exact he.trans (spanFinrank_pi_eq_sup_of_coprime_card M hcop)

end TauCeti.AddCommGroup
