/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Group.Generators
public import TauCeti.Algebra.Group.Primary.Decomposition

/-!
# The generator number of a finite abelian group

The least number of generators of a finite abelian group is the maximum of the least
numbers for its prime-primary components. We record this for both Mathlib's
`Submodule.spanFinrank` over `ℤ` and `AddGroup.rank`, using the canonical primary decomposition.
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
    dsimp only [M]
    have hp := Nat.prime_of_mem_primeFactors p.2
    have hq := Nat.prime_of_mem_primeFactors q.2
    rw [natCard_primaryComponent A hp, natCard_primaryComponent A hq]
    exact ((Nat.coprime_primes hp hq).mpr (by simpa using hpq)).pow _ _
  let e : (∀ p, M p) ≃ₗ[ℤ] A := (primaryDecomposition A).toIntLinearEquiv
  have he := Submodule.spanFinrank_map_eq_of_injective e.toLinearMap e.injective
    (p := ⊤)
  rw [Submodule.map_top, LinearEquiv.range] at he
  exact he.trans (spanFinrank_pi_eq_sup_of_coprime_card M hcop)

/-- The minimal number of generators `AddGroup.rank A` of a finite abelian group `A` equals the
supremum of `AddGroup.rank` over its prime-primary components. -/
theorem rank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    AddGroup.rank A =
      Finset.univ.sup (fun p : (Nat.card A).primeFactors ↦
        AddGroup.rank (_root_.AddCommGroup.primaryComponent A p.1)) := by
  rw [AddGroup.rank_eq_spanFinrank_top, spanFinrank_eq_sup_primaryComponents A]
  exact Finset.sup_congr rfl fun p _ ↦
    (AddGroup.rank_eq_spanFinrank_top (_root_.AddCommGroup.primaryComponent A p.1)).symm

/-- For every prime `p`, the rank of the `p`-primary component of a finite abelian group `A` is at
most `AddGroup.rank A`. -/
theorem rank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (_root_.AddCommGroup.primaryComponent A p) ≤ AddGroup.rank A := by
  by_cases hmem : p ∈ (Nat.card A).primeFactors
  · rw [rank_eq_sup_primaryComponents A]
    exact Finset.le_sup (f := fun q : (Nat.card A).primeFactors ↦
      AddGroup.rank (_root_.AddCommGroup.primaryComponent A q.1)) (Finset.mem_univ ⟨p, hmem⟩)
  · have hfac : (Nat.card A).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦
        hmem (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
    have hcard : Nat.card (_root_.AddCommGroup.primaryComponent A p) = 1 := by
      rw [natCard_primaryComponent A hp, hfac, pow_zero]
    have : Subsingleton (_root_.AddCommGroup.primaryComponent A p) :=
      Finite.card_le_one_iff_subsingleton.mp hcard.le
    rw [AddGroup.rank_eq_zero]
    exact Nat.zero_le _

/-- For a finite abelian group `A`, `AddGroup.rank A ≤ n` if and only if every prime-primary
component has rank at most `n`. -/
theorem rank_le_iff_forall_prime_primaryComponent (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) :
    AddGroup.rank A ≤ n ↔
      ∀ p : ℕ, p.Prime → AddGroup.rank (_root_.AddCommGroup.primaryComponent A p) ≤ n := by
  refine ⟨fun h p hp ↦ (rank_primaryComponent_le A hp).trans h, fun h ↦ ?_⟩
  rw [rank_eq_sup_primaryComponents A]
  exact Finset.sup_le fun p _ ↦ h p.1 (Nat.prime_of_mem_primeFactors p.2)

end TauCeti.AddCommGroup
