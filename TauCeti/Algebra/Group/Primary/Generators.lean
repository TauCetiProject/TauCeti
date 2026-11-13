/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Group.Generators
public import TauCeti.Algebra.Group.Primary.Decomposition

/-!
# The generator number of a finite abelian group

The least number of generators of a finite abelian group is the maximum of the least
numbers for its prime-primary components. We establish this for both Mathlib's `AddGroup.rank`
and `Submodule.spanFinrank` over `ℤ`, without introducing another invariant.
The maximum is taken over the prime divisors of the group order (or equivalently as the supremum
over all primes); for the trivial group the prime-divisor set is empty and the maximum is zero.

## Main statements

* `TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents`
* `AddGroup.rank_eq_sup_primaryComponents`
* `AddGroup.rank_primaryComponent_le`
* `AddGroup.rank_eq_ciSup_primaryComponent`

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

end TauCeti.AddCommGroup

namespace AddGroup

/-- The generator rank `l(A)` of a finite abelian group `A` is the maximum of the generator ranks
`l(A_p)` of its prime-primary components over the prime divisors of `|A|`. -/
theorem rank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    AddGroup.rank A =
      (Nat.card A).primeFactors.sup (fun p ↦
        AddGroup.rank (AddCommGroup.primaryComponent A p)) := by
  rw [AddGroup.rank_eq_spanFinrank_top,
    TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents]
  simp_rw [← AddGroup.rank_eq_spanFinrank_top]
  apply le_antisymm
  · refine Finset.sup_le fun p _ ↦ ?_
    exact Finset.le_sup (f := fun q ↦ AddGroup.rank (AddCommGroup.primaryComponent A q)) p.2
  · refine Finset.sup_le fun p hp ↦ ?_
    exact Finset.le_sup
      (f := fun q : (Nat.card A).primeFactors ↦
        AddGroup.rank (AddCommGroup.primaryComponent A q.1))
      (Finset.mem_univ ⟨p, hp⟩)

/-- For any prime `p`, the generator rank of the `p`-primary component of a finite abelian group
`A` is at most the generator rank of `A`. -/
theorem rank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (AddCommGroup.primaryComponent A p) ≤ AddGroup.rank A := by
  by_cases hmem : p ∈ (Nat.card A).primeFactors
  · rw [rank_eq_sup_primaryComponents A]
    exact Finset.le_sup (f := fun q ↦ AddGroup.rank (AddCommGroup.primaryComponent A q)) hmem
  · have hndvd : ¬ p ∣ Nat.card A := fun hdvd ↦
      hmem (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
    have hcard : Nat.card (AddCommGroup.primaryComponent A p) = 1 := by
      rw [TauCeti.AddCommGroup.natCard_primaryComponent A hp,
        Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
    have : Subsingleton (AddCommGroup.primaryComponent A p) :=
      Nat.card_eq_one_iff_unique.mp hcard |>.1
    simp [AddGroup.rank_eq_zero]

/-- Nikulin's formula `l(A) = max_p l(A_p)` over all primes `p`. -/
theorem rank_eq_ciSup_primaryComponent (A : Type*) [AddCommGroup A] [Finite A] :
    AddGroup.rank A =
      ⨆ p : {p : ℕ // p.Prime}, AddGroup.rank (AddCommGroup.primaryComponent A p.1) := by
  have : Nonempty {p : ℕ // p.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
  have hbdd : BddAbove (Set.range fun p : {p : ℕ // p.Prime} ↦
      AddGroup.rank (AddCommGroup.primaryComponent A p.1)) :=
    ⟨AddGroup.rank A, by rintro _ ⟨p, rfl⟩; exact rank_primaryComponent_le A p.2⟩
  refine le_antisymm ?_ (ciSup_le fun p ↦ rank_primaryComponent_le A p.2)
  rw [rank_eq_sup_primaryComponents A]
  refine Finset.sup_le fun p hp ↦ ?_
  exact le_ciSup hbdd ⟨p, Nat.prime_of_mem_primeFactors hp⟩

end AddGroup
