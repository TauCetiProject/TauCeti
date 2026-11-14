/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Generators
public import TauCeti.GroupTheory.Rank

/-!
# Group rank and primary components of a finite abelian group

For a finite abelian group `A`, its minimal number of generators `AddGroup.rank A` equals the
maximum of `AddGroup.rank (AddCommGroup.primaryComponent A p)` over the prime divisors `p` of
`Nat.card A`. For primes not dividing `Nat.card A`, the primary component is trivial and has rank
`0`, so upper bounds and strict inequalities on `AddGroup.rank A` reduce uniformly to all primes.

## Main statements

* `AddGroup.rank_eq_sup_primaryComponents`: `AddGroup.rank A` is the supremum of the ranks of its
  prime-primary components over `(Nat.card A).primeFactors`.
* `AddGroup.rank_primaryComponent_eq_zero_of_not_dvd`: for a prime `p` not dividing `Nat.card A`,
  `AddCommGroup.primaryComponent A p` has rank `0`.
* `AddGroup.rank_primaryComponent_le`: every prime-primary component has rank at most
  `AddGroup.rank A`.
* `AddGroup.rank_le_iff_forall_prime_primaryComponent`: `AddGroup.rank A ≤ n` if and only if every
  prime-primary component has rank at most `n`.
* `AddGroup.lt_rank_iff_exists_prime_primaryComponent`: `n < AddGroup.rank A` if and only if some
  prime-primary component has rank strictly greater than `n`.
* `AddGroup.exists_prime_rank_primaryComponent_eq`: when `A` is nontrivial, some prime divisor of
  `Nat.card A` achieves `AddGroup.rank A`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* D. Gorenstein, *Finite Groups*, Chapter 1.
-/

public section

namespace AddGroup

/-- An additive equivalence of abelian groups restricts to an additive equivalence between their
`n`-primary components, and therefore preserves their ranks when finitely generated. -/
theorem rank_primaryComponent_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℕ) [AddGroup.FG (AddCommGroup.primaryComponent A n)]
    [AddGroup.FG (AddCommGroup.primaryComponent B n)] :
    AddGroup.rank (AddCommGroup.primaryComponent A n) =
      AddGroup.rank (AddCommGroup.primaryComponent B n) := by
  let e' : AddCommGroup.primaryComponent A n ≃+ AddCommGroup.primaryComponent B n :=
    { toFun := fun x ↦ ⟨e x, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      invFun := fun y ↦ ⟨e.symm y, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y)
      map_add' := fun x y ↦ Subtype.ext (map_add e (x : A) (y : A)) }
  exact AddGroup.rank_congr e'

/-- The minimal number of generators of a finite abelian group is the maximum of the minimal
numbers of generators of its prime-primary components. For the trivial group, the prime-factor
index set is empty and both sides vanish. -/
theorem rank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    AddGroup.rank A =
      Finset.univ.sup fun p : (Nat.card A).primeFactors ↦
        AddGroup.rank (AddCommGroup.primaryComponent A p.1) := by
  simp_rw [AddGroup.rank_eq_spanFinrank_top]
  exact TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents A

/-- If a prime `p` does not divide `Nat.card A`, the `p`-primary component of `A` is trivial and
therefore has rank `0`. -/
theorem rank_primaryComponent_eq_zero_of_not_dvd (A : Type*) [AddCommGroup A] [Finite A]
    {p : ℕ} (hp : p.Prime) (hndvd : ¬ p ∣ Nat.card A) :
    AddGroup.rank (AddCommGroup.primaryComponent A p) = 0 := by
  have hcard : Nat.card (AddCommGroup.primaryComponent A p) = 1 := by
    rw [TauCeti.AddCommGroup.natCard_primaryComponent A hp,
      Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
  have : Subsingleton (AddCommGroup.primaryComponent A p) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  exact AddGroup.rank_eq_zero _

/-- For every prime `p`, the rank of the `p`-primary component of a finite abelian group `A` is at
most `AddGroup.rank A`. -/
theorem rank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (AddCommGroup.primaryComponent A p) ≤ AddGroup.rank A := by
  by_cases hpA : p ∣ Nat.card A
  · rw [rank_eq_sup_primaryComponents A]
    let q : (Nat.card A).primeFactors := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩⟩
    exact Finset.le_sup (f := fun r : (Nat.card A).primeFactors ↦
      AddGroup.rank (AddCommGroup.primaryComponent A r.1)) (Finset.mem_univ q)
  · rw [rank_primaryComponent_eq_zero_of_not_dvd A hp hpA]
    exact Nat.zero_le _

/-- `AddGroup.rank A ≤ n` holds if and only if every prime-primary component of `A` has rank at
most `n`. -/
theorem rank_le_iff_forall_prime_primaryComponent (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) :
    AddGroup.rank A ≤ n ↔
      ∀ p : ℕ, p.Prime → AddGroup.rank (AddCommGroup.primaryComponent A p) ≤ n := by
  refine ⟨fun h p hp ↦ (rank_primaryComponent_le A hp).trans h, fun h ↦ ?_⟩
  rw [rank_eq_sup_primaryComponents A]
  exact Finset.sup_le fun p _ ↦ h p.1 (Nat.prime_of_mem_primeFactors p.2)

/-- `n < AddGroup.rank A` holds if and only if some prime-primary component of `A` has rank
strictly greater than `n`. -/
theorem lt_rank_iff_exists_prime_primaryComponent (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) :
    n < AddGroup.rank A ↔
      ∃ p : ℕ, p.Prime ∧ n < AddGroup.rank (AddCommGroup.primaryComponent A p) := by
  rw [← not_le, rank_le_iff_forall_prime_primaryComponent]
  push Not
  rfl

/-- For a nontrivial finite abelian group `A`, some prime divisor `p` of `Nat.card A` attains
`AddGroup.rank A = AddGroup.rank (AddCommGroup.primaryComponent A p)`. -/
theorem exists_prime_rank_primaryComponent_eq (A : Type*) [AddCommGroup A] [Finite A]
    [Nontrivial A] :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card A ∧
      AddGroup.rank A = AddGroup.rank (AddCommGroup.primaryComponent A p) := by
  have h1 : 1 < Nat.card A := Finite.one_lt_card
  obtain ⟨q, hq, hqA⟩ := Nat.exists_prime_and_dvd h1.ne'
  have hne : (Finset.univ : Finset (Nat.card A).primeFactors).Nonempty :=
    ⟨⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqA, Nat.card_pos.ne'⟩⟩, Finset.mem_univ _⟩
  obtain ⟨p, _, hpmax⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun r : (Nat.card A).primeFactors ↦ AddGroup.rank (AddCommGroup.primaryComponent A r.1))
  exact ⟨p.1, Nat.prime_of_mem_primeFactors p.2, Nat.dvd_of_mem_primeFactors p.2,
    (rank_eq_sup_primaryComponents A).trans hpmax⟩

-- Concrete checks: `0`, `ℤ/6`, `(ℤ/2)²`, and `(ℤ/2)² × ℤ/3`.
example : AddGroup.rank PUnit = 0 := AddGroup.rank_eq_zero PUnit

example : AddGroup.rank (ZMod 6) = 1 := AddGroup.rank_zmod_of_ne_one (by decide)

example : AddGroup.rank (Fin 2 → ZMod 2) = 2 := by
  simpa using AddGroup.rank_pi_zmod_prime_pow (Fin 2) (k := 1) Nat.prime_two Nat.one_pos

example : AddGroup.rank ((Fin 2 → ZMod 2) × ZMod 3) = 2 := by
  have hcop : (Nat.card (Fin 2 → ZMod 2)).Coprime (Nat.card (ZMod 3)) := by
    simpa using (by decide : Nat.Coprime 4 3)
  rw [AddGroup.rank_prod_eq_max_of_coprime_card _ _ hcop,
    show AddGroup.rank (Fin 2 → ZMod 2) = 2 by
      simpa using AddGroup.rank_pi_zmod_prime_pow (Fin 2) (k := 1) Nat.prime_two Nat.one_pos,
    AddGroup.rank_zmod_of_ne_one (by decide)]
  rfl

end AddGroup
