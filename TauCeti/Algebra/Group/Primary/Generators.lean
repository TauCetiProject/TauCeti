/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Group.Generators
public import TauCeti.Algebra.Group.Primary.Decomposition
public import TauCeti.GroupTheory.Rank
import TauCeti.Algebra.Group.Primary.Card

/-!
# The generator number of a finite abelian group

The least number of generators of a finite abelian group, Nikulin's length `l(A)`, is the maximum
of the least numbers for its prime-primary components. We use the canonical primary decomposition
and state the result both for Mathlib's `Submodule.spanFinrank` over `ℤ` and for Mathlib's
`AddGroup.rank`, which agree by `AddGroup.rank_eq_spanFinrank`. A primary component therefore
never needs more generators than the group.
The maximum is taken over the prime divisors of the group order; for the trivial group the
prime-divisor set is empty and the maximum is zero.

## Main statements

* `TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents`
* `AddGroup.rank_eq_sup_primaryComponents`
* `AddGroup.rank_primaryComponent_le`

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
        (⊤ : Submodule ℤ (_root_.AddCommGroup.primaryComponent A p.val)).spanFinrank) := by
  classical
  let M : (Nat.card A).primeFactors → Type _ :=
    fun p ↦ _root_.AddCommGroup.primaryComponent A p.val
  have hcop : Pairwise fun p q ↦ (Nat.card (M p)).Coprime (Nat.card (M q)) := by
    intro p q hpq
    dsimp only [M]
    have hp := Nat.prime_of_mem_primeFactors p.property
    have hq := Nat.prime_of_mem_primeFactors q.property
    rw [natCard_primaryComponent A hp, natCard_primaryComponent A hq]
    exact ((Nat.coprime_primes hp hq).mpr (by simpa using hpq)).pow _ _
  let e : (∀ p, M p) ≃ₗ[ℤ] A := (primaryDecomposition A).toIntLinearEquiv
  have he := Submodule.spanFinrank_map_eq_of_injective e.toLinearMap e.injective
    (p := ⊤)
  rw [Submodule.map_top, LinearEquiv.range] at he
  exact he.trans (spanFinrank_pi_eq_sup_of_coprime_card M hcop)

end TauCeti.AddCommGroup

namespace AddGroup

/-- **Nikulin's length is local.** The least number of generators `AddGroup.rank A` of a finite
abelian group, Nikulin's `l(A)`, is the maximum of the least numbers of generators of its
prime-primary components over the prime divisors of `|A|`. -/
theorem rank_eq_sup_primaryComponents (A : Type*) [AddCommGroup A] [Finite A] :
    AddGroup.rank A =
      (Nat.card A).primeFactors.sup (fun p ↦
        AddGroup.rank (AddCommGroup.primaryComponent A p)) := by
  have h := TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents A
  simp only [← AddGroup.rank_eq_spanFinrank, Finset.univ_eq_attach] at h
  exact h.trans (Finset.sup_attach (Nat.card A).primeFactors
    (fun p ↦ AddGroup.rank (AddCommGroup.primaryComponent A p)))

/-- A prime-primary component of a finite abelian group needs at most as many generators as the
group itself. -/
theorem rank_primaryComponent_le (A : Type*) [AddCommGroup A] [Finite A] {p : ℕ}
    (hp : p.Prime) :
    AddGroup.rank (AddCommGroup.primaryComponent A p) ≤ AddGroup.rank A := by
  by_cases h : p ∣ Nat.card A
  · rw [rank_eq_sup_primaryComponents A]
    exact Finset.le_sup (f := fun p ↦ AddGroup.rank (AddCommGroup.primaryComponent A p))
      (Nat.mem_primeFactors.mpr ⟨hp, h, Nat.card_pos.ne'⟩)
  · have : Subsingleton (AddCommGroup.primaryComponent A p) :=
      (Nat.card_eq_one_iff_unique.mp (by
        rw [TauCeti.AddCommGroup.natCard_primaryComponent A hp,
          Nat.factorization_eq_zero_of_not_dvd h, pow_zero])).1
    simp [AddGroup.rank_eq_zero]

end AddGroup
