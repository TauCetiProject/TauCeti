/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Torsion

import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Orders of primary components of finite commutative groups

Let `A` be a commutative group and `n` a natural number, and write `A[n^∞]` for Mathlib's
`AddCommGroup.primaryComponent A n`, the subgroup of elements killed by some power of `n` (`n`
need not be prime). For a finite commutative group `A`, the order of `A[n^∞]` is the `n`-part of
`#A`: its prime factors divide `n`, and the index `[A : A[n^∞]]` is prime to `n` (both by Cauchy's
theorem). So finite groups of the same order have `n`-primary components of the same order.

For a prime `p` this pins the order down: `#A[p^∞]` is the full power of `p` dividing `#A`.

## Main results

* `TauCeti.AddCommGroup.coprime_index_primaryComponent`: `[A : A[n^∞]]` is prime to `n`.
* `TauCeti.AddCommGroup.dvd_of_prime_dvd_natCard_primaryComponent`: a prime dividing `#A[n^∞]`
  divides `n`.
* `TauCeti.AddCommGroup.natCard_primaryComponent_dvd_of_natCard_dvd` and
  `TauCeti.AddCommGroup.natCard_primaryComponent_eq_of_natCard_eq`: for finite groups, `#A[n^∞]`
  only depends on `#A`.
* `TauCeti.AddCommGroup.natCard_primaryComponent`: for a prime `p` and a finite group,
  `#A[p^∞] = p ^ v_p(#A)`.
* `TauCeti.AddCommGroup.natCard_dvd_of_natCard_primaryComponent_dvd` and
  `TauCeti.AddCommGroup.natCard_eq_of_natCard_primaryComponent_eq`: the converses, for finite
  groups: `#G ∣ #H` (resp. `#G = #H`) if this holds for every prime-primary component.
-/

public section

namespace TauCeti

namespace AddCommGroup

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **The index of the `n`-primary component is prime to `n`** whenever it is finite. -/
theorem coprime_index_primaryComponent (n : ℕ)
    [(AddCommGroup.primaryComponent A n).FiniteIndex] :
    (AddCommGroup.primaryComponent A n).index.Coprime n := by
  -- a prime `p ∣ n` dividing the index is the order of a class `x` modulo `A[n^∞]` (Cauchy), but
  -- then `p x`, hence `n x`, lies in `A[n^∞]`, and so does `x`
  refine Nat.coprime_of_dvd fun p hp hpi hpn ↦ ?_
  have := Fact.mk hp
  rw [AddSubgroup.index_eq_card] at hpi
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpi
  induction x using QuotientAddGroup.induction_on with | H x => ?_
  obtain ⟨m, rfl⟩ := hpn
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp <|
    (QuotientAddGroup.eq_zero_iff (p • x)).mp <| by
      rw [QuotientAddGroup.mk_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : (x : A ⧸ AddCommGroup.primaryComponent A (p * m)) = 0 :=
    (QuotientAddGroup.eq_zero_iff x).mpr <| AddCommGroup.mem_primaryComponent.mpr ⟨k + 1, by
      have : (p * m) ^ (k + 1) • x = m • (p * m) ^ k • p • x := by
        rw [smul_smul, smul_smul]
        ring_nf
      rw [this, hk, nsmul_zero]⟩
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

/-- **The order of the `n`-primary component has only prime factors dividing `n`** whenever it is
finite. -/
theorem dvd_of_prime_dvd_natCard_primaryComponent {n p : ℕ}
    [Finite (AddCommGroup.primaryComponent A n)] (hp : p.Prime)
    (h : p ∣ Nat.card (AddCommGroup.primaryComponent A n)) : p ∣ n := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
  refine hp.dvd_of_dvd_pow (n := k) ?_
  rw [← hx]
  exact addOrderOf_dvd_of_nsmul_eq_zero (Subtype.ext hk)

/-- **The order of the `n`-primary component is monotone in the order of the group**: if
`#A ∣ #B` for commutative groups with `B` finite, then `#A[n^∞] ∣ #B[n^∞]` (`A` is then finite
too). -/
theorem natCard_primaryComponent_dvd_of_natCard_dvd [Finite B]
    (h : Nat.card A ∣ Nat.card B) (n : ℕ) :
    Nat.card (AddCommGroup.primaryComponent A n) ∣
      Nat.card (AddCommGroup.primaryComponent B n) := by
  have : Finite A :=
    Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero (Nat.card_pos (α := B)).ne' h)
  -- `#A[n^∞]` divides `#B = #B[n^∞] · [B : B[n^∞]]` and is prime to the index
  have hcop : (Nat.card (AddCommGroup.primaryComponent A n)).Coprime
      (AddCommGroup.primaryComponent B n).index :=
    Nat.coprime_of_dvd fun p hp hpA hpB ↦ hp.not_dvd_one <|
      (coprime_index_primaryComponent (A := B) n).gcd_eq_one ▸
        Nat.dvd_gcd hpB (dvd_of_prime_dvd_natCard_primaryComponent hp hpA)
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [AddSubgroup.card_mul_index]
  exact (AddSubgroup.card_addSubgroup_dvd_card _).trans h

/-- **Commutative groups of the same finite order have `n`-primary components of the same
order.** -/
theorem natCard_primaryComponent_eq_of_natCard_eq [Finite B]
    (h : Nat.card A = Nat.card B) (n : ℕ) :
    Nat.card (AddCommGroup.primaryComponent A n) =
      Nat.card (AddCommGroup.primaryComponent B n) := by
  have : Finite A := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact Nat.dvd_antisymm (natCard_primaryComponent_dvd_of_natCard_dvd h.dvd n)
      (natCard_primaryComponent_dvd_of_natCard_dvd h.symm.dvd n)

/-- **The order of a prime-primary component** of a finite commutative group is the corresponding
prime-power factor of the group order. -/
theorem natCard_primaryComponent (A : Type*) [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime) :
    Nat.card (AddCommGroup.primaryComponent A p) = p ^ (Nat.card A).factorization p := by
  -- `#A[p^∞]` is a power of `p`, and the complementary factor `[A : A[p^∞]]` is prime to `p`
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (AddCommGroup.primaryComponent A p) = p ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd ↦
      (Nat.prime_dvd_prime_iff_eq hq hp).mp (dvd_of_prime_dvd_natCard_primaryComponent hq hqd)⟩
  have hi : (AddCommGroup.primaryComponent A p).index.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (hp.coprime_iff_not_dvd.mp (coprime_index_primaryComponent p).symm)
  rw [← (AddCommGroup.primaryComponent A p).card_mul_index, hk,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) AddSubgroup.index_ne_zero_of_finite]
  simp [hp.factorization_pow, hi]

/-- **If the `p`-primary component of `G` has order dividing that of `H` for every prime `p`, then
`#G ∣ #H`** for finite commutative groups. The order of the `p`-primary component is the `p`-part
of the group order (`TauCeti.AddCommGroup.natCard_primaryComponent`). -/
theorem natCard_dvd_of_natCard_primaryComponent_dvd {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] [Finite G] [Finite H]
    (h : ∀ p : ℕ, p.Prime → Nat.card (AddCommGroup.primaryComponent G p) ∣
      Nat.card (AddCommGroup.primaryComponent H p)) :
    Nat.card G ∣ Nat.card H := by
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
  intro p hp
  refine (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 ?_
  rw [← natCard_primaryComponent G hp]
  exact (h p hp).trans (AddSubgroup.card_addSubgroup_dvd_card _)

/-- **Finite commutative groups whose `p`-primary components have the same order for every prime
`p` have the same order.** This is the converse of
`TauCeti.AddCommGroup.natCard_primaryComponent_eq_of_natCard_eq`. -/
theorem natCard_eq_of_natCard_primaryComponent_eq {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] [Finite G] [Finite H]
    (h : ∀ p : ℕ, p.Prime → Nat.card (AddCommGroup.primaryComponent G p) =
      Nat.card (AddCommGroup.primaryComponent H p)) :
    Nat.card G = Nat.card H :=
  Nat.dvd_antisymm (natCard_dvd_of_natCard_primaryComponent_dvd fun p hp ↦ (h p hp).dvd)
    (natCard_dvd_of_natCard_primaryComponent_dvd fun p hp ↦ (h p hp).symm.dvd)

end AddCommGroup

end TauCeti
