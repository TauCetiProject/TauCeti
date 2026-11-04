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

For a prime `n` this is also a consequence of Sylow theory
(`TauCeti.AddCommGroup.natCard_primaryComponent`).

## Main results

* `TauCeti.AddCommGroup.coprime_index_primaryComponent`: `[A : A[n^∞]]` is prime to `n`.
* `TauCeti.AddCommGroup.dvd_of_prime_dvd_natCard_primaryComponent`: a prime dividing `#A[n^∞]`
  divides `n`.
* `TauCeti.AddCommGroup.natCard_primaryComponent_dvd_of_natCard_dvd` and
  `TauCeti.AddCommGroup.natCard_primaryComponent_eq_of_natCard_eq`: for finite groups, `#A[n^∞]`
  only depends on `#A`.
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
`#A ∣ #B` for finite commutative groups, then `#A[n^∞] ∣ #B[n^∞]`. -/
theorem natCard_primaryComponent_dvd_of_natCard_dvd [Finite A] [Finite B]
    (h : Nat.card A ∣ Nat.card B) (n : ℕ) :
    Nat.card (AddCommGroup.primaryComponent A n) ∣
      Nat.card (AddCommGroup.primaryComponent B n) := by
  -- `#A[n^∞]` divides `#B = #B[n^∞] · [B : B[n^∞]]` and is prime to the index
  have hcop : (Nat.card (AddCommGroup.primaryComponent A n)).Coprime
      (AddCommGroup.primaryComponent B n).index :=
    Nat.coprime_of_dvd fun p hp hpA hpB ↦ hp.not_dvd_one <|
      (coprime_index_primaryComponent (A := B) n).gcd_eq_one ▸
        Nat.dvd_gcd hpB (dvd_of_prime_dvd_natCard_primaryComponent hp hpA)
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [AddSubgroup.card_mul_index]
  exact (AddSubgroup.card_addSubgroup_dvd_card _).trans h

/-- **Finite commutative groups of the same order have `n`-primary components of the same
order.** -/
theorem natCard_primaryComponent_eq_of_natCard_eq [Finite A] [Finite B]
    (h : Nat.card A = Nat.card B) (n : ℕ) :
    Nat.card (AddCommGroup.primaryComponent A n) = Nat.card (AddCommGroup.primaryComponent B n) :=
  Nat.dvd_antisymm (natCard_primaryComponent_dvd_of_natCard_dvd h.dvd n)
    (natCard_primaryComponent_dvd_of_natCard_dvd h.symm.dvd n)

end AddCommGroup

end TauCeti
