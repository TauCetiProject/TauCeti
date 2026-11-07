/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import TauCeti.Algebra.Group.End

/-!
# Prime-order automorphisms of small finite groups

An automorphism of prime order `p` of a group with `p + 1` elements cycles through
all nonidentity elements. These elements therefore have the same order. Cauchy's
theorem excludes such an automorphism when two distinct primes divide the group order.

This rules out automorphisms of order 11 or 23 in groups of order 12 or 24,
respectively, as needed to exclude regular normal subgroups in Mathieu actions.
-/

public section

namespace MulAut

variable {G : Type*} [Group G]

/-- An automorphism of prime order `p` of a group with `p + 1` elements gives all nonidentity
elements the same order. -/
theorem orderOf_eq_of_card_eq_succ (f : MulAut G) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p + 1) (hf : orderOf f = p)
    {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) : orderOf x = orderOf y := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  let : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hcard
  have hinj : Function.Injective (toPerm G) := MulEquiv.toEquiv_injective
  have horder : orderOf (toPerm G f) = p := (orderOf_injective (toPerm G) hinj f).trans hf
  have hcycle : (toPerm G f).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (horder ▸ hp) (by
      rw [horder, hcard]
      have := hp.two_le
      omega)
  have hsub : (toPerm G f).support ⊆ Finset.univ.erase 1 := by
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rintro rfl
    exact Equiv.Perm.mem_support.mp hz (by rw [toPerm_apply, map_one])
  have hsupp : (toPerm G f).support = Finset.univ.erase 1 :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [← hcycle.orderOf, horder]
      simp [Finset.card_erase_of_mem, hcard])
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq (x := x) (y := y)
    (Equiv.Perm.mem_support.mp (by rw [hsupp]; simp [hx]))
    (Equiv.Perm.mem_support.mp (by rw [hsupp]; simp [hy]))
  have hxy : (f ^ n) x = y := by rwa [← toPerm_apply, map_pow]
  exact ((f ^ n).orderOf_eq x).symm.trans (congrArg orderOf hxy)

/-- Distinct prime divisors exclude a prime-order automorphism on `p + 1` elements. -/
theorem orderOf_ne_prime_of_card_eq_succ (f : MulAut G) {p q r : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p + 1)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqdvd : q ∣ Nat.card G) (hrdvd : r ∣ Nat.card G) : orderOf f ≠ p := by
  intro hf
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hx1 : x ≠ 1 := (orderOf_eq_prime_iff.mp hx).2
  have hy1 : y ≠ 1 := (orderOf_eq_prime_iff.mp hy).2
  exact hqr (hx.symm.trans ((orderOf_eq_of_card_eq_succ f hp hcard hf hx1 hy1).trans hy))

end MulAut
