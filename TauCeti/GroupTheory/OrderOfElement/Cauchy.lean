/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# The order of a finite group is invertible when the orders of its elements are

Let `G` be a finite group and `k` a commutative semiring. The order of every element of `G`
divides `#G`, and by Cauchy's theorem every prime dividing `#G` is the order of some element. So
`#G` is a unit of `k` exactly when the order of every element of `G` is a unit of `k`
(`TauCeti.isUnit_natCard_iff_forall_isUnit_orderOf`). For instance `#G` is invertible in a field
of characteristic `p` exactly when `G` has no element of order `p`.

The elementwise condition makes sense for infinite groups too, which is how it is used for locally
finite groups: there it controls the orders of all finite subgroups at once.

## Main results

* `TauCeti.isUnit_natCard_iff_forall_isUnit_orderOf`: `#G` is a unit of `k` exactly when the
  order of every element of `G` is.
-/

public section

namespace TauCeti

/-- **The order of a finite group is invertible exactly when the orders of its elements are.** For
a finite group `G` and a commutative semiring `k`, `#G` is a unit of `k` exactly when the order of
every element of `G` is a unit of `k`. -/
theorem isUnit_natCard_iff_forall_isUnit_orderOf {G k : Type*} [Group G] [Finite G]
    [CommSemiring k] :
    IsUnit (Nat.card G : k) ↔ ∀ g : G, IsUnit (orderOf g : k) := by
  refine ⟨fun h g ↦ isUnit_of_dvd_unit (Nat.cast_dvd_cast (orderOf_dvd_natCard g)) h, fun h ↦ ?_⟩
  -- every divisor of `#G` is a unit: its prime factors are orders of elements, by Cauchy
  suffices ∀ n, n ∣ Nat.card G → IsUnit (n : k) from this _ dvd_rfl
  intro n
  induction n using induction_on_primes with
  | zero => exact fun hn ↦ absurd (Nat.eq_zero_of_zero_dvd hn) Nat.card_pos.ne'
  | one => exact fun _ ↦ by simp
  | prime_mul p a hp ih =>
    intro hn
    have := Fact.mk hp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (dvd_of_mul_right_dvd hn)
    rw [Nat.cast_mul]
    exact (hg ▸ h g).mul (ih (dvd_of_mul_left_dvd hn))

end TauCeti
