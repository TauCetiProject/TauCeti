/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Associated elements and principal ideals in local rings

In an integral domain, two elements divide each other—equivalently, generate the same principal
ideal—if and only if they differ by a unit (`associated_of_dvd_dvd` and
`Ideal.span_singleton_eq_span_singleton`). In an arbitrary commutative ring with zero divisors
this can fail, as for `x` and `x * z` in `k[x, z] ⧸ (x * (1 - z ^ 2))`. In any local ring mutual
divisibility still characterizes `Associated` without a domain or commutativity hypothesis, and in
a commutative local ring two elements generate the same principal ideal if and only if they are
associated. In particular, invariants defined from a generator of a principal ideal of a local ring
(such as its maximal ideal) can be shown independent of the chosen generator by proving invariance
under multiplication by a unit.

## Main results

* `TauCeti.IsLocalRing.associated_of_dvd_dvd`: in a local ring, mutual divisibility implies
  `Associated`.
* `TauCeti.IsLocalRing.associated_iff_dvd_dvd`: characterization of `Associated` by mutual
  divisibility in a local ring.
* `TauCeti.IsLocalRing.span_singleton_eq_span_singleton`: two elements of a commutative local ring
  generate the same principal ideal if and only if they are associated.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

section Ring

variable {R : Type*} [Ring R] [IsLocalRing R]

/-- In a local ring, two elements that divide each other on the right are associated, with no
domain or commutativity hypothesis. -/
theorem associated_of_dvd_dvd {a b : R} (hab : a ∣ b) (hba : b ∣ a) : Associated a b := by
  obtain ⟨c, rfl⟩ := hab
  obtain ⟨d, hd⟩ := hba
  by_cases hc : IsUnit c
  · exact ⟨hc.unit, rfl⟩
  · have hu : IsUnit (1 - c * d) :=
      (isUnit_or_isUnit_one_sub_self (c * d)).resolve_left fun h ↦ hc (isUnit_of_mul_isUnit_left h)
    have ha0 : a * (1 - c * d) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← hd, sub_self]
    obtain rfl : a = 0 := hu.mul_left_eq_zero.mp ha0
    rw [zero_mul]

/-- In a local ring, two elements are associated if and only if each divides the other. -/
theorem associated_iff_dvd_dvd {a b : R} : Associated a b ↔ a ∣ b ∧ b ∣ a :=
  ⟨fun h ↦ ⟨h.dvd, h.symm.dvd⟩, fun ⟨hab, hba⟩ ↦ associated_of_dvd_dvd hab hba⟩

end Ring

/-- In a commutative local ring, two elements generate the same principal ideal if and only if
they are associated. -/
theorem span_singleton_eq_span_singleton {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} :
    Ideal.span {a} = Ideal.span {b} ↔ Associated a b := by
  rw [le_antisymm_iff, Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, and_comm, ← associated_iff_dvd_dvd]

end TauCeti.IsLocalRing
