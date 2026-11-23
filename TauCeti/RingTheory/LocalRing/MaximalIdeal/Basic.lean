/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Elements in the maximal ideal of a local ring

In a commutative local semiring, every nonunit belongs to the unique maximal ideal
`IsLocalRing.maximalIdeal R`. In particular, any element that fails to divide another lies in the
maximal ideal (`TauCeti.IsLocalRing.mem_maximalIdeal_of_not_dvd`), and every irreducible element
lies in `IsLocalRing.maximalIdeal R` (`Irreducible.mem_maximalIdeal`) and is never a product of two
elements of `IsLocalRing.maximalIdeal R` (`Irreducible.ne_mul_of_mem_maximalIdeal`).
-/

public section

namespace TauCeti.IsLocalRing

/-- In a commutative local semiring, any element that fails to divide another lies in the maximal
ideal. -/
theorem mem_maximalIdeal_of_not_dvd {R : Type*} [CommSemiring R] [IsLocalRing R] {f a : R}
    (hfa : ¬ f ∣ a) : f ∈ _root_.IsLocalRing.maximalIdeal R :=
  of_not_not fun h ↦ hfa (_root_.IsLocalRing.notMem_maximalIdeal.mp h).dvd

end TauCeti.IsLocalRing

namespace Irreducible

variable {R : Type*} [CommSemiring R] [IsLocalRing R]

/-- Every irreducible element of a local ring belongs to its maximal ideal. -/
theorem mem_maximalIdeal {c : R} (hc : Irreducible c) : c ∈ IsLocalRing.maximalIdeal R :=
  (IsLocalRing.mem_maximalIdeal c).mpr hc.not_isUnit

/-- An irreducible element of a local ring cannot be written as a product of two elements of the
maximal ideal. -/
theorem ne_mul_of_mem_maximalIdeal {c x y : R} (hc : Irreducible c)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hy : y ∈ IsLocalRing.maximalIdeal R) :
    c ≠ x * y := fun h ↦
  (hc.isUnit_or_isUnit h).elim ((IsLocalRing.mem_maximalIdeal x).mp hx)
    ((IsLocalRing.mem_maximalIdeal y).mp hy)

end Irreducible
