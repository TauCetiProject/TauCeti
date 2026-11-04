/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Irreducible elements and the maximal ideal of a local ring

In a commutative local semiring, every nonunit belongs to the unique maximal ideal. Consequently,
every irreducible element lies in the maximal ideal and cannot be factored as a product of two
elements of the maximal ideal.

## Main results

* `Irreducible.mem_maximalIdeal`: an irreducible element of a local ring lies in its maximal ideal.
* `Irreducible.ne_mul_of_mem_maximalIdeal`: an irreducible element of a local ring is never the
  product of two elements of the maximal ideal.
-/

public section

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
