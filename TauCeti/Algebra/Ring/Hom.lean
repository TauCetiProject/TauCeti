/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute

/-!
# Multiplicative maps into rings

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.

A ring homomorphism applied entrywise to a scalar multiple `c • v` of a family gives
`f c • (f ∘ v)`.

## Main results

* `MonoidHom.map_neg_one_eq_one_or_eq_neg_one`: the image of `-1` is `1` or `-1`.
* `RingHom.comp_smul`: `f ∘ (c • v) = f c • (f ∘ v)`.
-/

public section

namespace MonoidHom

/-- A multiplicative map into a ring without zero divisors sends `-1` to `1` or `-1`.
Only distributive negation and a multiplicative identity are required in the source; the target
ring need not be associative. -/
theorem map_neg_one_eq_one_or_eq_neg_one {M R : Type*} [MulOneClass M] [HasDistribNeg M]
    [NonAssocRing R] [NoZeroDivisors R] (f : M →* R) :
    f (-1) = 1 ∨ f (-1) = -1 :=
  mul_self_eq_one_iff.mp (by rw [← map_mul]; simp)

end MonoidHom

namespace RingHom

variable {R S ι : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

/-- A ring homomorphism applied entrywise to `c • v` gives `f c • (f ∘ v)`. -/
theorem comp_smul (f : R →+* S) (c : R) (v : ι → R) : f ∘ (c • v) = f c • (f ∘ v) :=
  funext fun _ ↦ map_mul f _ _

end RingHom
