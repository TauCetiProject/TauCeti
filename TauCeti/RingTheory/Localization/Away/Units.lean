/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Descending units from the complement of a prime divisor

In a domain, an element not divisible by a prime element `p` is a unit if it becomes a unit
after inverting `p`. This allows an invertibility condition established off a prime divisor
to descend to the original ring, provided the element does not vanish along that divisor.
-/

public section

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := S) p).mp hx
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow hp n).mp hn
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

end Prime
