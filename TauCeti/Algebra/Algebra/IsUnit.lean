/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Scalars mapping to units of an algebra

Let `A` be an `R`-algebra, not necessarily commutative. The image of `R` in `A` is central, so if
`a * b` maps to a unit of `A` then so do `a` and `b`. Hence the set of scalars mapping to units is
closed under divisors as well as under powers. For `A = Module.End R M` these say that divisors
and powers of a scalar acting invertibly on `M` act invertibly. For instance, the canonical map
`M → M_c` to a localization away from `c` extends to `M_a → M_c` whenever `a ∣ c`.

## Main statements

* `IsUnit.algebraMap_of_dvd`: a divisor of a scalar mapping to a unit maps to a unit.
* `IsUnit.algebraMap_powers`: the powers of a scalar mapping to a unit map to units.
-/

public section

namespace IsUnit

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- A divisor of a scalar mapping to a unit of an `R`-algebra maps to a unit. -/
theorem algebraMap_of_dvd {a c : R} (hc : IsUnit (algebraMap R A c)) (hac : a ∣ c) :
    IsUnit (algebraMap R A a) := by
  obtain ⟨b, rfl⟩ := hac
  rw [map_mul, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at hc
  exact hc.1

/-- The powers of a scalar mapping to a unit of an `R`-algebra map to units. -/
theorem algebraMap_powers {a : R} (h : IsUnit (algebraMap R A a)) (x : Submonoid.powers a) :
    IsUnit (algebraMap R A x) := by
  obtain ⟨_, k, rfl⟩ := x
  simpa using h.pow k

end IsUnit
