/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries

/-!
# Scalar towers for Laurent series

The `R`-algebra structure on `R⸨X⸩` is the one inherited from `R⟦X⟧` through
`HahnSeries.ofPowerSeries`, so its scalar action is multiplication by the image of a constant
power series. This is propositionally, but not definitionally, equal to the coefficientwise
action `HahnSeries.instSMul` found by default.

This file records that the algebra actions form a scalar tower `R → R⟦X⟧ → R⸨X⸩`. This is what
fraction-field constructions such as `IsFractionRing.algEquivOfAlgEquiv` require to extend an
`R`-algebra equivalence with `R⟦X⟧` to one with `R⸨X⸩`.

## Main results

* `TauCeti.LaurentSeries.isScalarTower_powerSeries`: the algebra actions of `R` on `R⟦X⟧` and
  `R⸨X⸩` form a scalar tower.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommSemiring R]

/-- The constant scalars on `R⸨X⸩` factor through `R⟦X⟧`. The scalar actions are stated through
the algebra structures, since the `R`-algebra structure on `R⸨X⸩` is the one inherited from
`R⟦X⟧` rather than the coefficientwise action. -/
instance isScalarTower_powerSeries :
    @IsScalarTower R R⟦X⟧ R⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq' rfl

end TauCeti.LaurentSeries
