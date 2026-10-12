/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Substituting into the binomial series

Mathlib substitutes a power series `b` with nilpotent constant coefficient into a power series
`f` through `PowerSeries.subst b f`, and records the side condition on `b` as
`PowerSeries.HasSubst b`. This file records that the substitution `X ↦ (1 + X) ^ u - 1`, for a
binomial series `(1 + X) ^ u`, is legitimate: it is the change of variable relating the
power-series coordinates of a completed group algebra attached to two topological generators.

## Main results

* `TauCeti.hasSubst_binomialSeries_sub_one`: `(1 + X) ^ u - 1` can be substituted.
-/

public section

namespace TauCeti

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The binomial series `(1 + X) ^ u - 1` has constant coefficient zero, so power series can be
substituted into it. -/
theorem hasSubst_binomialSeries_sub_one [BinomialRing R] (u : R) :
    HasSubst (binomialSeries S u - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

end TauCeti
