/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Vanishing of the order of vanishing

For a Noetherian domain `R` of Krull dimension at most one with fraction field `K`, Mathlib's
`Ring.ordFrac R : K →*₀ ℤᵐ⁰` extends the order of vanishing `Ring.ord R x = length (R ⧸ (x))` to
the fraction field. This file records that the order of a nonzero element of `R` is trivial
exactly when that element is a unit: `R ⧸ (x)` is the zero ring exactly when `(x)` is the unit
ideal. Mathlib has the forward direction, `Ring.ordFrac_of_isUnit`; the converse is what reads
"`f` has order zero at a codimension-one point" as "`f` is a unit at that point".

## Main results

* `TauCeti.Ring.ord_eq_zero_iff`: `Ring.ord R x = 0` exactly when `x` is a unit;
* `TauCeti.Ring.isUnit_iff_ordFrac_one`: `x` is a unit exactly when `Ring.ordFrac R x = 1`; this
  extends Mathlib's `Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` to Noetherian domains
  of dimension at most one.
-/

public section

namespace TauCeti

namespace Ring

variable {R : Type*} [CommRing R]

/-- The order of vanishing of a ring element is zero exactly when the element is a unit: the
quotient `R ⧸ (x)` is trivial exactly when `(x)` is the unit ideal. -/
theorem ord_eq_zero_iff (x : R) : Ring.ord R x = 0 ↔ IsUnit x := by
  rw [Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- In a Noetherian domain of dimension at most one, an element is a unit exactly when its order
of vanishing in the fraction field is trivial. This extends Mathlib's
`Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` from discrete valuation rings to the
local rings at the codimension-one points of an arbitrary locally Noetherian integral scheme. -/
theorem isUnit_iff_ordFrac_one {x : R} : IsUnit x ↔ Ring.ordFrac R (algebraMap R K x) = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm, ← ord_eq_zero_iff,
    ← hn, ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one, Nat.cast_eq_zero, Nat.cast_eq_zero]

end Ring

end TauCeti
