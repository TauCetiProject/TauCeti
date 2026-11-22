/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
import TauCeti.RingTheory.OrderOfVanishing
import TauCeti.RingTheory.Valuation.Discrete.Order.Vanishing

/-!
# Order of vanishing in the valuation ring of a place

The valuation ring `P.integers` of a place `P` of `F / k` is a discrete valuation ring, so
Mathlib's length-based order of vanishing `Ring.ord P.integers x` is defined for every
`x : P.integers`. On nonzero elements, it agrees with the normalized additive order
`(P.ord (x : F)).toNat`.

## Main results

* `TauCeti.Place.ringOrd_integers_eq_toNat_ord`: for `x : P.integers` with `(x : F) ≠ 0`,
  `Ring.ord P.integers x = ((P.ord (x : F)).toNat : ℕ∞)`.
-/

public section

namespace TauCeti

namespace Place

/-- For a nonzero element `x` of the valuation ring `P.integers`, the module-length order of
vanishing `Ring.ord P.integers x` agrees with the normalized additive order
`(P.ord (x : F)).toNat`. -/
theorem ringOrd_integers_eq_toNat_ord {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) {x : P.integers} (hx : (x : F) ≠ 0) :
    Ring.ord P.integers x = ((P.ord (x : F)).toNat : ℕ∞) := by
  let σ : P.integers ≃+* P.valuation.valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring P.integers_def)
  rw [← Ring.ord_ringEquiv σ x,
    Valuation.ringOrd_valuationSubring_eq_toNat_ord P.valuation P.valuation_surjective
      (by simpa [σ, RingEquiv.coe_subringCongr_apply] using hx),
    RingEquiv.coe_subringCongr_apply, P.ord_valuation]

end Place

end TauCeti
