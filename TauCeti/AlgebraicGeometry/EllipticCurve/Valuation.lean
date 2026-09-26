/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Valuations of Weierstrass invariants

This file records how additive valuations of Weierstrass-curve invariants behave under admissible
changes of variables.

## Main results

* `WeierstrassCurve.ord_Δ_smul`: a change of variables subtracts twelve times the order of its
  scaling parameter from the order of the discriminant.
-/

public section

namespace WeierstrassCurve

open scoped WithZero

variable {K : Type*} [Field K]

/-- **A change of variables subtracts twelve times the order of its scaling parameter from the
order of the discriminant.** This is a statement about an arbitrary `ℤᵐ⁰`-valued valuation of
`K`; the discrete valuation of a local minimal model plays no role. -/
theorem ord_Δ_smul (w : Valuation K ℤᵐ⁰) (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    w.ord (C • W).Δ = w.ord W.Δ - 12 * w.ord (C.u : K) := by
  rw [variableChange_Δ,
    Valuation.ord_mul _ (pow_ne_zero _ C.u⁻¹.ne_zero) W.isUnit_Δ.ne_zero,
    Valuation.ord_pow, Units.val_inv_eq_inv_val, Valuation.ord_inv]
  ring

end WeierstrassCurve

end
