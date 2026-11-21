/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder

/-!
# Hölder exponent triples in `ℝ≥0∞`

Elementary facts about `ENNReal.HolderTriple` and `ENNReal.HolderConjugate`: the missing
exponent `r` with `1/p + 1/r = 1/q` exists once `q ≤ p`, and the exponent conjugate to `p > 2`
is less than `2`, as for the supercritical exponents of planar Sobolev and Cauchy-transform
estimates.

## Main declarations

* `ENNReal.HolderTriple.of_le`: for `q ≤ p`, the triple `(p, (q⁻¹ - p⁻¹)⁻¹, q)`.
* `ENNReal.HolderConjugate.lt_two`: the conjugate of an exponent `p > 2` is less than `2`.
-/

public section

open scoped ENNReal

namespace ENNReal.HolderTriple

/-- For `q ≤ p`, the exponent `r = (q⁻¹ - p⁻¹)⁻¹` satisfies `1/p + 1/r = 1/q`. -/
theorem of_le {p q : ℝ≥0∞} (hqp : q ≤ p) : HolderTriple p (q⁻¹ - p⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 hqp)]⟩

end ENNReal.HolderTriple

namespace ENNReal.HolderConjugate

/-- The exponent conjugate to `p > 2` is less than `2`. -/
theorem lt_two {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : 2 < p) : q < 2 := by
  by_contra hq
  have h := ENNReal.add_lt_add_of_lt_of_le (ENNReal.inv_ne_top.2 (ne_zero q p))
    (ENNReal.inv_lt_inv.2 hp) (ENNReal.inv_le_inv.2 (not_lt.1 hq))
  rw [inv_add_inv_eq_one p q, ENNReal.inv_two_add_inv_two] at h
  exact lt_irrefl _ h

end ENNReal.HolderConjugate
