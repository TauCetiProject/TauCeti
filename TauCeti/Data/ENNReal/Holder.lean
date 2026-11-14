/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.Basic.Real.ConjExponents

/-!
# Hölder exponent triples in `ℝ≥0∞`

Elementary facts about Hölder exponents: the missing exponent `r` with `1/p + 1/r = 1/q` exists
once `q ≤ p`, and the conjugate exponent of `p > 2` is below `2`.

## Main declarations

* `ENNReal.HolderTriple.of_le`: for `q ≤ p`, the triple `(p, (q⁻¹ - p⁻¹)⁻¹, q)`.
* `ENNReal.conjExponent_lt_two`: `p.conjExponent < 2` for `2 < p`.
-/

public section

open scoped ENNReal

namespace ENNReal.HolderTriple

/-- For `q ≤ p`, the exponent `r = (q⁻¹ - p⁻¹)⁻¹` satisfies `1/p + 1/r = 1/q`. -/
theorem of_le {p q : ℝ≥0∞} (hqp : q ≤ p) : HolderTriple p (q⁻¹ - p⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 hqp)]⟩

end ENNReal.HolderTriple

namespace ENNReal

/-- The conjugate exponent of `p > 2` is below `2`. -/
theorem conjExponent_lt_two {p : ℝ≥0∞} (hp : 2 < p) : p.conjExponent < 2 := by
  have h1 : 1 < p - 1 := by
    rwa [lt_tsub_iff_left, one_add_one_eq_two]
  rw [conjExponent]
  calc 1 + (p - 1)⁻¹ < 1 + 1 := ENNReal.add_lt_add_left one_ne_top (ENNReal.inv_lt_one.2 h1)
    _ = 2 := one_add_one_eq_two

end ENNReal
