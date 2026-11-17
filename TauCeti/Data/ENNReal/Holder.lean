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

Elementary facts about Hölder exponents: the missing exponent `r` of a triple with
`1/p + 1/r = 1/q` exists once `q ≤ p`, and the Hölder condition `1/p + 1/q ≤ 1` bounds both
exponents below by `1` and the conjugate exponent of `p` above by `q`.

## Main declarations

* `ENNReal.HolderTriple.of_le`: for `q ≤ p`, the triple `(p, (q⁻¹ - p⁻¹)⁻¹, q)`.
* `ENNReal.one_le_left_of_inv_add_inv_le_one`, `ENNReal.one_le_right_of_inv_add_inv_le_one`:
  `1/p + 1/q ≤ 1` forces `1 ≤ p` and `1 ≤ q`.
* `ENNReal.conjExponent_le_of_inv_add_inv_le_one`: `1/p + 1/q ≤ 1` forces `p' ≤ q` for the
  conjugate exponent `p'` of `p`.
-/

public section

open scoped ENNReal

namespace ENNReal.HolderTriple

/-- For `q ≤ p`, the exponent `r = (q⁻¹ - p⁻¹)⁻¹` satisfies `1/p + 1/r = 1/q`. -/
theorem of_le {p q : ℝ≥0∞} (hqp : q ≤ p) : HolderTriple p (q⁻¹ - p⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 hqp)]⟩

end ENNReal.HolderTriple

namespace ENNReal

variable {p q : ℝ≥0∞}

/-- The Hölder condition `1/p + 1/q ≤ 1` forces `1 ≤ p`. -/
theorem one_le_left_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : 1 ≤ p :=
  ENNReal.inv_le_one.1 (le_self_add.trans hpq)

/-- The Hölder condition `1/p + 1/q ≤ 1` forces `1 ≤ q`. -/
theorem one_le_right_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : 1 ≤ q :=
  ENNReal.inv_le_one.1 (le_add_self.trans hpq)

/-- Under the Hölder condition `1/p + 1/q ≤ 1`, the conjugate exponent of `p` is at most `q`. -/
theorem conjExponent_le_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : p.conjExponent ≤ q := by
  have hp1 := one_le_left_of_inv_add_inv_le_one hpq
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have h1 : p⁻¹ + p.conjExponent⁻¹ = 1 := by
    rw [HolderTriple.inv_add_inv_eq_inv p p.conjExponent 1, inv_one]
  exact ENNReal.inv_le_inv.1 (ENNReal.le_of_add_le_add_left
    (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp1).ne') (h1 ▸ hpq))

end ENNReal
