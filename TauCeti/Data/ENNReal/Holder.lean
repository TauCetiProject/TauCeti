/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder

/-!
# Hölder exponent triples in `ℝ≥0∞`

Two elementary facts about `ENNReal.HolderTriple`: the missing exponent `r` with
`1/p + 1/r = 1/q` exists once `q ≤ p`, and a Hölder triple with target at least `1` has
`1/p + 1/q ≤ 1`.

## Main declarations

* `ENNReal.HolderTriple.of_le`: for `q ≤ p`, the triple `(p, (q⁻¹ - p⁻¹)⁻¹, q)`.
* `ENNReal.HolderTriple.inv_add_inv_le_one`: `p⁻¹ + q⁻¹ ≤ 1` when the target is at least `1`.
-/

public section

open scoped ENNReal

namespace ENNReal.HolderTriple

/-- For `q ≤ p`, the exponent `r = (q⁻¹ - p⁻¹)⁻¹` satisfies `1/p + 1/r = 1/q`. -/
theorem of_le {p q : ℝ≥0∞} (hqp : q ≤ p) : HolderTriple p (q⁻¹ - p⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 hqp)]⟩

/-- A Hölder triple whose target exponent is at least `1` has `1/p + 1/q ≤ 1`. -/
theorem inv_add_inv_le_one (p q r : ℝ≥0∞) [HolderTriple p q r] (hr : 1 ≤ r) :
    p⁻¹ + q⁻¹ ≤ 1 := by
  rw [inv_add_inv_eq_inv p q r]
  exact ENNReal.inv_le_one.2 hr

end ENNReal.HolderTriple
