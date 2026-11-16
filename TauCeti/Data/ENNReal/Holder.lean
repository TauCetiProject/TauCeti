/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder

/-!
# Hölder exponent triples and conjugates in `ℝ≥0∞`

Elementary facts about `ENNReal.HolderTriple` and `ENNReal.HolderConjugate`: the missing exponent
`r` with `1/p + 1/r = 1/q` exists once `q ≤ p`, and a Hölder conjugate pair `(p, q)` satisfies
`2 < p ↔ q < 2`.

## Main declarations

* `ENNReal.HolderTriple.of_le`: for `q ≤ p`, the triple `(p, (q⁻¹ - p⁻¹)⁻¹, q)`.
* `ENNReal.HolderConjugate.two_lt_iff_lt_two`: for Hölder conjugates `(p, q)`, `2 < p ↔ q < 2`.
-/

public section

open scoped ENNReal

namespace ENNReal.HolderTriple

/-- For `q ≤ p`, the exponent `r = (q⁻¹ - p⁻¹)⁻¹` satisfies `1/p + 1/r = 1/q`. -/
theorem of_le {p q : ℝ≥0∞} (hqp : q ≤ p) : HolderTriple p (q⁻¹ - p⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 hqp)]⟩

end ENNReal.HolderTriple

namespace ENNReal.HolderConjugate

/-- For Hölder conjugate exponents `(p, q)` in `ℝ≥0∞`, `2 < p` holds if and only if `q < 2`. -/
theorem two_lt_iff_lt_two (p q : ℝ≥0∞) [HolderConjugate p q] : 2 < p ↔ q < 2 := by
  constructor
  · intro hp
    by_contra! h2q
    have hp2 : p⁻¹ < (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_lt_inv.2 hp
    have hq2 : q⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 h2q
    have h1 : p⁻¹ + q⁻¹ < (2 : ℝ≥0∞)⁻¹ + 2⁻¹ :=
      ENNReal.add_lt_add_of_lt_of_le (hq2.trans_lt (by norm_num)).ne hp2 hq2
    rw [inv_add_inv_eq_one p q, inv_add_inv_eq_one 2 2] at h1
    exact h1.false
  · intro hq
    by_contra! hp2
    have hp2' : (2 : ℝ≥0∞)⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hp2
    have hq2' : (2 : ℝ≥0∞)⁻¹ < q⁻¹ := ENNReal.inv_lt_inv.2 hq
    have h1 : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ < p⁻¹ + q⁻¹ :=
      ENNReal.add_lt_add_of_le_of_lt (by norm_num) hp2' hq2'
    rw [inv_add_inv_eq_one p q, inv_add_inv_eq_one 2 2] at h1
    exact h1.false

end ENNReal.HolderConjugate
