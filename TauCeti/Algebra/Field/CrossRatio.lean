/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cross-ratio of four points in a field

For four points `a, b, c, d` of a field `K`, the birapport
`TauCeti.crossRatio a b c d = (a - c) * (b - d) / ((a - d) * (b - c))` is the cross-ratio
normalized so that `(a, 0, 1, z)` tends to `z` as `a → ∞`, with poles where `a = d` or `b = c`
totalised to `0 : K` by field division.

## Main definitions

* `TauCeti.crossRatio`: the finite cross-ratio `(a - c) * (b - d) / ((a - d) * (b - c))` over a
  field `K`.

## Main results

* `TauCeti.crossRatio_swap_within_pairs`, `TauCeti.crossRatio_swap_pairs`, and
  `TauCeti.crossRatio_reverse`: unconditional Klein-four invariance.
* `TauCeti.crossRatio_eq_zero_iff` and `TauCeti.crossRatio_eq_one_iff`: exact characterizations of
  when `crossRatio` equals `0` or `1`, with corollaries `TauCeti.crossRatio_ne_zero` and
  `TauCeti.crossRatio_ne_one`.
* `TauCeti.crossRatio_swap_first_second` and its five transposition companions: the anharmonic
  transformations `r ↦ r⁻¹`, `r ↦ 1 - r`, and `r ↦ r / (r - 1)` under permutations of four points
  under sharp non-degeneracy hypotheses.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993), §4.1.
* Don Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*,
  Springer (2007), Part I, §3.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K]

/-- The cross-ratio `(a - c) * (b - d) / ((a - d) * (b - c))` of four elements of a field `K`,
normalized so that `(a, 0, 1, z)` tends to `z` as `a → ∞`. Poles where `a = d` or `b = c` take
the totalised field value `0`. -/
def crossRatio (a b c d : K) : K :=
  (a - c) * (b - d) / ((a - d) * (b - c))

/-- Explicit rational formula for `TauCeti.crossRatio`. -/
theorem crossRatio_def (a b c d : K) :
    crossRatio a b c d = (a - c) * (b - d) / ((a - d) * (b - c)) :=
  (rfl)

/-- Swapping both `(a, b)` and `(c, d)` leaves `crossRatio` unchanged, including at degenerate
tuples. -/
theorem crossRatio_swap_within_pairs (a b c d : K) :
    crossRatio b a d c = crossRatio a b c d := by
  simp only [crossRatio_def, mul_comm (b - d) (a - c), mul_comm (b - c) (a - d)]

/-- Exchanging the first pair `(a, b)` with the second pair `(c, d)` leaves `crossRatio`
unchanged, including at degenerate tuples. -/
theorem crossRatio_swap_pairs (a b c d : K) :
    crossRatio c d a b = crossRatio a b c d := by
  have hnum : (c - a) * (d - b) = (a - c) * (b - d) := by ring
  have hden : (c - b) * (d - a) = (a - d) * (b - c) := by ring
  rw [crossRatio_def, crossRatio_def, hnum, hden]

/-- Reversing the order of all four points leaves `crossRatio` unchanged. -/
theorem crossRatio_reverse (a b c d : K) :
    crossRatio d c b a = crossRatio a b c d := by
  rw [crossRatio_swap_pairs, crossRatio_swap_within_pairs]

/-- `crossRatio a b c d` vanishes when the first and third entries coincide. -/
@[simp]
theorem crossRatio_self_first_third (a b d : K) : crossRatio a b a d = 0 := by
  simp [crossRatio_def]

/-- `crossRatio a b c d` vanishes when the second and fourth entries coincide. -/
@[simp]
theorem crossRatio_self_second_fourth (a b c : K) : crossRatio a b c b = 0 := by
  simp [crossRatio_def]

/-- `crossRatio a b c d` takes the totalised value `0` when the first and fourth entries
coincide. -/
@[simp]
theorem crossRatio_self_first_fourth (a b c : K) : crossRatio a b c a = 0 := by
  simp [crossRatio_def]

/-- `crossRatio a b c d` takes the totalised value `0` when the second and third entries
coincide. -/
@[simp]
theorem crossRatio_self_second_third (a b d : K) : crossRatio a b b d = 0 := by
  simp [crossRatio_def]

/-- When the first two entries coincide and are distinct from the third and fourth, `crossRatio`
equals `1`. Both distinctness hypotheses are needed because division by zero yields `0`. -/
@[simp]
theorem crossRatio_self_first_second {a c d : K} (had : a ≠ d) (hac : a ≠ c) :
    crossRatio a a c d = 1 := by
  rw [crossRatio_def, mul_comm (a - d) (a - c)]
  exact div_self (mul_ne_zero (sub_ne_zero.mpr hac) (sub_ne_zero.mpr had))

/-- When the last two entries coincide and are distinct from the first and second, `crossRatio`
equals `1`. -/
@[simp]
theorem crossRatio_self_third_fourth {a b c : K} (hac : a ≠ c) (hbc : b ≠ c) :
    crossRatio a b c c = 1 := by
  rw [← crossRatio_swap_pairs]
  exact crossRatio_self_first_second hbc.symm hac.symm

/-- `crossRatio a b c d` vanishes precisely when a numerator factor (`a = c` or `b = d`) or a
denominator factor (`a = d` or `b = c`) vanishes. -/
@[simp]
theorem crossRatio_eq_zero_iff (a b c d : K) :
    crossRatio a b c d = 0 ↔ a = c ∨ b = d ∨ a = d ∨ b = c := by
  simp [crossRatio_def, sub_eq_zero, or_assoc]

/-- `crossRatio a b c d` equals `1` precisely when the denominator is nonzero (`a ≠ d` and `b ≠ c`)
and either the first two or the last two entries coincide. -/
@[simp]
theorem crossRatio_eq_one_iff (a b c d : K) :
    crossRatio a b c d = 1 ↔ a ≠ d ∧ b ≠ c ∧ (a = b ∨ c = d) := by
  rw [crossRatio_def]
  by_cases hden : (a - d) * (b - c) = 0
  · simp only [hden, div_zero, zero_ne_one, false_iff, not_and]
    intro had hbc
    exact absurd hden (mul_ne_zero (sub_ne_zero.mpr had) (sub_ne_zero.mpr hbc))
  · have had : a ≠ d := sub_ne_zero.mp (left_ne_zero_of_mul hden)
    have hbc : b ≠ c := sub_ne_zero.mp (right_ne_zero_of_mul hden)
    rw [div_eq_one_iff_eq hden, ← sub_eq_zero]
    have hfac : (a - c) * (b - d) - (a - d) * (b - c) = (a - b) * (c - d) := by ring
    rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    simp [had, hbc]

/-- `crossRatio a b c d` is nonzero whenever `a ≠ c`, `b ≠ d`, `a ≠ d`, and `b ≠ c`. -/
theorem crossRatio_ne_zero {a b c d : K} (hac : a ≠ c) (hbd : b ≠ d) (had : a ≠ d)
    (hbc : b ≠ c) : crossRatio a b c d ≠ 0 := by
  simp [hac, hbd, had, hbc]

/-- `crossRatio a b c d` is not equal to `1` whenever `a ≠ b` and `c ≠ d`. -/
theorem crossRatio_ne_one {a b c d : K} (hab : a ≠ b) (hcd : c ≠ d) :
    crossRatio a b c d ≠ 1 := by
  simp [hab, hcd]

/-- On `(a, 0, 1, z)`, `crossRatio a 0 1 z = z * (a - 1) / (a - z)` for all `a, z : K` (including
the pole `a = z`, where both sides equal `0`). -/
theorem crossRatio_zero_one (a z : K) :
    crossRatio a 0 1 z = z * (a - 1) / (a - z) := by
  rw [crossRatio_def]
  have hnum : (a - 1) * (0 - z) = -(z * (a - 1)) := by ring
  have hden : (a - z) * (0 - 1) = -(a - z) := by ring
  rw [hnum, hden, neg_div_neg_eq]

/-- Exchanging the first two entries inverts `crossRatio` unconditionally (with `0⁻¹ = 0`). -/
theorem crossRatio_swap_first_second (a b c d : K) :
    crossRatio b a c d = (crossRatio a b c d)⁻¹ := by
  rw [crossRatio_def, crossRatio_def, inv_div, mul_comm (b - c) (a - d), mul_comm (b - d) (a - c)]

/-- Exchanging the last two entries inverts `crossRatio` unconditionally (with `0⁻¹ = 0`). -/
theorem crossRatio_swap_third_fourth (a b c d : K) :
    crossRatio a b d c = (crossRatio a b c d)⁻¹ := by
  rw [← crossRatio_swap_within_pairs, crossRatio_swap_first_second]

/-- Plücker relation for `crossRatio`: exchanging the middle two entries replaces `r` by `1 - r`
whenever `a ≠ d` and `b ≠ c`. -/
theorem crossRatio_swap_second_third {a b c d : K} (had : a ≠ d) (hbc : b ≠ c) :
    crossRatio a c b d = 1 - crossRatio a b c d := by
  rw [crossRatio_def, crossRatio_def]
  field_simp [sub_ne_zero.mpr had, sub_ne_zero.mpr hbc, sub_ne_zero.mpr hbc.symm]
  ring

/-- Exchanging the first and fourth entries replaces `crossRatio` by `1 - r` whenever `a ≠ d` and
`b ≠ c`. -/
theorem crossRatio_swap_first_fourth {a b c d : K} (had : a ≠ d) (hbc : b ≠ c) :
    crossRatio d b c a = 1 - crossRatio a b c d := by
  rw [← crossRatio_reverse, crossRatio_swap_second_third had hbc]

/-- Exchanging the first and third entries sends `r = crossRatio a b c d` to `r / (r - 1)`
whenever `a ≠ d` and `b ≠ c` (including when `a = c` or `b = d`, where both sides equal `0`). -/
theorem crossRatio_swap_first_third {a b c d : K} (had : a ≠ d) (hbc : b ≠ c) :
    crossRatio c b a d = crossRatio a b c d / (crossRatio a b c d - 1) := by
  rcases eq_or_ne a c with rfl | hac
  · simp
  rcases eq_or_ne b d with rfl | hbd
  · simp
  have hr0 : crossRatio a b c d ≠ 0 := crossRatio_ne_zero hac hbd had hbc
  rw [crossRatio_swap_first_second, crossRatio_swap_second_third hbd hac,
    crossRatio_swap_first_second]
  rcases eq_or_ne (crossRatio a b c d) 1 with hr1 | hr1
  · simp [hr1]
  · field_simp [hr0, sub_ne_zero.mpr hr1]

/-- Exchanging the second and fourth entries sends `r = crossRatio a b c d` to `r / (r - 1)`
whenever `a ≠ d` and `b ≠ c` (including when `a = c` or `b = d`, where both sides equal `0`). -/
theorem crossRatio_swap_second_fourth {a b c d : K} (had : a ≠ d) (hbc : b ≠ c) :
    crossRatio a d c b = crossRatio a b c d / (crossRatio a b c d - 1) := by
  rw [← crossRatio_swap_within_pairs, crossRatio_swap_first_third hbc had,
    crossRatio_swap_within_pairs]

/-! ### Checks and sharpness witnesses -/

section Checks

-- Missing-hypothesis negative control: `crossRatio 0 0 1 2 = 1`, whereas `crossRatio 0 0 0 2 = 0`.
example : crossRatio (0 : ℚ) 0 1 2 = 1 ∧ crossRatio (0 : ℚ) 0 0 2 = 0 :=
  ⟨crossRatio_self_first_second (by norm_num) (by norm_num), by simp⟩

end Checks

end TauCeti
