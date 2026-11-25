/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.BigOStar
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Examples of the explicit error predicate

These examples pin down the reading of `TauCeti.BigOStar a b e`, written `a = b + O*(e)`, against
nearby readings that would be wrong:

* `pi_bigOStar_three` and `not_pi_bigOStar_three`: `π = 3 + O*(0.1416)` holds and
  `π = 3 + O*(0.1415)` fails, since `π - 3 = 0.14159…`; the displayed error is a two-sided bound
  on the absolute difference.
* `not_pi_bigOStar_four_zero`: `π = 4 + O*(0)` fails although `π ≤ 4 + 0`, so the predicate is not
  the one-sided bound `a ≤ b + e`.
* `not_one_bigOStar_one_neg_one`: `1 = 1 + O*(-1)` fails, so a negative error is never admissible,
  unlike under a reading `‖a - b‖ ≤ |e|`.
* `I_bigOStar_zero_one` and `one_bigOStar_zero_one`: `i = 0 + O*(1)` holds in `ℂ`, and
  `1 = 0 + O*(1)` holds in `ℝ`, so the error is absolute: the relative reading
  `‖a - b‖ ≤ e ‖b‖` would require `1 ≤ 0`.
-/

public section

namespace TauCeti.BigOStarExamples

open Real

/-- `π = 3 + O*(0.1416)`. -/
theorem pi_bigOStar_three : BigOStar π 3 0.1416 := by
  rw [bigOStar_iff_sub_le_and_le_add]
  constructor <;> linarith [pi_gt_d4, pi_lt_d4]

/-- `π = 3 + O*(0.1415)` fails, since `π - 3 > 0.1415`. -/
theorem not_pi_bigOStar_three : ¬BigOStar π 3 0.1415 := by
  rw [bigOStar_iff_sub_le_and_le_add]
  rintro ⟨-, h⟩
  linarith [pi_gt_d4]

/-- `π = 4 + O*(0)` fails, although `π ≤ 4 + 0`. -/
theorem not_pi_bigOStar_four_zero : ¬BigOStar π 4 0 ∧ π ≤ 4 + 0 := by
  rw [bigOStar_zero_iff]
  exact ⟨pi_lt_four.ne, by linarith [pi_lt_four]⟩

/-- `1 = 1 + O*(-1)` fails: a negative error is never admissible. -/
theorem not_one_bigOStar_one_neg_one : ¬BigOStar (1 : ℝ) 1 (-1) := by
  simp

/-- `i = 0 + O*(1)` holds in `ℂ`, with equality `‖i‖ = 1`. -/
theorem I_bigOStar_zero_one : BigOStar Complex.I 0 1 := by
  simp

/-- `1 = 0 + O*(1)` holds, while the relative bound `‖1 - 0‖ ≤ 1 * ‖0‖` fails. -/
theorem one_bigOStar_zero_one : BigOStar (1 : ℝ) 0 1 ∧ ¬‖(1 : ℝ) - 0‖ ≤ 1 * ‖(0 : ℝ)‖ := by
  simp

end TauCeti.BigOStarExamples
