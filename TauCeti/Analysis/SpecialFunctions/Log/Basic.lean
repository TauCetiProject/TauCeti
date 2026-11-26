/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic facts about the real logarithm

* `Real.log_div_pos`: for `0 < r < c` the logarithm `log (c / r)` is positive.
* `Real.coe_toNNReal_log_one_add`: for `0 ≤ r` the logarithm `log (1 + r)` is nonnegative, so
  `((log (1 + r)).toNNReal : ℝ) = log (1 + r)`.
* `Real.abs_log_sub_log_le_log`: two positive reals within a factor `c` of each other have
  logarithms within `log c`.

## Upper boundedness of `Real.log` on bounded and compact sets

Although `Real.log` is discontinuous at `0`, Lean's conventions `Real.log 0 = 0` and
`Real.log (-x) = Real.log x` (`Real.log_abs`), combined with `Real.log_le_self`, ensure
`Real.log y ≤ |y|` for every `y : ℝ`. Consequently, `Real.log '' s` is bounded above for every
bounded subset `s : Set ℝ`, and `(fun x ↦ Real.log (f x)) '' s` is bounded above whenever `f` is a
continuous real-valued function on a compact set `s` (even if `f` vanishes or changes sign on `s`).

Two positive reals within a factor `c` of each other have logarithms within `log c`
(`Real.abs_log_sub_log_le_log`).
-/

public section

namespace Real

/-- For `0 < r < c` the logarithm `log (c / r)` is positive. -/
theorem log_div_pos {c r : ℝ} (h0 : 0 < r) (hr : r < c) : 0 < log (c / r) :=
  log_pos ((one_lt_div h0).2 hr)

/-- The logarithmic time `log (1 + r)` of a nonnegative `r` is nonnegative, so it survives the
round trip through `ℝ≥0`. -/
theorem coe_toNNReal_log_one_add {r : ℝ} (hr : 0 ≤ r) :
    ((log (1 + r)).toNNReal : ℝ) = log (1 + r) :=
  coe_toNNReal _ (log_nonneg (by linarith))

end Real

/-- For any bounded subset `s : Set ℝ`, the image `Real.log '' s` is bounded above (using
`Real.log y = Real.log |y| ≤ |y|` across nonpositive values). -/
theorem Bornology.IsBounded.bddAbove_image_log {s : Set ℝ} (hs : Bornology.IsBounded s) :
    BddAbove (Real.log '' s) := by
  obtain ⟨C, hC⟩ := hs.exists_norm_le
  refine ⟨C, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [← Real.log_abs]
  exact (Real.log_le_self (abs_nonneg y)).trans (Real.norm_eq_abs y ▸ hC y hy)

/-- If `f : X → ℝ` is continuous on a compact set `s`, the image `(fun x ↦ Real.log (f x)) '' s` is
bounded above, including across zeros and negative values of `f` on `s`. -/
theorem IsCompact.bddAbove_image_log {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hf : ContinuousOn f s) :
    BddAbove ((fun x ↦ Real.log (f x)) '' s) :=
  Set.image_image Real.log f s ▸ (hs.image_of_continuousOn hf).isBounded.bddAbove_image_log

example : BddAbove ((fun x : ℝ ↦ Real.log x) '' Set.Icc (-1) 1) :=
  isCompact_Icc.bddAbove_image_log continuousOn_id

/-- Two positive reals within a factor `c` of each other, `x ≤ c y` and `y ≤ c x`, have
logarithms within `log c`: `|log x - log y| ≤ log c`. -/
theorem Real.abs_log_sub_log_le_log {x y c : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ c * y)
    (hyx : y ≤ c * x) : |Real.log x - Real.log y| ≤ Real.log c := by
  have hc : 0 < c := pos_of_mul_pos_left (hx.trans_le hxy) hy.le
  have hup : Real.log x ≤ Real.log c + Real.log y := by
    rw [← Real.log_mul hc.ne' hy.ne']
    exact Real.log_le_log hx hxy
  have hlo : Real.log y ≤ Real.log c + Real.log x := by
    rw [← Real.log_mul hc.ne' hx.ne']
    exact Real.log_le_log hy hyx
  exact abs_le.2 ⟨by linarith, by linarith⟩
