/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The sine-to-tangent transfer function `tan ∘ arcsin`

Davis--Kahan tangent theorems convert each directed sine singular value `s` into the
tangent `tan (arcsin s) = s / √(1 - s²)` of the same angle.  This module collects the
elementary facts about that scalar transfer used by the infinite-trial limiting argument:
nonnegativity, monotonicity on `[0, 1)`, the exact preimage `sin (arctan C)` of a
prescribed tangent value `C`, and continuity at every point of `[0, 1)`.

Everything here is real analysis about one function; no operator theory enters.
-/

public section

namespace TauCeti
namespace TanArcsin

open Real

/-- The sine-to-tangent transfer is nonnegative on nonnegative inputs — including the
junk regime `1 ≤ t`, where `arcsin` clamps to `π / 2` and `tan (π / 2) = 0`. -/
theorem tanArcsin_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tan (Real.arcsin t) := by
  rw [Real.tan_arcsin]
  exact div_nonneg ht (Real.sqrt_nonneg _)

/-- The sine-to-tangent transfer is monotone from `[0, b]` into `[0, tan (arcsin b)]`
whenever the upper input stays strictly below one. -/
theorem tanArcsin_le_tanArcsin {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Real.tan (Real.arcsin a) ≤ Real.tan (Real.arcsin b) := by
  rw [Real.tan_arcsin, Real.tan_arcsin]
  have hb0 : 0 ≤ b := ha.trans hab
  have hbsq : b ^ 2 < 1 := by nlinarith
  have hasq : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hbpos : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hapos : 0 < Real.sqrt (1 - a ^ 2) := by
    have : a ^ 2 < 1 := lt_of_le_of_lt hasq hbsq
    exact Real.sqrt_pos.mpr (by linarith)
  have hden : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - a ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  calc
    a / Real.sqrt (1 - a ^ 2) ≤ b / Real.sqrt (1 - a ^ 2) :=
      div_le_div_of_nonneg_right hab hapos.le
    _ ≤ b / Real.sqrt (1 - b ^ 2) :=
      div_le_div_of_nonneg_left hb0 hbpos hden

/-- `sin (arctan C)` is the sine whose angle has tangent exactly `C`. -/
theorem tanArcsin_sin_arctan (C : ℝ) :
    Real.tan (Real.arcsin (Real.sin (Real.arctan C))) = C := by
  rw [Real.arcsin_sin (Real.neg_pi_div_two_lt_arctan C).le
    (Real.arctan_lt_pi_div_two C).le, Real.tan_arctan]

/-- `sin (arctan C)` lies strictly below one. -/
theorem sin_arctan_lt_one (C : ℝ) : Real.sin (Real.arctan C) < 1 := by
  rw [Real.sin_arctan]
  have hpos : 0 < Real.sqrt (1 + C ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_one hpos]
  rcases le_or_gt C 0 with hC | hC
  · exact lt_of_le_of_lt hC hpos
  · exact (Real.lt_sqrt hC.le).mpr (by nlinarith)

/-- The sine-to-tangent transfer is continuous at every point of `[0, 1)`. -/
theorem continuousAt_tanArcsin {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    ContinuousAt (fun s => Real.tan (Real.arcsin s)) t := by
  have hcos : Real.cos (Real.arcsin t) ≠ 0 := by
    rw [Real.cos_arcsin]
    have : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
    exact (Real.sqrt_pos.mpr this).ne'
  exact (Real.continuousAt_tan.mpr hcos).comp Real.continuous_arcsin.continuousAt

end TanArcsin
end TauCeti
