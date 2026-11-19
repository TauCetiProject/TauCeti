/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Real powers of nonnegative multiples

In a unital algebra with a continuous functional calculus for self-adjoint elements, the real
power of a nonnegative multiple of a nonnegative element is the multiple of the power:
`(c • a) ^ y = c ^ y • a ^ y` for every `c : ℝ≥0` and every real `y` (`CFC.smul_rpow`), and
likewise for every real `c ≥ 0` (`CFC.real_smul_rpow`). This is the
identity behind the homogeneity of powers of operator-valued functions: if
`a (t • ξ) = t ^ m • a ξ`, then `a (t • ξ) ^ y = t ^ (m y) • a ξ ^ y`.
-/

public section

open scoped NNReal

namespace CFC

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

/-- The real power of a multiple of a nonnegative element: `(c • a) ^ y = c ^ y • a ^ y`. -/
theorem smul_rpow (a : A) (c : ℝ≥0) (y : ℝ) (ha : 0 ≤ a := by cfc_tac) :
    (c • a) ^ y = c ^ y • a ^ y := by
  rcases eq_or_ne c 0 with rfl | hc
  · rcases eq_or_ne y 0 with rfl | hy
    · simp [rpow_zero a ha, rpow_zero (0 : A) le_rfl]
    · simp [← rpow_eq_pow, zero_rpow hy, NNReal.zero_rpow hy]
  have hσ : spectrum ℝ≥0 (c • a) = (c • ·) '' spectrum ℝ≥0 a :=
    spectrum.unit_smul_eq_smul a (Units.mk0 c hc)
  by_cases hf : ContinuousOn (fun x : ℝ≥0 ↦ x ^ y) (spectrum ℝ≥0 a)
  · rw [rpow_def, rpow_def,
      ← cfc_comp_smul c _ a ((NNReal.continuousOn_rpow_const_smul_image_iff hc).mpr hf) ha,
      ← cfc_smul (c ^ y) _ a hf]
    refine cfc_congr fun x _ ↦ ?_
    simp [NNReal.mul_rpow, smul_eq_mul]
  · -- Otherwise `x ↦ x ^ y` is not continuous on the spectrum of `c • a` either, and both
    -- sides are the junk value `0`.
    have hf' : ¬ContinuousOn (fun x : ℝ≥0 ↦ x ^ y) (spectrum ℝ≥0 (c • a)) := by
      rwa [hσ, NNReal.continuousOn_rpow_const_smul_image_iff hc]
    rw [rpow_def, rpow_def, cfc_apply_of_not_continuousOn _ hf,
      cfc_apply_of_not_continuousOn _ hf', smul_zero]

/-- The real power of a nonnegative real multiple of a nonnegative element:
`(c • a) ^ y = c ^ y • a ^ y` for `0 ≤ c`. -/
theorem real_smul_rpow (a : A) {c : ℝ} (hc : 0 ≤ c) (y : ℝ) (ha : 0 ≤ a := by cfc_tac) :
    (c • a) ^ y = c ^ y • a ^ y := by
  lift c to ℝ≥0 using hc
  simpa [NNReal.smul_def] using smul_rpow a c y ha

end CFC
