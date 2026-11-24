/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Real powers of nonnegative multiples

For a nonnegative element `a` of an algebra with a continuous functional calculus and a real
number `c ≥ 0`, the real powers of `c • a` split as `(c • a) ^ y = c ^ y • a ^ y`
(`CFC.smul_rpow`), the operator version of `Real.mul_rpow`. It is what makes real powers of
positively homogeneous families of operators again positively homogeneous.
-/

public section

open scoped NNReal

namespace CFC

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- Real powers of a nonnegative multiple of a nonnegative element:
`(c • a) ^ y = c ^ y • a ^ y` for `0 ≤ c`. -/
theorem smul_rpow [IsSemitopologicalRing A] [T2Space A] {c : ℝ} (hc : 0 ≤ c) (a : A) (y : ℝ)
    (ha : 0 ≤ a := by cfc_tac) : (c • a) ^ y = c ^ y • a ^ y := by
  lift c to ℝ≥0 using hc
  rcases eq_or_ne c 0 with rfl | hc
  · rcases eq_or_ne y 0 with rfl | hy
    · simp [rpow_zero a ha, rpow_zero (0 : A)]
    · simpa [Real.zero_rpow hy] using zero_rpow (A := A) hy
  -- For `c ≠ 0`, scaling by `c` is a homeomorphism of `ℝ≥0` that the power `f` turns into a
  -- nonzero multiple, so `f` is continuous on the spectrum of `c • a` exactly when it is on that
  -- of `a`. Otherwise both sides are junk values of the functional calculus.
  set f : ℝ≥0 → ℝ≥0 := fun x ↦ x ^ y
  have hf : f ∘ (c • ·) = fun x ↦ c ^ y • f x := funext fun x ↦ by simp [f, NNReal.mul_rpow]
  have hcont : ContinuousOn f ((c • ·) '' spectrum ℝ≥0 a) ↔ ContinuousOn f (spectrum ℝ≥0 a) := by
    exact ((Homeomorph.smulOfNeZero c hc).isInducing.continuousOn_image_iff (g := f)).trans <|
      (congrArg (ContinuousOn · _) hf).to_iff.trans
      (continuousOn_const_smul_iff₀ (NNReal.rpow_pos (pos_iff_ne_zero.2 hc)).ne')
  have hspec : spectrum ℝ≥0 (c • a) = (c • ·) '' spectrum ℝ≥0 a := by
    rw [← cfc_smul_id (R := ℝ≥0) c a, cfc_map_spectrum _ a]
  rw [← NNReal.smul_def, ← NNReal.coe_rpow, ← NNReal.smul_def, rpow_def, rpow_def]
  by_cases h : ContinuousOn f (spectrum ℝ≥0 a)
  · rw [← cfc_comp_smul c f a (hcont.2 h), ← cfc_smul (c ^ y) f a h]
    exact cfc_congr fun x _ ↦ congrFun hf x
  · rw [cfc_apply_of_not_continuousOn _ (hspec ▸ mt hcont.1 h),
      cfc_apply_of_not_continuousOn _ h, smul_zero]

end CFC
