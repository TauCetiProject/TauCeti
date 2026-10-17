/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Dimension roots of Lebesgue volume under dilation

The dimension root of outer volume scales by the absolute value of a real dilation
in a positive-dimensional real inner product space. The identity applies to arbitrary
sets and infinite outer volumes, and supplies the scaling law for volume inequalities.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dimension-root volume scales linearly under every real dilation, including zero.
This identity holds for arbitrary sets and infinite outer volumes. -/
theorem volume_smul_rpow {A : Set E} (hn : Module.finrank ℝ E ≠ 0) (c : ℝ) :
    volume (c • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      ENNReal.ofReal |c| * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  rw [Measure.addHaar_smul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    abs_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (abs_nonneg c) hn]

end TauCeti
