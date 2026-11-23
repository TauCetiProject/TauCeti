/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
import TauCeti.Analysis.SpecialFunctions.Sigmoid.Basic

/-!
# The sigmoid as a bounded Hölder function

This file packages `Real.sigmoid` as an element `TauCeti.sigmoidHolder` of `HolderSpace α ℝ ℝ`
for every exponent `α ≤ 1`.
-/

public section

namespace TauCeti

open Real
open scoped NNReal

/-- The logistic function `x ↦ sigmoid x`, as a bounded `α`-Hölder function on `ℝ` (`α ≤ 1`). -/
noncomputable def sigmoidHolder {α : ℝ≥0} (hα : α ≤ 1) : HolderSpace α ℝ ℝ :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup sigmoid continuous_sigmoid 1 fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sigmoid_nonneg x)]
      exact sigmoid_le_one x)
    (by simpa using memHolder_iteratedDeriv_sigmoid 0 hα)

/-- Evaluation of `sigmoidHolder` at a real point gives `sigmoid`. -/
@[simp]
theorem sigmoidHolder_apply {α : ℝ≥0} (hα : α ≤ 1) (x : ℝ) : sigmoidHolder hα x = sigmoid x := by
  simp [sigmoidHolder]

end TauCeti
