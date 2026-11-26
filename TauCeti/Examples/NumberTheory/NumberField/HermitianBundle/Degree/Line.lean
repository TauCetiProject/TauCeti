/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Line

/-!
# The Arakelov degree of a hermitian line: examples

Over `ℚ`, the trivial lines with generator norms `e^{-a}` and `e^{-b}` have degrees `a` and `b`,
and their tensor product has degree `a + b`.
-/

public section

open NumberField TauCeti

namespace TauCeti.HermitianLineDegreeExamples

/-- Over `ℚ`, `deg^((ℤ, e^{-a} |·|)) = a`. -/
example (a : ℝ) : ((HermitianMetric.trivial ℚ).rescale a).lineDegree = a := by
  rw [HermitianMetric.lineDegree_rescale, HermitianMetric.lineDegree_trivial, Module.finrank_self]
  simp

/-- Over `ℚ`, the tensor product of the trivial lines with generator norms `e^{-a}` and `e^{-b}`
has degree `a + b`. -/
example (a b : ℝ) :
    (((HermitianMetric.trivial ℚ).rescale a).tmul
      ((HermitianMetric.trivial ℚ).rescale b)).lineDegree = a + b := by
  rw [HermitianMetric.lineDegree_tmul, HermitianMetric.lineDegree_rescale,
    HermitianMetric.lineDegree_rescale, HermitianMetric.lineDegree_trivial, Module.finrank_self]
  simp

end TauCeti.HermitianLineDegreeExamples
