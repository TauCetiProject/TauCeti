/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A sample covariance matrix

The sample covariance of the `1 × 2` complex data matrix with entries `1` and `I` is `1`.
-/

public section

open Matrix

/-- The sample covariance of the `1 × 2` data matrix `(1, i)` is `(1 + 1) / 2 = 1`. -/
example : sampleCovariance !![(1 : ℂ), Complex.I] = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp
  norm_num
