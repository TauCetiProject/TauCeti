/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.TraceForm
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.QuadraticExtension
public import TauCeti.NumberTheory.EffectiveBounds.TraceForm
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Quadratic trace forms over the rationals, the dyadic field and the reals

The quadratic-algebra model gives `Tr_*⟨1⟩ ≅ ⟨2, 2d⟩` for every radicand, including the split
case. Over the reals, taking the square root `i` recovers the trace discriminant calculation used
in effective bounds: the quadratic form is `⟨2, -2⟩` and the algebra discriminant is `-4`.
-/

public section

open QuadraticMap

namespace TauCeti

example (d : ℚ) :
    ((QuadraticMap.sq (R := QuadraticAlgebra ℚ d 0)
      (A := QuadraticAlgebra ℚ d 0)).traceTransfer ℚ).Equivalent
      (weightedSumSquares ℚ ![(2 : ℚ), 2 * d]) :=
  equivalent_traceTransfer_sq_weightedSumSquares d

example (d : ℚ_[2]) :
    ((QuadraticMap.sq (R := QuadraticAlgebra ℚ_[2] d 0)
      (A := QuadraticAlgebra ℚ_[2] d 0)).traceTransfer ℚ_[2]).Equivalent
      (weightedSumSquares ℚ_[2] ![(2 : ℚ_[2]), 2 * d]) :=
  equivalent_traceTransfer_sq_weightedSumSquares d

example : ((QuadraticMap.sq (R := ℂ) (A := ℂ)).traceTransfer ℝ).Equivalent
      (weightedSumSquares ℝ ![(2 : ℝ), -2]) ∧
    Algebra.discr ℝ ![1, Complex.I] = -4 := by
  have hi : Complex.I ∉ Set.range (algebraMap ℝ ℂ) := by
    rintro ⟨r, hr⟩
    simpa using congrArg Complex.im hr
  have hi2 : Complex.I ^ 2 = algebraMap ℝ ℂ (-1 : ℝ) := by simp
  refine ⟨?_, ?_⟩
  · simpa using equivalent_traceTransfer_sq_weightedSumSquares_of_sq
      Complex.finrank_real_complex hi hi2
  · rw [Algebra.discr_one_elem_eq_of_sq_algebraMap Complex.finrank_real_complex hi2 hi]
    norm_num

end TauCeti
