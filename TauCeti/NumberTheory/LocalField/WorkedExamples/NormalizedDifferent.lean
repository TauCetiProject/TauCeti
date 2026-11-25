/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.LocalField.Discriminant.Normalized
import TauCeti.NumberTheory.LocalField.WorkedExamples.CyclotomicEight.Basic
import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.NegOne.Ramification
import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Two
import TauCeti.NumberTheory.LocalField.WorkedExamples.TriadicSqrtThree
import TauCeti.NumberTheory.LocalField.WorkedExamples.UnramifiedQuadratic

/-!
# Examples of normalized differents

These computations compare the unramified and tame cases with three wild dyadic extensions.
In particular, the different exponent three of `ℚ₂(√2)` normalizes to `3/2`, whereas the
cyclotomic extension `ℚ₂(ζ₈)` has normalized different two.
-/

namespace TauCeti

example : localRootDiscrExp ℚ_[2] UnramifiedQuadratic = 0 :=
  (localRootDiscrExp_eq_zero_iff _ _).2 inferInstance

example : localRootDiscrExp ℚ_[3] TriadicSqrtThree = 1 / 2 := by
  rw [(localRootDiscrExp_eq_one_sub_inv_iff _ _).2 TriadicSqrtThree.isTamelyRamified,
    TriadicSqrtThree.ramificationIndex_eq_two]
  norm_num

example : localRootDiscrExp ℚ_[2] DyadicSqrtNegOne = 1 := by
  rw [localRootDiscrExp_def, DyadicSqrtNegOne.discriminantExponent_eq_two,
    QuadraticAlgebra.finrank_eq_two (-1 : ℚ_[2]) 0]
  norm_num

example : localRootDiscrExp ℚ_[2] DyadicSqrtTwo = 3 / 2 := by
  rw [localRootDiscrExp_eq_differentExponent_div_ramificationIndex,
    DyadicSqrtTwo.differentExponent_eq_three,
    DyadicSqrtTwo.ramificationIndex_eq_two]
  norm_num

example : localRootDiscrExp ℚ_[2] DyadicCyclotomicEight = 2 := by
  rw [localRootDiscrExp_eq_differentExponent_div_ramificationIndex,
    DyadicCyclotomicEight.differentExponent_eq_eight,
    DyadicCyclotomicEight.ramificationIndex_eq_four]
  norm_num

end TauCeti
