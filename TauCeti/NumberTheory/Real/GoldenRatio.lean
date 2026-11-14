/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Algebraic and numerical properties of the golden ratio

The golden ratio `φ` and its conjugate `ψ` are the two roots of `X² - X - 1`. This file records
the complex root multiset of this polynomial — used to compute with the conjugates of `φ`, for
instance to show that `φ` is a Pisot number and that the Mahler measure of `X² - X - 1` is `φ` —
together with the elementary bound `log φ < 1 / 2` (`φ² < e`).

## Main results

* `TauCeti.aroots_X_sq_sub_X_sub_one`: the complex roots of `X² - X - 1` are `φ` and `ψ`.
* `TauCeti.log_goldenRatio_lt_one_half`: `Real.log Real.goldenRatio < 1 / 2`.
-/

public section

open Polynomial
open scoped Real

namespace TauCeti

/-- The complex roots of `X² - X - 1` are the golden ratio `φ` and its conjugate `ψ`. -/
theorem aroots_X_sq_sub_X_sub_one :
    (X ^ 2 - X - 1 : ℤ[X]).aroots ℂ = {(Real.goldenRatio : ℂ), (Real.goldenConj : ℂ)} := by
  have hP : (X ^ 2 - X - 1 : ℤ[X]) = C 1 * X ^ 2 + C (-1) * X + C (-1) := by
    simp [sub_eq_add_neg]
  rw [hP, aroots_quadratic_eq_pair_iff_of_ne_zero' (by simp), map_neg, map_one, neg_neg, div_one,
    div_one]
  exact ⟨mod_cast Real.goldenRatio_add_goldenConj, mod_cast Real.goldenRatio_mul_goldenConj⟩

/-- The natural logarithm of the golden ratio is strictly less than `1 / 2`. -/
theorem log_goldenRatio_lt_one_half : Real.log Real.goldenRatio < 1 / 2 := by
  have hφ_sq : Real.goldenRatio ^ 2 < Real.exp 1 := by
    have h21 : Real.goldenRatio ^ 2 < 21 / 8 := by
      have h5 : √(5 : ℝ) < 9 / 4 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
      rw [Real.goldenRatio_sq, Real.goldenRatio]; linarith
    exact h21.trans (by linarith [Real.exp_one_gt_d9])
  have h := (Real.log_lt_log_iff (pow_pos Real.goldenRatio_pos 2) (Real.exp_pos 1)).mpr hφ_sq
  rw [Real.log_pow, Nat.cast_ofNat, Real.log_exp] at h
  linarith

end TauCeti
