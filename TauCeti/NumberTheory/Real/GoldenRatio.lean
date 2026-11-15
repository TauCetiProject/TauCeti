/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio

import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# The complex roots of `X² - X - 1`

The golden ratio `φ` and its conjugate `ψ` are the two roots of `X² - X - 1`. This file records
the complex root multiset of this polynomial, which is used to compute with the conjugates of `φ`,
for instance to show that `φ` is a Pisot number and that the Mahler measure of `X² - X - 1` is `φ`.

## Main results

* `TauCeti.aroots_X_sq_sub_X_sub_one`: the complex roots of `X² - X - 1` are `φ` and `ψ`.
-/

public section

open Polynomial

namespace TauCeti

/-- The complex roots of `X² - X - 1` are the golden ratio `φ` and its conjugate `ψ`. -/
theorem aroots_X_sq_sub_X_sub_one :
    (X ^ 2 - X - 1 : ℤ[X]).aroots ℂ = {(Real.goldenRatio : ℂ), (Real.goldenConj : ℂ)} := by
  have hP : (X ^ 2 - X - 1 : ℤ[X]) = C 1 * X ^ 2 + C (-1) * X + C (-1) := by
    simp [sub_eq_add_neg]
  rw [hP, aroots_quadratic_eq_pair_iff_of_ne_zero' (by simp), map_neg, map_one, neg_neg, div_one,
    div_one]
  exact ⟨mod_cast Real.goldenRatio_add_goldenConj, mod_cast Real.goldenRatio_mul_goldenConj⟩

end TauCeti
