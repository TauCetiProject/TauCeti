/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.Basic

/-!
# The field `ℚ(i)`, presented by a square root of `−1`

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² + 1`, that is `K = ℚ(i)` presented by a square root of `−1`. This file records
the basic shape of this presentation, shared by the worked example: the defining identity
`θ² = −1`, the minimal polynomial in the radicand form `X² − C (−1)` of the quadratic-field
theory, and `[K : ℚ] = 2`.

## Main results

* `TauCeti.NumberField.GaussianRationals.sq_eq_neg_one`: `θ² = −1`.
* `TauCeti.NumberField.GaussianRationals.isUnit`: `θ` is a unit, since `θ · (−θ) = 1`.
* `TauCeti.NumberField.GaussianRationals.finrank_eq_two`: `[K : ℚ] = 2`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.NumberField.GaussianRationals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- The minimal polynomial `X² + 1` in the radicand form `X² − C (−1)` of the quadratic-field
theory. -/
theorem minpoly_eq_X_sq_sub_C (hmin : minpoly ℤ θ = X ^ 2 + 1) :
    minpoly ℤ θ = X ^ 2 - C (-1) := by
  rw [hmin, map_neg, map_one, sub_neg_eq_add]

omit [NumberField K] in
/-- The defining identity `θ² = −1`. -/
@[simp]
theorem sq_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 + 1) : θ ^ 2 = -1 := by
  rw [gen_sq (minpoly_eq_X_sq_sub_C hmin), map_neg, map_one]

omit [NumberField K] in
/-- `θ` is a unit of `𝓞 K`: `θ · (−θ) = 1`. -/
theorem isUnit (hmin : minpoly ℤ θ = X ^ 2 + 1) : IsUnit θ :=
  IsUnit.of_mul_eq_one (-θ) (by linear_combination -(sq_eq_neg_one hmin))

/-- `ℚ(i)` has degree `2`. -/
theorem finrank_eq_two (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Module.finrank ℚ K = 2 :=
  finrank_rat_eq_two (minpoly_eq_X_sq_sub_C hmin) hgen

end TauCeti.NumberField.GaussianRationals
