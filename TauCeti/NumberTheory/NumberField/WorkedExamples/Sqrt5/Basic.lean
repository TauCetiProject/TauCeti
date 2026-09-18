/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.Basic

/-!
# The field `ℚ(√5)`, presented by the golden ratio

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² − X − 1`, that is `K = ℚ(√5)` presented by `θ = (1 + √5)/2`. This file
records the basic shape of this presentation, shared by the worked example: the minimal
polynomial in the form `X² − X + C ((1 − 5)/4)` used by the quadratic splitting laws, and
`[K : ℚ] = 2`.

## Main results

* `TauCeti.NumberField.Sqrt5.finrank_eq_two`: `[K : ℚ] = 2`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- The minimal polynomial `X² − X − 1` in the form `X² − X + C ((1 - 5) / 4)` of the quadratic
splitting laws. -/
theorem minpoly_eq_X_sq_sub_X_add (hmin : minpoly ℤ θ = X ^ 2 - X - 1) :
    minpoly ℤ θ = X ^ 2 - X + C ((1 - 5) / 4) := by
  rw [hmin]; norm_num [sub_eq_add_neg]

/-- `ℚ(√5)` has degree `2`. -/
theorem finrank_eq_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Module.finrank ℚ K = 2 :=
  NumberField.finrank_rat_eq_two_of_minpoly_eq_X_sq_sub_X_add (minpoly_eq_X_sq_sub_X_add hmin)
    hgen

end TauCeti.NumberField.Sqrt5
