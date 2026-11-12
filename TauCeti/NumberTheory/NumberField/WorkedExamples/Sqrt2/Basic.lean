/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.Basic

/-!
# The field `ℚ(√2)`

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² − 2`, that is `K = ℚ(√2)`. This file records the basic shape of this
presentation, shared by the worked examples: `θ² = 2` and `[K : ℚ] = 2`.

## Main results

* `TauCeti.NumberField.Sqrt2.sq_eq_two`: `θ² = 2`.
* `TauCeti.NumberField.Sqrt2.finrank_eq_two`: `[K : ℚ] = 2`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt2

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- The minimal polynomial `X² − 2` in the radicand form `X² − C 2` of the quadratic-field
theory. -/
private theorem minpoly_eq_X_sq_sub_C (hmin : minpoly ℤ θ = X ^ 2 - 2) :
    minpoly ℤ θ = X ^ 2 - C 2 := by
  rw [hmin, map_ofNat]

omit [NumberField K] in
/-- The defining identity `θ² = 2`. -/
@[simp]
theorem sq_eq_two (hmin : minpoly ℤ θ = X ^ 2 - 2) : θ ^ 2 = 2 := by
  rw [gen_sq (minpoly_eq_X_sq_sub_C hmin), map_ofNat]

/-- `ℚ(√2)` has degree `2`. -/
theorem finrank_eq_two (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Module.finrank ℚ K = 2 :=
  finrank_rat_eq_two (minpoly_eq_X_sq_sub_C hmin) hgen

end TauCeti.NumberField.Sqrt2
