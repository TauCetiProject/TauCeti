/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The infinite places of a quadratic field `ℚ(√d)`

The signature of `ℚ(√d)` is read off the sign of `d`: for `d < 0` the field is totally complex
and for `0 ≤ d` it is totally real. Both are special cases of the generic square-root criteria
`NumberField.isTotallyComplex_of_sq_ratCast_of_neg` and
`NumberField.isTotallyReal_of_sq_ratCast_of_nonneg`, applied to the generator `θ` with `θ² = d`.
Total reality needs the generator hypothesis as well, since a real square root only forces the
embeddings fixed on `ℚ(θ)` to be real.

## Main results

* `NumberField.isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg`.
* `NumberField.isTotallyReal_of_minpoly_eq_X_sq_sub_C_of_nonneg`.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **An imaginary quadratic field is totally complex.** Any number field `K` containing an
algebraic integer `θ` with `minpoly ℤ θ = X² - d` and `d < 0` is totally complex — in particular the
imaginary quadratic field `ℚ(√d)`. -/
theorem isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hd : d < 0) : IsTotallyComplex K :=
  isTotallyComplex_of_sq_ratCast_of_neg (x := (θ : K)) (r := (d : ℚ))
    (coe_gen_sq_ratCast hmin) (by exact_mod_cast hd)

/-- **A real quadratic field is totally real.** A number field `K` generated over `ℚ` by an
algebraic integer `θ` with `minpoly ℤ θ = X² - d` and `0 ≤ d` is totally real — in particular
the real quadratic field `ℚ(√d)`. -/
theorem isTotallyReal_of_minpoly_eq_X_sq_sub_C_of_nonneg (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 ≤ d) : IsTotallyReal K :=
  isTotallyReal_of_sq_ratCast_of_nonneg (x := (θ : K)) (r := (d : ℚ))
    (coe_gen_sq_ratCast hmin) hgen (by exact_mod_cast hd)

end NumberField
