/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The leading coefficient of a rational function

Every rational function `f ∈ K(X)` is uniquely `f = p / q` with `p, q ∈ K[X]` coprime and `q` monic
(`RatFunc.num` and `RatFunc.denom`). Its **leading coefficient** is the leading coefficient of `p`.
It is multiplicative, so for any representation `f = p / q` with `q ≠ 0` it is the quotient of the
leading coefficients of `p` and `q`. It is the value at infinity of `f · X ^ (-deg f)`, and it
describes the specialization of Milnor K-theory at the place at infinity of `K(X)`.

## Main definitions

* `RatFunc.leadingCoeffHom`: the leading coefficient `K(X) →*₀ K`.

## Main results

* `RatFunc.leadingCoeffHom_apply`: the leading coefficient of `f` is that of `f.num`.
* `RatFunc.leadingCoeffHom_algebraMap`: on polynomials it is `Polynomial.leadingCoeff`.
* `RatFunc.leadingCoeffHom_div_algebraMap`: `lc(p / q) = lc(p) / lc(q)`.
-/

public section

namespace RatFunc

open Polynomial

variable {K : Type*} [Field K]

/-- The **leading coefficient** of a rational function, as a multiplicative map `K(X) →*₀ K`: the
leading coefficient of its numerator `f.num`, the denominator `f.denom` being monic. It is
multiplicative, so `lc(p / q) = lc(p) / lc(q)` for all polynomials `p` and `q`
(`RatFunc.leadingCoeffHom_div_algebraMap`). -/
noncomputable def leadingCoeffHom : RatFunc K →*₀ K where
  toFun f := f.num.leadingCoeff
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by
    have h := congrArg leadingCoeff (num_denom_mul f g)
    simpa [(monic_denom _).leadingCoeff] using h

theorem leadingCoeffHom_apply (f : RatFunc K) : leadingCoeffHom f = f.num.leadingCoeff :=
  (rfl)

/-- On polynomials the leading coefficient is `Polynomial.leadingCoeff`. -/
@[simp]
theorem leadingCoeffHom_algebraMap (p : K[X]) :
    leadingCoeffHom (algebraMap K[X] (RatFunc K) p) = p.leadingCoeff := by
  rw [leadingCoeffHom_apply, num_algebraMap]

/-- A constant is its own leading coefficient. -/
@[simp]
theorem leadingCoeffHom_C (c : K) : leadingCoeffHom (C c) = c := by
  rw [← algebraMap_C, leadingCoeffHom_algebraMap, leadingCoeff_C]

@[simp]
theorem leadingCoeffHom_X : leadingCoeffHom (X : RatFunc K) = 1 := by
  rw [← algebraMap_X, leadingCoeffHom_algebraMap, leadingCoeff_X]

/-- The leading coefficient of a quotient of polynomials is the quotient of their leading
coefficients. -/
theorem leadingCoeffHom_div_algebraMap (p q : K[X]) :
    leadingCoeffHom (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      p.leadingCoeff / q.leadingCoeff := by
  rw [map_div₀, leadingCoeffHom_algebraMap, leadingCoeffHom_algebraMap]

end RatFunc
