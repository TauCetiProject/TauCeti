/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The product of the linear factors over a finite field

Over a finite field `K` with `q` elements, the polynomial `X ^ q - X` is monic of degree `q` and
has every element of `K` as a simple root (`FiniteField.roots_X_pow_card_sub_X`), so it is the
product of the linear factors `X - a` over all `a : K`.

## Main results

* `TauCeti.FiniteField.prod_X_sub_C_eq_X_pow_card_sub_X`: `∏ a : K, (X - a) = X ^ q - X`.
-/

public section

open Polynomial

namespace TauCeti.FiniteField

variable (K : Type*) [Field K] [Fintype K]

/-- Over a finite field `K` with `q` elements, `X ^ q - X` is the product of the linear factors
`X - a` over all `a : K`. -/
theorem prod_X_sub_C_eq_X_pow_card_sub_X :
    ∏ a : K, (X - C a) = (X ^ Fintype.card K - X : K[X]) := by
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  have hroots := _root_.FiniteField.roots_X_pow_card_sub_X K
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (monic_X_pow_sub (p := (X : K[X])) (by rw [degree_X]; exact_mod_cast hcard))
    (by rw [natDegree_X_pow_sub_X hcard, hroots]; simp)
  rwa [hroots] at h

end TauCeti.FiniteField
