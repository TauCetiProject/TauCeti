/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# The Hilbert symbol over a finite field

This file computes the norm-equation Hilbert symbol `TauCeti.hilbertSymbol` over a finite field:
it is always `1`, because the binary form `x ^ 2 - a * y ^ 2` attached to a nonzero `a` is
universal there.

In odd characteristic universality is a counting argument: a quadratic polynomial over a finite
field of odd order takes more than half of the values of the field, so the value sets of `x ^ 2`
and of `a * y ^ 2 + b` cannot be disjoint. In characteristic two squaring is onto, so already
`a * y ^ 2` takes every value.

The statement is the residue-field input for the computation of the symbol of two units of a
nonarchimedean local field away from residue characteristic two, where a solution modulo the
maximal ideal is lifted by Hensel's lemma.

## Main results

* `TauCeti.exists_eq_sq_sub_mul_sq_of_finite`: the binary form `x ^ 2 - a * y ^ 2` attached to a
  nonzero `a` is universal over a finite field.
* `TauCeti.hilbertSymbol_eq_one_of_finite`: the symbol is trivial over a finite field.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter I, §2, Proposition 5.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 62:1b.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [Finite K]

-- Provenance: the odd-characteristic branch follows Mathlib's `ZMod.sq_add_sq`, which is the
-- case `a = -1` over `ZMod p` of the statement below.
/-- **The binary form `x ^ 2 - a * y ^ 2` is universal over a finite field**: for `a ≠ 0` every
element of `K` is of that shape. -/
theorem exists_eq_sq_sub_mul_sq_of_finite {a : K} (ha : a ≠ 0) (b : K) :
    ∃ x y : K, b = x ^ 2 - a * y ^ 2 := by
  have : Fintype K := Fintype.ofFinite K
  by_cases hchar : ringChar K = 2
  · -- Squaring is onto in characteristic two, and there `-(a * y ^ 2) = a * y ^ 2`.
    obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two hchar (b / a)
    have hb : b = y * y * a := (div_eq_iff ha).mp hy
    have h2 : (2 : K) = 0 := by
      exact (ringChar.spec K 2).mpr (by rw [hchar])
    exact ⟨0, y, by linear_combination hb + a * y ^ 2 * h2⟩
  · have hcard : Fintype.card K % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (Fintype.card K) with hc | hc
      · exact absurd (FiniteField.even_card_iff_char_two.mpr hc) hchar
      · exact hc
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic (R := K)
      (f := X ^ 2 - C b) (g := -(C a * X ^ 2)) (degree_X_pow_sub_C (by norm_num) b)
      (by rw [degree_neg]; exact degree_C_mul_X_pow 2 ha) hcard
    refine ⟨x, y, ?_⟩
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_neg, eval_mul] at hxy
    linear_combination -hxy

/-- Over a finite field the Hilbert symbol is always `1`. -/
@[simp]
theorem hilbertSymbol_eq_one_of_finite (a b : Kˣ) : hilbertSymbol a b = 1 :=
  (hilbertSymbol_eq_one_iff a b).mpr (exists_eq_sq_sub_mul_sq_of_finite a.ne_zero (b : K))

end TauCeti
