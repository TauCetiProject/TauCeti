/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Square roots and the binomial `X ^ n - C a`

Mathlib's Kummer theory of `X ^ n - C a` (in `Mathlib/FieldTheory/KummerExtension.lean`) runs
through a primitive `n`-th root of unity, which is unavailable for `n = 2` in characteristic `2`.
This file records the elementary facts that need no root of unity: membership in the root set of
`X ^ n - C a` is the equation `x ^ n = a`, and for `n = 2` a single square root `δ` of `a` already
splits the binomial and generates its splitting field, because the only other root is `-δ`.

## Main results

* `Polynomial.mem_rootSet_X_pow_sub_C`: a point of an extension is a root of `X ^ n - C a` exactly
  when its `n`-th power is `a`.
* `IntermediateField.adjoin_rootSet_X_pow_two_sub_C`: a square root of `a` generates the root-set
  adjunction of `X ^ 2 - C a`.
* `Polynomial.splits_map_X_pow_two_sub_C`: a square root of `a` in an extension splits
  `X ^ 2 - C a` there.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

universe u v

section RootSet

variable {F : Type u} [CommRing F] {E : Type v} [Field E] [Algebra F E] {a : F}

/-- A point of an extension is a root of `X ^ n - C a` exactly when its `n`-th power is `a`. -/
@[simp]
theorem _root_.Polynomial.mem_rootSet_X_pow_sub_C {n : ℕ} (hn : n ≠ 0) {x : E} :
    x ∈ ((X : F[X]) ^ n - C a).rootSet E ↔ x ^ n = algebraMap F E a := by
  rw [(monic_X_pow_sub_C a hn).mem_rootSet, map_sub, aeval_X_pow, aeval_C,
    sub_eq_zero]

end RootSet

section Adjoin

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {a : F} {δ : E}

/-- Over a field, a square root `δ` of `a` generates the whole splitting field of `X ^ 2 - C a`,
because the only other root is `-δ`. -/
theorem _root_.IntermediateField.adjoin_rootSet_X_pow_two_sub_C
    (hδ : δ ^ 2 = algebraMap F E a) :
    IntermediateField.adjoin F (((X : F[X]) ^ 2 - C a).rootSet E) = F⟮δ⟯ := by
  have hmem : δ ∈ ((X : F[X]) ^ 2 - C a).rootSet E :=
    (Polynomial.mem_rootSet_X_pow_sub_C two_ne_zero).mpr hδ
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr fun x hx ↦ ?_)
    (IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin F _ hmem))
  have hx' : x ^ 2 = algebraMap F E a := (Polynomial.mem_rootSet_X_pow_sub_C two_ne_zero).mp hx
  have hfac : (x - δ) * (x + δ) = 0 := by linear_combination hx' - hδ
  rcases mul_eq_zero.mp hfac with h | h
  · exact (sub_eq_zero.mp h) ▸ IntermediateField.mem_adjoin_simple_self F δ
  · exact (eq_neg_of_add_eq_zero_left h) ▸ neg_mem (IntermediateField.mem_adjoin_simple_self F δ)

end Adjoin

section Splits

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E] {a : F} {δ : E}

/-- A square root of `a` in `E` splits `X ^ 2 - C a` there: the two linear factors are `X - C δ`
and `X + C δ`. Unlike `Polynomial.X_pow_sub_C_splits_of_isPrimitiveRoot` this needs no primitive
root of unity, so it also covers characteristic `2`, where the two factors coincide. -/
theorem _root_.Polynomial.splits_map_X_pow_two_sub_C (hδ : δ ^ 2 = algebraMap F E a) :
    (((X : F[X]) ^ 2 - C a).map (algebraMap F E)).Splits := by
  have hmap : ((X : F[X]) ^ 2 - C a).map (algebraMap F E) = (X - C δ) * (X - C (-δ)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hδ, map_pow, map_neg]
    ring
  rw [hmap]
  exact (Splits.X_sub_C δ).mul (Splits.X_sub_C (-δ))

end Splits

end TauCeti
