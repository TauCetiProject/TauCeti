/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Int.Cast.Basic

/-!
# Casting and two-point support for `Finsupp.single`

The integer cast commutes with evaluating a finitely supported function with one-point support:
the cast of `Finsupp.single a n b` is `Finsupp.single a (n : R) b` in any additive group with one.

A nonzero singleton `Finsupp.single a b` vanishes away from `a`
(`Finsupp.single_apply_eq_zero_of_ne_zero`). For a sum of two nonzero singletons
`Finsupp.single a b + Finsupp.single c d` in a canonically ordered additive commutative monoid, the
support is `{a, c}`, and evaluation vanishes away from `a` and `c`.
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

/-- Evaluation of a nonzero singleton `single a b` vanishes away from `a`. -/
@[simp]
theorem single_apply_eq_zero_of_ne_zero {α M : Type*} [Zero M] {a x : α} {b : M} (hb : b ≠ 0) :
    single a b x = 0 ↔ x ≠ a :=
  single_apply_eq_zero.trans ⟨fun h hxa ↦ hb (h hxa), fun h hxa ↦ (h hxa).elim⟩

/-- A sum of two nonzero singletons `single a b + single c d` vanishes exactly away from `a` and
`c`. -/
theorem single_add_single_eq_zero_iff {α M : Type*}
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {a c : α} {b d : M} (hb : b ≠ 0) (hd : d ≠ 0) (x : α) :
    (single a b + single c d) x = 0 ↔ x ≠ a ∧ x ≠ c := by
  simp only [add_apply, add_eq_zero, single_apply_eq_zero_of_ne_zero hb,
    single_apply_eq_zero_of_ne_zero hd]

/-- A sum of two nonzero singletons `single a b + single c d` is nonzero exactly at `a` and
`c`. -/
theorem single_add_single_ne_zero_iff {α M : Type*}
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {a c : α} {b d : M} (hb : b ≠ 0) (hd : d ≠ 0) (x : α) :
    (single a b + single c d) x ≠ 0 ↔ x = a ∨ x = c := by
  simpa only [ne_eq, not_and_or, not_not] using
    not_congr (single_add_single_eq_zero_iff hb hd x)

/-- The support of a sum of two nonzero singletons `single a b + single c d` is `{a, c}`, without
assuming `a ≠ c`. -/
theorem support_single_add_single' {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {a c : α} {b d : M} (hb : b ≠ 0) (hd : d ≠ 0) :
    (single a b + single c d).support = {a, c} := by
  ext x
  rw [mem_support_iff, single_add_single_ne_zero_iff hb hd]
  simp

end Finsupp
