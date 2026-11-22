/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Cast.Basic

/-!
# Casting and two-point support for `Finsupp.single`

The integer cast commutes with evaluating a finitely supported function with one-point support:
the cast of `Finsupp.single a n b` is `Finsupp.single a (n : R) b` in any additive group with one.

For a sum of two nonzero singletons `Finsupp.single a b + Finsupp.single c d` in a canonically
ordered additive commutative monoid, the support is `{a, c}`, and evaluation vanishes away from
`a` and `c`.
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

/-- The support of a sum of two nonzero singletons `single a b + single c d` is `{a, c}`, without
assuming `a ≠ c`. -/
theorem support_single_add_single' {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M] [Sub M] [OrderedSub M]
    {a c : α} {b d : M} (hb : b ≠ 0) (hd : d ≠ 0) :
    (single a b + single c d).support = {a, c} := by
  rw [support_add_eq_union, support_single a hb, support_single c hd, Finset.singleton_union]

/-- A sum of two nonzero singletons `single a b + single c d` vanishes exactly away from `a` and
`c`. -/
theorem single_add_single_eq_zero_iff {α M : Type*}
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {a c : α} {b d : M} (hb : b ≠ 0) (hd : d ≠ 0) (x : α) :
    (single a b + single c d) x = 0 ↔ x ≠ a ∧ x ≠ c := by
  simp only [add_apply, add_eq_zero, single_apply_eq_zero]
  exact ⟨fun ⟨ha, hc⟩ ↦ ⟨fun h ↦ hb (ha h), fun h ↦ hd (hc h)⟩,
    fun ⟨ha, hc⟩ ↦ ⟨fun h ↦ (ha h).elim, fun h ↦ (hc h).elim⟩⟩

/-- A sum of two nonzero singletons `single a b + single c d` is nonzero exactly at `a` and
`c`. -/
theorem single_add_single_ne_zero_iff {α M : Type*}
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {a c : α} {b d : M} (hb : b ≠ 0) (hd : d ≠ 0) (x : α) :
    (single a b + single c d) x ≠ 0 ↔ x = a ∨ x = c := by
  simpa only [ne_eq, not_and_or, not_not] using
    not_congr (single_add_single_eq_zero_iff hb hd x)

end Finsupp
