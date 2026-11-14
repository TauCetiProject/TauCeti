/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products over the `attach` of an inserted finset

A product over the `attach` of a finset `s = insert q t`, with a factor depending on the
membership proof, splits into the factor at `q` and the product over the `attach` of `t`
(`Finset.prod_attach_eq_of_eq_insert`). Additively, this is `Finset.sum_attach_eq_of_eq_insert`.
-/

public section

namespace Finset

variable {ι M : Type*} [DecidableEq ι] [CommMonoid M]

/-- A product over the `attach` of a finset `s = insert q t` splits into the factor at `q` and the
product over the `attach` of `t`, for a factor depending on the membership proof. -/
@[to_additive /-- A sum over the `attach` of a finset `s = insert q t` splits into the term at `q`
and the sum over the `attach` of `t`, for a summand depending on the membership proof. -/]
theorem prod_attach_eq_of_eq_insert {s t : Finset ι} {q : ι} (hq : q ∉ t) (hs : s = insert q t)
    (G : (x : ι) → x ∈ s → M) :
    ∏ x ∈ s.attach, G x.1 x.2 = G q (hs ▸ mem_insert_self q t) *
      ∏ x ∈ t.attach, G x.1 (hs ▸ mem_insert_of_mem x.2) := by
  subst hs
  rw [attach_insert, prod_insert (by simpa using hq), prod_image]
  intro x _ y _ h
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

end Finset
