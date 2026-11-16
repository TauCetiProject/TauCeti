/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products over the `attach` of an inserted finset

For `a ∉ s`, a product over `(insert a s).attach`, with a factor depending on the membership
proof, splits into the factor at `a` and the product over `s.attach`
(`Finset.prod_attach_insert`). When `f : {x // x ∈ s} → M` and `s = insert q t` with `q ∉ t` is
only a hypothesis, `s` cannot be rewritten in `∏ x ∈ s.attach, f x`, since the domain of `f`
depends on `s`; `Finset.prod_attach_eq_of_eq_insert` gives the same splitting in that situation.
The additive forms are `Finset.sum_attach_insert` and `Finset.sum_attach_eq_of_eq_insert`.
-/

public section

namespace Finset

variable {ι M : Type*} [DecidableEq ι] [CommMonoid M]

/-- For `a ∉ s`, a product over `(insert a s).attach` splits into the factor at `a` and the product
over `s.attach`, for a factor depending on the membership proof. -/
@[to_additive /-- For `a ∉ s`, a sum over `(insert a s).attach` splits into the term at `a` and
the sum over `s.attach`, for a summand depending on the membership proof. -/]
theorem prod_attach_insert {s : Finset ι} {a : ι} (ha : a ∉ s)
    (f : {x // x ∈ insert a s} → M) :
    ∏ x ∈ (insert a s).attach, f x = f ⟨a, mem_insert_self a s⟩ *
      ∏ x ∈ s.attach, f ⟨x.1, mem_insert_of_mem x.2⟩ := by
  rw [attach_insert, prod_insert (by simpa using ha), prod_image]
  intro x _ y _ h
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

/-- A product over the `attach` of a finset `s = insert q t` with `q ∉ t` splits into the factor at
`q` and the product over the `attach` of `t`, for a factor depending on the membership proof. -/
@[to_additive /-- A sum over the `attach` of a finset `s = insert q t` with `q ∉ t` splits into the
term at `q` and the sum over the `attach` of `t`, for a summand depending on the membership
proof. -/]
theorem prod_attach_eq_of_eq_insert {s t : Finset ι} {q : ι} (hq : q ∉ t) (hs : s = insert q t)
    (f : {x // x ∈ s} → M) :
    ∏ x ∈ s.attach, f x = f ⟨q, hs ▸ mem_insert_self q t⟩ *
      ∏ x ∈ t.attach, f ⟨x.1, hs ▸ mem_insert_of_mem x.2⟩ := by
  subst hs
  exact prod_attach_insert hq f

end Finset
