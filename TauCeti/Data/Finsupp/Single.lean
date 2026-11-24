/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Int.Cast.Basic

/-!
# Single-coordinate casting and splitting for finitely supported functions

`Finsupp.intCast_single_apply` commutes integer casts with evaluating a one-point finitely supported
function. Over any additive commutative monoid and decidable index type,
`Finsupp.eraseSingleEquiv k` decomposes `α →₀ M` into its value at `k` and the complementary
subtype `{ a : α →₀ M // a k = 0 }`.
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

section EraseSingle

variable {α M : Type*} [DecidableEq α] [AddCommMonoid M]

/-- Equivalence splitting `a : α →₀ M` into `(a k, a.erase k)` with inverse
`(m, a₀) ↦ a₀.val + single k m`. -/
noncomputable def eraseSingleEquiv (k : α) : (α →₀ M) ≃ M × { a : α →₀ M // a k = 0 } where
  toFun a := (a k, ⟨a.erase k, erase_same⟩)
  invFun p := p.2.val + single k p.1
  left_inv a := erase_add_single k a
  right_inv := fun ⟨_, a₀⟩ ↦ Prod.ext (by simp [a₀.property]) <| Subtype.ext <| ext fun i ↦ by
    by_cases hik : i = k <;> simp [hik, a₀.property]

@[simp]
theorem eraseSingleEquiv_apply_fst (k : α) (a : α →₀ M) :
    (eraseSingleEquiv k a).1 = a k :=
  (rfl)

@[simp]
theorem coe_eraseSingleEquiv_apply_snd (k : α) (a : α →₀ M) :
    ((eraseSingleEquiv k a).2 : α →₀ M) = a.erase k :=
  (rfl)

@[simp]
theorem eraseSingleEquiv_symm_apply (k : α) (p : M × { a : α →₀ M // a k = 0 }) :
    (eraseSingleEquiv k).symm p = p.2.val + single k p.1 :=
  (rfl)

end EraseSingle

end Finsupp
