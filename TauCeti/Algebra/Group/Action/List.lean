/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Action.Defs

/-!
# Actions of list products

Evaluation of a list product and its inverse in a monoid or group action as a right fold and a
left fold of inverse actions (`List.prod_smul`, `List.inv_prod_smul`).
-/

public section

namespace List

/-- Evaluating a list product in a monoid action applies the factors from right to left. -/
theorem prod_smul {M α : Type*} [Monoid M] [MulAction M α] (l : List M) (a : α) :
    l.prod • a = l.foldr (· • ·) a := by
  induction l with
  | nil => simp
  | cons m l ih => simp [mul_smul, ih]

/-- Evaluating the inverse of a list product in a group action applies the inverse factors from
left to right. -/
theorem inv_prod_smul {G α : Type*} [Group G] [MulAction G α] (l : List G) (a : α) :
    (l.prod)⁻¹ • a = l.foldl (fun x g => g⁻¹ • x) a := by
  induction l generalizing a with
  | nil => simp
  | cons g l ih => simp [mul_inv_rev, mul_smul, ih]

end List
