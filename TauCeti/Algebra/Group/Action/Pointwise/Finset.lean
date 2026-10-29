/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Finset.SymmDiff

/-!
# Symmetric differences of translates of finite sets

A group element `g` acting on a type `X` moves a finite set `F ⊆ X` to a translate `g • F` of the
same size, so `g • F` has as many points outside `F` as `F` has outside `g • F`. Hence the
symmetric difference `g • F ∆ F` has twice as many points as `g • F \ F`. Følner-type arguments
use this to pass between symmetric differences and one-sided differences.

## Main results

* `Finset.card_smul_finset_symmDiff`: `|gF △ F| = 2 |gF \ F|` for a finite set `F`.
-/

public section

open scoped Pointwise symmDiff

namespace Finset

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- A translate `g • F` of a finite set has as many points outside `F` as `F` has outside `g • F`,
so its symmetric difference with `F` has twice as many points as `g • F \ F`. -/
theorem card_smul_finset_symmDiff (g : G) (F : Finset X) : #((g • F) ∆ F) = 2 * #(g • F \ F) := by
  rw [symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff,
    ← card_sdiff_comm (card_smul_finset g F), Nat.two_mul]

end Finset
