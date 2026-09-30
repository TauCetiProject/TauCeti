/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End

/-!
# Coordinates of `mulAutArrow`

Mathlib's `mulAutArrow` lets a group `G` acting on `A` act on `A → M` by multiplicative
automorphisms. This file records that action's evaluation formula in plain coordinates, supporting
coordinate calculations in semidirect products built from `mulAutArrow`, particularly
arbitrary-action permutation wreath products.

## Main results

* `TauCeti.mulAutArrow_apply_apply_eq_apply_inv_smul`: `mulAutArrow g f a = f (g⁻¹ • a)`.
-/

public section

namespace TauCeti

variable {G M A : Type*} [Group G] [MulAction G A] [Monoid M]

/-- The automorphism `mulAutArrow g` of `A → M` evaluates coordinates through `g⁻¹`:
`mulAutArrow g f a = f (g⁻¹ • a)`. -/
-- `mulAutArrow_apply_apply` leaves `(g • f) a` for the non-instance `arrowAction`; its
-- `arrowAction_smul` is stated with a bare `SMul.smul` and does not match, so the remaining
-- step is the defining equation of that action. The `high` priority makes `simp` use this
-- lemma before Mathlib's `mulAutArrow_apply_apply`, which has the same left-hand side.
@[simp high]
theorem mulAutArrow_apply_apply_eq_apply_inv_smul (g : G) (f : A → M) (a : A) :
    mulAutArrow g f a = f (g⁻¹ • a) := by
  rw [mulAutArrow_apply_apply]
  rfl

end TauCeti
