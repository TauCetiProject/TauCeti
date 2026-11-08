/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End

/-!
# Actions of `MulAut`: conjugation laws and coordinates of `mulAutArrow`

A group `G` acts on any type `α` with an action of `MulAut G` through the inner automorphisms,
`s ↦ MulAut.conj s • (-)`. This file records the laws making this an action of `G` in the form
`MulAut.conj s • a`, in which Mathlib writes the conjugate `sHs⁻¹` of a subgroup `H`.

Mathlib's `mulAutArrow` lets a group `G` acting on `A` act on `A → M` by multiplicative
automorphisms. This file also records that action's evaluation formula in plain coordinates,
supporting coordinate calculations in semidirect products built from `mulAutArrow`, particularly
arbitrary-action permutation wreath products.

## Main results

* `TauCeti.conj_one_smul`, `TauCeti.conj_mul_smul`, `TauCeti.conj_inv_smul_smul`: conjugation is
  an action of `G` on any type on which `MulAut G` acts, for instance on the subgroups of `G`.
* `TauCeti.mulAutArrow_apply_apply_eq_apply_inv_smul`: `mulAutArrow g f a = f (g⁻¹ • a)`.
-/

public section

namespace TauCeti

section Conj

variable {G α : Type*} [Group G] [MulAction (MulAut G) α]

/-- Conjugating by `1` acts trivially, for instance on the subgroups of `G`. -/
theorem conj_one_smul (a : α) : MulAut.conj (1 : G) • a = a := by
  simp

/-- Conjugating by `s * t` is conjugating by `t` and then by `s`, for instance on the subgroups
of `G`. -/
theorem conj_mul_smul (s t : G) (a : α) :
    MulAut.conj (s * t) • a = MulAut.conj s • (MulAut.conj t • a) := by
  rw [map_mul, mul_smul]

/-- Conjugating by `s⁻¹` undoes conjugating by `s`, for instance on the subgroups of `G`. -/
theorem conj_inv_smul_smul (s : G) (a : α) : MulAut.conj s⁻¹ • (MulAut.conj s • a) = a := by
  rw [map_inv, inv_smul_smul]

end Conj

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
