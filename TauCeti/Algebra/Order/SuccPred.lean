/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.SuccPred.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Successors in ordered additive groups

In an ordered additive group the translations `x ↦ a + x` are order isomorphisms, so they commute
with the successor function: `a + succ b = succ (a + b)`. In particular `succ a = a + succ 0` and
`succ^[n] a = a + n • succ 0`, so the successor function of a discretely ordered abelian group is
translation by its least positive element `succ 0`. Unlike Mathlib's `SuccAddOrder`, this does not
ask the instance `One` to be that element: on `Lex (Fin n → ℤ)` the instance `One` is the constant
function `1`, which is not the least positive element when `n ≥ 2`.

Consequently, a linearly ordered commutative monoid with a successor order fails to be
`Archimedean` if and only if some element exceeds all finite multiples `n • succ 0`
(`TauCeti.Order.not_archimedean_iff_exists_forall_nsmul_succ_zero_lt`).
-/

public section

namespace TauCeti.Order

open _root_.Order

variable {α : Type*}

section AddGroup

variable [AddGroup α] [PartialOrder α] [AddLeftMono α] [SuccOrder α]

/-- Translations commute with the successor function. -/
theorem add_succ (a b : α) : a + succ b = succ (a + b) :=
  (OrderIso.addLeft a).map_succ b

/-- The successor of `a` is `a` plus the least positive element `succ 0`. -/
theorem succ_eq_add_succ_zero (a : α) : succ a = a + succ 0 := by
  rw [add_succ, add_zero]

/-- Iterating `succ` `n` times adds `n • succ 0`. -/
theorem succ_iterate_eq_add_nsmul_succ_zero (a : α) (n : ℕ) :
    succ^[n] a = a + n • succ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, succ_eq_add_succ_zero, add_assoc, ← succ_nsmul]

/-- The `n`-th iterate of `succ` at `0` is `n • succ 0`. -/
@[simp]
theorem succ_iterate_zero (n : ℕ) : succ^[n] (0 : α) = n • succ 0 := by
  rw [succ_iterate_eq_add_nsmul_succ_zero, zero_add]

end AddGroup

/-- A linearly ordered commutative monoid with a successor order is non-Archimedean if and only if
some element strictly exceeds every finite multiple `n • succ 0`. -/
theorem not_archimedean_iff_exists_forall_nsmul_succ_zero_lt
    [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [SuccOrder α] :
    ¬ Archimedean α ↔ ∃ t : α, ∀ n : ℕ, n • succ 0 < t := by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ h => ?_⟩
  · by_contra! hle
    refine h ⟨fun x y hy => ?_⟩
    obtain ⟨n, hn⟩ := hle x
    exact ⟨n, hn.trans (nsmul_le_nsmul_right (succ_le_of_lt hy) n)⟩
  · have h01 : (0 : α) < succ 0 :=
      lt_succ_of_not_isMax (not_isMax_of_lt (by simpa using ht 0))
    obtain ⟨n, hn⟩ := h.arch t h01
    exact (ht n).not_ge hn

end TauCeti.Order
