/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Setoid quotient helpers

This file records small generic additions to Mathlib's `Setoid` quotient API.

## Main declarations

* `TauCeti.Setoid.map_of_le_mk`: the quotient map induced by a setoid inequality sends a
  representative to the same representative in the larger quotient.
* `TauCeti.Setoid.sameCycle_toPerm_iff`: the orbit relation of an involution has classes of size
  at most two.
-/

public section

namespace TauCeti

namespace Setoid

/-- Two points lie in the same orbit of an involution exactly when they are equal or one is the
image of the other. -/
theorem sameCycle_toPerm_iff {α : Type*} (f : α → α) (hf : Function.Involutive f) (a b : α) :
    (hf.toPerm f).SameCycle a b ↔ a = b ∨ a = f b := by
  constructor
  · rintro ⟨i, hi⟩
    have hp : (hf.toPerm f) ^ 2 = 1 := by
      ext x
      exact hf x
    rw [zpow_eq_zpow_emod' i hp] at hi
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · left
      simpa [h] using hi
    · right
      have hfa : f a = b := by simpa [h] using hi
      calc
        a = f (f a) := (hf a).symm
        _ = f b := congrArg f hfa
  · rintro (rfl | h)
    · exact Equiv.Perm.SameCycle.rfl
    · refine ⟨1, ?_⟩
      have : f a = b := by
        calc
          f a = f (f b) := congrArg f h
          _ = b := hf b
      simpa using this

/-- The quotient map induced by a setoid inequality sends a representative to the same
representative in the larger quotient. -/
@[simp]
lemma map_of_le_mk {α : Type*} {s t : Setoid α} (h : s ≤ t) (x : α) :
    _root_.Setoid.map_of_le h (Quotient.mk'' x : Quotient s) =
      (Quotient.mk'' x : Quotient t) :=
  Quotient.map'_mk'' id h x

end Setoid

end TauCeti
