/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.Iterate

/-!
# Simulating the iterates of one function by another

Read `f : α → α` and `g : β → β` as the one-step transitions of two discrete-time systems and
`Φ : α → β` as a translation of the states of the first into states of the second. Say that `g`
*simulates* `f` along `Φ` when every single step of `f` is matched by finitely many steps of `g`
on the translated states. `TauCeti.exists_iterate_of_forall_exists_iterate` says that a
simulation of the single steps is automatically a simulation of all the iterates, so a run of `f`
of any length may be replayed as a run of `g`.

This is the form in which a coarse system is compared with a finer one that refines each of its
steps into a finite stretch of its own, of a length that may vary from state to state: only the
single steps have to be inspected, and the lengths of the stretches never have to be tracked.

## Main results

* `TauCeti.exists_iterate_of_forall_exists_iterate`: a simulation of single steps is a simulation
  of iterates.
-/

public section

namespace TauCeti

/-- If every step of `f` is simulated by finitely many steps of `g` along `Φ`, then so is every
iterate of `f`. -/
theorem exists_iterate_of_forall_exists_iterate {α β : Type*} {f : α → α} {g : β → β}
    {Φ : α → β} (h : ∀ a, ∃ m, g^[m] (Φ a) = Φ (f a)) (n : ℕ) (a : α) :
    ∃ m, g^[m] (Φ a) = Φ (f^[n] a) := by
  induction n generalizing a with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m₁, h₁⟩ := h a
    obtain ⟨m₂, h₂⟩ := ih (f a)
    exact ⟨m₂ + m₁, by rw [Function.iterate_add_apply, h₁, h₂, Function.iterate_succ_apply]⟩

end TauCeti
