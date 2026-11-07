/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Computability.StateTransition

/-!
# Induction along a finite execution

Propagate an invariant, indexed by the number of steps, along an `EvalsTo` witness.
-/

public section

namespace StateTransition

/-- Induction along a run `h` from `a` to `b`: if `motive 0 a` holds and every step `f c = some c'`
takes `motive n c` to `motive (n + 1) c'`, then `motive h.steps b` holds. -/
theorem EvalsTo.induction_on {σ : Type*} {f : σ → Option σ} {a b : σ} (h : EvalsTo f a (some b))
    (motive : ℕ → σ → Prop) (zero : motive 0 a)
    (succ : ∀ n c c', motive n c → f c = some c' → motive (n + 1) c') : motive h.steps b := by
  suffices ∀ n c, (flip bind f)^[n] (some a) = some c → motive n c from this _ _ h.evals_in_steps
  intro n
  induction n with
  | zero => rintro c ⟨⟩; exact zero
  | succ n ih =>
    intro c' hc'
    rw [Function.iterate_succ_apply'] at hc'
    obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.1 hc'
    exact succ n c c' (ih c hc) hc'


end StateTransition
