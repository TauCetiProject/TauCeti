/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.StateTransition.Induction

/-!
# Transporting an execution along a simulation

A step-preserving map transports an execution without changing its step count.
-/

public section

namespace StateTransition

/-- A map sending every step of `f` to a step of `g` sends a run of `f` to a run of `g` with the
same number of steps. -/
@[expose]
def EvalsTo.map {σ τ : Type*} {f : σ → Option σ} {g : τ → Option τ} (tr : σ → τ)
    (htr : ∀ c c', f c = some c' → g (tr c) = some (tr c')) {a b : σ} (h : EvalsTo f a (some b)) :
    EvalsTo g (tr a) (some (tr b)) where
  steps := h.steps
  evals_in_steps := h.induction_on (fun n c ↦ (flip bind g)^[n] (some (tr a)) = some (tr c)) rfl
    fun n c c' ih hc ↦ by rw [Function.iterate_succ_apply', ih]; exact htr c c' hc


end StateTransition
