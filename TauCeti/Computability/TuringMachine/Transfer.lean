/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Transferring a stack in a controlled number of steps

A pop-and-push loop translates and reverses a stack of length `n` in `2 * n + 1` steps.
-/

public section

open Function (update)

namespace Turing.TM2

open Stmt

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

/-- A transfer loop between distinct stacks `k₁` and `k₂`: the label `L` pops `k₁` into the state,
from which `rd` reads the popped letter translated by `get`; if there was none, it jumps to `L'`,
otherwise to `P x`, which pushes `x` onto `k₂` and jumps back to `L`. Started at `L`, the machine
reaches `L'` in `2 * (S k₁).length + 1` steps, with `k₁` empty and `S k₁`, translated by `get`,
pushed onto `k₂` in reverse order. -/
theorem iterate_transfer (M : Λ → Stmt Γ Λ σ) {k₁ k₂ : K} (hk : k₁ ≠ k₂) {get : Γ k₁ → Γ k₂}
    {rd : σ → Option (Γ k₂)} {w : σ → Option (Γ k₁) → σ} {L L' : Λ} {P : Γ k₂ → Λ}
    (hL : M L = pop k₁ w (goto fun s ↦ (rd s).elim L' P))
    (hP : ∀ x, M (P x) = push k₂ (fun _ ↦ x) (goto fun _ ↦ L))
    (hrd : ∀ s o, rd (w s o) = o.map get) (hw : ∀ s o o', w (w s o) o' = w s o')
    (S : ∀ k, List (Γ k)) (s : σ) :
    (flip bind (step M))^[2 * (S k₁).length + 1] (some ⟨some L, s, S⟩) =
      some ⟨some L', w s none, update (update S k₁ []) k₂ (((S k₁).map get).reverse ++ S k₂)⟩ := by
  generalize hl : S k₁ = l
  induction l generalizing S s with
  | nil =>
    have hS : update S k₁ [] = S := Function.update_eq_self_iff.2 hl.symm
    simp [flip, hL, hl, hrd, hS]
  | cons x l ih =>
    have h₂ : (flip bind (step M))^[2] (some ⟨some L, s, S⟩) =
        some ⟨some L, w s (some x), update (update S k₁ l) k₂ (get x :: S k₂)⟩ := by
      simp [flip, hL, hP, hl, hrd, Function.update_of_ne hk.symm]
    rw [show 2 * (x :: l).length + 1 = 2 * l.length + 1 + 2 by rw [List.length_cons]; omega,
      Function.iterate_add_apply, h₂, ih _ _ (by simp [Function.update_of_ne hk])]
    simp [hw, Function.update_comm hk.symm]


end Turing.TM2
