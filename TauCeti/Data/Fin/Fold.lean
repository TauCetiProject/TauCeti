/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# Folding composites over `Fin`

The fold `Fin.foldl l (fun g k ↦ φ k ∘ g) id` is the composite `φ (l - 1) ∘ ⋯ ∘ φ 0` of a finite
sequence of maps. `Fin.foldl_comp_apply_of_succ_eq` evaluates it along a chain of states
`w 0, …, w l` with `w (k + 1) = φ k (w k)`: the composite sends the first state to the last one.
-/

public section

namespace Fin

/-- A composite `φ (l - 1) ∘ ⋯ ∘ φ 0` sends the first state of a chain of states
`w (k + 1) = φ k (w k)` to the last one. -/
theorem foldl_comp_apply_of_succ_eq {α : Sort*} {l : ℕ} (φ : Fin l → α → α) (w : Fin (l + 1) → α)
    (hw : ∀ k, w k.succ = φ k (w k.castSucc)) :
    Fin.foldl l (fun g k ↦ φ k ∘ g) id (w 0) = w (Fin.last l) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [Fin.foldl_succ_last, Function.comp_apply, ← Fin.castSucc_zero,
      ih (fun k ↦ φ k.castSucc) (fun k ↦ w k.castSucc)
        (fun k ↦ by simpa only [Fin.succ_castSucc] using hw k.castSucc),
      ← hw, Fin.succ_last]

end Fin
