/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Batteries.Data.Fin.Fold
public import Mathlib.Data.Fin.Basic

/-!
# Folding composites over `Fin`

The fold `Fin.foldl l (fun g k ↦ φ k ∘ g) id` is the composite `φ (l - 1) ∘ ⋯ ∘ φ 0` of a finite
sequence of maps. `Fin.foldl_comp_apply_of_succ_eq` evaluates it along a chain of states
`w 0, …, w l` with `w (k + 1) = φ k (w k)`: the composite sends the first state to the last one.

For varying intermediate types, `Fin.dfoldl_add` splits a dependent fold into two consecutive
blocks at any intermediate index.
-/

public section

namespace Fin

/-- Split a dependent left fold at an arbitrary intermediate index. The first fold uses the
first `m` transitions, and the second uses the remaining `n` transitions. -/
theorem dfoldl_add {m n : ℕ} {α : Fin (m + n + 1) → Type*}
    (f : ∀ i : Fin (m + n), α i.castSucc → α i.succ) (x : α 0) :
    dfoldl (m + n) α f x =
      dfoldl n (fun i => α (i.natAdd m)) (fun i => f (i.natAdd m))
        (dfoldl m (fun i => α (i.castLE (by omega))) (fun i => f (i.castAdd n)) x) := by
  induction n with
  | zero => simp only [Nat.add_zero, dfoldl_zero]; rfl
  | succ n ih =>
    exact (dfoldl_succ_last f x).trans
      ((congrArg (f (last (m + n)))
        (ih (α := fun i => α i.castSucc) (fun i => f i.castSucc) x)).trans
        (dfoldl_succ_last (α := fun i => α (i.natAdd m))
          (fun i => f (i.natAdd m))
          (dfoldl m (fun i => α (i.castLE (by omega)))
            (fun i => f (i.castAdd (n + 1))) x)).symm)

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
