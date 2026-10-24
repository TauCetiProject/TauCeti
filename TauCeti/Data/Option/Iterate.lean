/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Iteration of a partial self-map

Iterating a map `α → Option α` returns `none` as soon as one application is undefined.
The bind composition law and the two successor equations support both recursive proofs
and concatenation of partial trajectories. This supplies the common iteration used by
crystal strings and path root operators.
-/

public section

namespace Option

variable {α : Type*}

/-- Apply a partial self-map `n` times, stopping at the first undefined value. -/
def iterate (f : α → Option α) : ℕ → α → Option α
  | 0, x => some x
  | n + 1, x => (f x).bind (iterate f n)

/-- Zero iterations leave the starting value defined and unchanged. -/
@[simp]
theorem iterate_zero (f : α → Option α) (x : α) : iterate f 0 x = some x := (rfl)

/-- First apply the partial map once, then perform the remaining iterations. -/
theorem iterate_succ (f : α → Option α) (n : ℕ) (x : α) :
    iterate f (n + 1) x = (f x).bind (iterate f n) := (rfl)

/-- A single iteration is the original partial map. -/
@[simp]
theorem iterate_one (f : α → Option α) (x : α) : iterate f 1 x = f x := by
  simp [iterate_succ]

/-- Two successive runs of a partial map concatenate by option bind. -/
theorem iterate_add (f : α → Option α) (m n : ℕ) (x : α) :
    iterate f (m + n) x = (iterate f m x).bind (iterate f n) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, iterate_succ, ih, Option.bind_assoc]

/-- A successor run can instead apply the partial map after the preceding iterations. -/
theorem iterate_succ' (f : α → Option α) (n : ℕ) (x : α) :
    iterate f (n + 1) x = (iterate f n x).bind f := by
  have hfun : iterate f 1 = f := funext (iterate_one f)
  simpa only [hfun] using iterate_add f n 1 x

end Option
