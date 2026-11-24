/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Algebraic operations on appended tuples

Inverting (negating) a tuple `Fin.snoc p x` entrywise inverts (negates) both the initial tuple
`p` and the appended last entry `x`.

## Main results

* `Fin.inv_snoc`, `Fin.neg_snoc`: inversion and negation commute with appending a last entry.
-/

public section

namespace Fin

variable {n : ℕ} {α : Fin (n + 1) → Type*}

/-- Inverting an appended tuple inverts the initial tuple and the last entry. -/
@[to_additive (attr := simp)
  /-- Negating an appended tuple negates the initial tuple and the last entry. -/]
theorem inv_snoc [∀ j, Inv (α j)] (p : ∀ i : Fin n, α i.castSucc) (x : α (last n)) :
    (snoc p x)⁻¹ = snoc p⁻¹ x⁻¹ := by
  funext i
  refine lastCases ?_ (fun i ↦ ?_) i <;> simp

end Fin
