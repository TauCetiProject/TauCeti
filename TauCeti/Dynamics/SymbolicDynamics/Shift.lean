/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic

/-!
# Iterates of the shift

A complement to Mathlib's `SymbolicDynamics.FullShift.mulShift`: iterating the shift by `g`
`k` times is the shift by `g ^ k` (in additive notation, by `k • g`). On `ℤ → A`, a set invariant
under the two-sided shift `shift 1` is invariant under every shift `shift k`, `k ∈ ℤ`.

## Main results

* `SymbolicDynamics.FullShift.mulShift_iterate`, `SymbolicDynamics.FullShift.shift_iterate`:
  `(mulShift g)^[k] = mulShift (g ^ k)` and `(shift g)^[k] = shift (k • g)`.
* `SymbolicDynamics.FullShift.preimage_shift_eq_of_preimage_shift_one_eq`: a set invariant under
  `shift 1` is invariant under every `shift k`.
-/

public section

namespace SymbolicDynamics.FullShift

variable {A G : Type*} [Monoid G]

/-- Iterating the shift by `g` `k` times is the shift by `g ^ k`. -/
@[to_additive (attr := simp) /-- Iterating the shift by `g` `k` times is the shift by `k • g`. -/]
theorem mulShift_iterate (g : G) (k : ℕ) : (mulShift (A := A) g)^[k] = mulShift (g ^ k) := by
  induction k with
  | zero => funext x; simp
  | succ k ih => rw [Function.iterate_succ', ih, pow_succ]; funext x; simp [mulShift_mul]

/-- A set invariant under the two-sided shift is invariant under every shift `shift k`,
`k ∈ ℤ`. -/
theorem preimage_shift_eq_of_preimage_shift_one_eq {s : Set (ℤ → A)}
    (hs : shift (1 : ℤ) ⁻¹' s = s) (k : ℤ) : shift k ⁻¹' s = s := by
  have hstep (k : ℤ) : shift (k + 1) = shift (1 : ℤ) ∘ shift (A := A) k :=
    funext fun x ↦ shift_add k 1 x
  induction k using Int.induction_on with
  | zero =>
    rw [show shift (0 : ℤ) = (id : (ℤ → A) → ℤ → A) from funext shift_zero, Set.preimage_id]
  | succ k ih => rw [hstep, Set.preimage_comp, hs, ih]
  | pred k ih =>
    have h := hstep (-k - 1)
    rw [sub_add_cancel] at h
    rwa [h, Set.preimage_comp, hs] at ih

end SymbolicDynamics.FullShift
