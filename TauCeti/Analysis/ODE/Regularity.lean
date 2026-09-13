/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Regularity of solutions to first-order ODEs

This file contains the basic regularity theorem that a solution of a first-order equation gains one
derivative over a right-hand side that is already differentiable on its range.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

/-- A solution of a first-order equation with a `C^n` right-hand side is `C^(n + 1)`. -/
theorem contDiffOn_succ_of_hasDerivAt_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} {f : ℝ → F} {v : F → F} {s : Set ℝ} {u : Set F}
    (hs : IsOpen s) (hv : ContDiffOn ℝ n v u) (hfu : MapsTo f s u)
    (hf : ∀ t ∈ s, HasDerivAt f (v (f t)) t) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  induction n generalizing f with
  | zero =>
      have h : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) f s := by
        rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
        refine ⟨fun t ht => (hf t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
        apply (hv.comp (contDiffOn_zero.mpr ?_) hfu).congr
        · exact fun t ht => (hf t ht).deriv
        · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
      simpa using h
  | succ n ih =>
      have hfn : ContDiffOn ℝ (n + 1 : ℕ) f s :=
        ih (hv.of_le (by exact_mod_cast Nat.le_succ n)) hfu hf
      have h : ContDiffOn ℝ (((n + 1 : ℕ) : ℕ∞ω) + 1) f s := by
        rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
        refine ⟨fun t ht => (hf t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
        exact (hv.comp hfn hfu).congr fun t ht => (hf t ht).deriv
      simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using h

end TauCeti

end
