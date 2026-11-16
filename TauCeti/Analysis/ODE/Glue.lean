/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gluing solutions of an ODE on adjacent intervals

Two solutions of `x' = v t (x t)` on adjacent closed intervals `[l, m]` and `[m, u]`, with
derivatives taken within those intervals, glue to a solution on `[l, u]` once they agree at the
common end `m`. The one-sided derivatives at `m` match because both equal `v m (x m)`.

## Main results

* `TauCeti.hasDerivWithinAt_Icc_ite`: the glued function `t ↦ if t ≤ m then f t else g t` solves
  the equation within `[l, u]`.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two solutions of `x' = v t (x t)` on adjacent closed intervals `[l, m]` and `[m, u]` which agree
at the common end `m` glue to a solution on `[l, u]`. -/
theorem hasDerivWithinAt_Icc_ite {v : ℝ → E → E} {f g : ℝ → E} {l m u : ℝ} (hlm : l ≤ m)
    (hmu : m ≤ u) (hf : ∀ t ∈ Icc l m, HasDerivWithinAt f (v t (f t)) (Icc l m) t)
    (hg : ∀ t ∈ Icc m u, HasDerivWithinAt g (v t (g t)) (Icc m u) t) (hfg : f m = g m) :
    ∀ t ∈ Icc l u, HasDerivWithinAt (fun t ↦ if t ≤ m then f t else g t)
      (v t (if t ≤ m then f t else g t)) (Icc l u) t := by
  intro t ht
  have hhf : EqOn (fun t ↦ if t ≤ m then f t else g t) f (Icc l m) := fun s hs ↦ ite_eq_left hs.2
  have hhg : EqOn (fun t ↦ if t ≤ m then f t else g t) g (Icc m u) := fun s hs ↦ by
    rcases hs.1.eq_or_lt with rfl | hs'
    · exact (ite_eq_left le_rfl).trans hfg
    · exact ite_eq_right (not_le.2 hs')
  rw [← Icc_union_Icc_eq_Icc hlm hmu]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases htm : t ≤ m
    · rw [show (if t ≤ m then f t else g t) = f t from hhf ⟨ht.1, htm⟩]
      exact (hf t ⟨ht.1, htm⟩).congr hhf (hhf ⟨ht.1, htm⟩)
    · refine hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure ?_)
      rw [isClosed_Icc.closure_eq]
      exact fun h ↦ htm h.2
  · by_cases htm : m ≤ t
    · rw [show (if t ≤ m then f t else g t) = g t from hhg ⟨htm, ht.2⟩]
      exact (hg t ⟨htm, ht.2⟩).congr hhg (hhg ⟨htm, ht.2⟩)
    · refine hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure ?_)
      rw [isClosed_Icc.closure_eq]
      exact fun h ↦ htm h.1

end TauCeti
