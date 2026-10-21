/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Differentiability away from finitely many exceptions

A function that is `C^1` on a closed interval outside a finite exceptional set is
differentiable at every interior point outside that set. In particular, it supplies
a countable differentiability exception set for the interval.
-/

public section

open Set

/-- `C^1` regularity outside a finite set supplies a countable differentiability exception set
in the interior of the interval. -/
theorem ContDiffOn.exists_countable_differentiableAt_of_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} {s : Set ℝ}
    (h : ContDiffOn ℝ 1 f (Icc a b \ s)) (hs : s.Finite) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ f t := by
  refine ⟨s, hs.countable, ?_⟩
  intro t ht
  exact (h.contDiffAt (Filter.inter_mem (Icc_mem_nhds ht.1.1 ht.1.2)
    (hs.isClosed.isOpen_compl.mem_nhds ht.2))).differentiableAt (by norm_num)
