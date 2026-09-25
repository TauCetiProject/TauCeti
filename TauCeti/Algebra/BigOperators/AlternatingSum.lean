/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Abel

/-!
# Alternating sums over integer intervals

This file gives a telescoping formula for alternating sums of consecutive pairs in an additive
commutative group.
-/

public section

namespace TauCeti

/-- An alternating sum of consecutive pairs telescopes to its two end terms. -/
theorem sum_Icc_negOnePow_smul_add {G : Type*} [AddCommGroup G] (f : ℤ → G) (a b : ℤ)
    (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, (n.negOnePow : ℤ) • (f n + f (n + 1)) =
      (a.negOnePow : ℤ) • f a + (b.negOnePow : ℤ) • f (b + 1) := by
  induction b, hab using Int.leInduction with
  | base => simp [smul_add]
  | succ b hb ih =>
    have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp), ih, Int.negOnePow_succ]
    simp only [Units.val_neg, neg_smul, smul_add]
    abel

end TauCeti
