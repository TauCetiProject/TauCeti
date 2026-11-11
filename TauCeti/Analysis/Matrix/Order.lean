/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Compact order intervals for the Loewner order

For the Loewner order on square matrices over `ℝ` or `ℂ` (`open scoped MatrixOrder`), every closed
interval `Set.Icc a b` is compact. If the interval is nonempty, then `b - a` is positive
semidefinite and every `x` in it has `0 ≤ x - a ≤ b - a`, so the spectrum of `x - a` lies in
`[0, r]` for any upper bound `r` of the spectrum of `b - a`; the `ℓ²` operator norm of `x - a`,
which is its spectral radius, is then at most `r`. The interval is closed because the Loewner
order is.

This is the compactness behind fixed-point arguments on sets of matrices such as
`{S | α • 1 ≤ S ≤ β • 1}`, which are also convex.

## Main statements

* `Matrix.instCompactIccSpace`: the Loewner order on `Matrix n n 𝕜` has compact closed intervals.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Finite n]

open scoped ContinuousFunctionalCalculus in
/-- Closed intervals of the Loewner order on square matrices are compact. -/
instance instCompactIccSpace : CompactIccSpace (Matrix n n 𝕜) where
  isCompact_Icc {a b} := by
    classical
    have := Fintype.ofFinite n
    rcases (Set.Icc a b).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
    · simp [h]
    have hba : 0 ≤ b - a := sub_nonneg.2 (hx₀.1.trans hx₀.2)
    obtain ⟨r, hr⟩ := (isCompact_iff_compactSpace.mpr inferInstance :
      IsCompact (spectrum ℝ (b - a))).bddAbove
    have hbar : b - a ≤ algebraMap ℝ _ r :=
      le_algebraMap_of_spectrum_le (fun x hx ↦ hr hx) hba.isSelfAdjoint
    -- Measure the interval with the `ℓ²` operator norm, whose topology is the entrywise one.
    open scoped Matrix.Norms.L2Operator in
    let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
    refine Metric.isCompact_of_isClosed_isBounded isClosed_Icc
      ((Metric.isBounded_closedBall (x := a) (r := max r 0)).subset fun x hx ↦ ?_)
    have hy : 0 ≤ x - a := sub_nonneg.2 hx.1
    have hyr : x - a ≤ algebraMap ℝ _ r := (sub_le_sub_right hx.2 a).trans hbar
    rw [Metric.mem_closedBall, dist_eq_norm, ← cfc_id' ℝ (x - a) hy.isSelfAdjoint]
    refine norm_cfc_le (le_max_right _ _) fun t ht ↦ ?_
    have h₁ := (StarOrderedRing.nonneg_iff_spectrum_nonneg _ hy.isSelfAdjoint).1 hy t ht
    have h₂ := (le_algebraMap_iff_spectrum_le (ha := hy.isSelfAdjoint)).1 hyr t ht
    rw [Real.norm_eq_abs, abs_of_nonneg h₁]
    exact h₂.trans (le_max_left _ _)

end Matrix
