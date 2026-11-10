/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.LinearAlgebra.Matrix.Trace.Square
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The trace bound for a symmetric Riccati equation

Trace Cauchy–Schwarz and a lower curvature-trace bound give the scalar Riccati inequality,
including for an empty matrix index. The determinant density-root application additionally
needs positive dimension.

Formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

namespace Matrix

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The scalar trace bound obtained from a symmetric matrix Riccati equation and a lower
curvature-trace bound. The matrix index may be empty. -/
theorem trace_add_sq_trace_div_card_le_card_mul {ι : Type*} [Fintype ι]
    {S S' K : Matrix ι ι 𝕜} (hS : S.IsSymm)
    {κ : 𝕜} (hode : S' = -(S * S) - K)
    (hric : -(Fintype.card ι : 𝕜) * κ ≤ K.trace) :
    S'.trace + S.trace ^ 2 / (Fintype.card ι : 𝕜) ≤ (Fintype.card ι : 𝕜) * κ := by
  have hnonneg : 0 ≤ (S * S).trace :=
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg (S i i)).trans
      (sum_sq_diag_le_trace_mul_self hS)
  have htrace : S.trace ^ 2 / (Fintype.card ι : 𝕜) ≤ (S * S).trace := by
    apply div_le_of_le_mul₀ (Nat.cast_nonneg _) hnonneg
    simpa only [mul_comm] using sq_trace_le_card_mul_trace_mul_self hS
  rw [hode, trace_sub, trace_neg]
  linarith

end Matrix
