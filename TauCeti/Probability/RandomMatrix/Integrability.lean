/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Pow
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Integrability of traces of random matrix powers

The trace of the `k`-th power of a square matrix is a finite sum, over the closed walks of length
`k`, of the products of the `k` entries read along the walk (`Matrix.trace_pow_eq_sum_prod`). For
`k ≠ 0`, Hölder's inequality therefore puts the trace of `A ^ k` in `Lᵖ` for any measure when
every entry of the random matrix `A` lies in `L^(p * k)`. For `k = 0` the trace is the constant
`card ι`, and the theorem assumes a finite measure in that case. Neither independence nor
centering is needed.

## Main results

* `TauCeti.memLp_trace_pow`: with entries in `L^(p * k)`, `(A ^ k).trace` lies in `Lᵖ`; the
  measure is assumed finite when `k = 0`.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal

namespace TauCeti

variable {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] {P : Measure Ω} [Fintype ι] [DecidableEq ι]
  [NormedCommRing 𝕜]

/-- The trace of the `k`th power of a random square matrix lies in `Lᵖ` for every `p : ℝ≥0∞`
whenever all of its entries lie in `L^(p * k)`. The measure is assumed finite when `k = 0`, where
the trace is constant. Neither independence nor centering is required. -/
theorem memLp_trace_pow {A : Ω → Matrix ι ι 𝕜} {p : ℝ≥0∞} {k : ℕ}
    (hP : k = 0 → IsFiniteMeasure P) (hA : ∀ i j, MemLp (fun ω ↦ A ω i j) (p * k) P) :
    MemLp (fun ω ↦ (A ω ^ k).trace) p P := by
  rcases eq_or_ne k 0 with rfl | hk
  · have := hP rfl
    simp [memLp_const]
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    refine memLp_finsetSum Finset.univ fun w _ ↦
      memLp_fun_prod_of_memLp_mul_card ⟨⟨0, Nat.pos_of_ne_zero hk⟩, Finset.mem_univ _⟩
        fun t _ ↦ ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hA _ _

end TauCeti
