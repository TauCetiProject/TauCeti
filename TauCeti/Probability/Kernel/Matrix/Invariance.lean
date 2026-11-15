/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.Matrix.Basic
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Stationarity and detailed balance in finite matrix coordinates

For a finite measure `μ` and a finite kernel `κ`, stationarity is exactly the row-vector
identity `π ᵥ* κ.toMatrix = π`, where `π a = (μ {a}).toNNReal`. Reversibility is exactly
symmetry of `Matrix.diagonal π * κ.toMatrix`. These characterizations do not require that
`μ` be a probability measure or that `κ` be Markov.

For a row-stochastic matrix, the same criteria apply to its associated Markov kernel.
The PMF specializations let a caller supply a probability law without introducing a
separate probability-vector structure. Detailed balance implies stationarity through
Mathlib's `Kernel.IsReversible.invariant`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.7 and 1.9.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

namespace ProbabilityTheory.Kernel

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A finite measure is invariant exactly when its mass row vector is fixed by the
transition matrix. No normalization of the measure or kernel is required. -/
theorem invariant_iff_vecMul (κ : Kernel α α) [IsFiniteKernel κ]
    (μ : Measure α) [IsFiniteMeasure μ] :
    κ.Invariant μ ↔
      (fun a => (μ {a}).toNNReal) ᵥ* κ.toMatrix = fun a => (μ {a}).toNNReal := by
  rw [Invariant, Measure.ext_iff_singleton, funext_iff]
  refine forall_congr' fun a => ?_
  rw [← comp_apply_singleton_eq_vecMul]
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).symm

/-- Detailed balance for a finite kernel and finite measure is symmetry of the
transition matrix after multiplying each row by the corresponding mass. -/
theorem isReversible_iff_isSymm_diagonal_mul [DecidableEq α]
    (κ : Kernel α α) [IsFiniteKernel κ] (μ : Measure α) [IsFiniteMeasure μ] :
    κ.IsReversible μ ↔
      (Matrix.diagonal (fun a => (μ {a}).toNNReal) * κ.toMatrix).IsSymm := by
  have hmass (a b : α) :
      (μ ⊗ₘ κ) ({a} ×ˢ {b}) =
        (((Matrix.diagonal (fun a => (μ {a}).toNNReal) * κ.toMatrix) a b : ℝ≥0) : ℝ≥0∞) := by
    rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
    simp [ENNReal.coe_toNNReal]
  constructor
  · intro h
    apply Matrix.IsSymm.ext_iff.mpr
    intro a b
    apply ENNReal.coe_injective
    rw [← hmass, ← hmass,
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
    exact h (measurableSet_singleton b) (measurableSet_singleton a)
  · intro h
    have hswap : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ := by
      apply Measure.ext_iff_singleton.mpr
      rintro ⟨a, b⟩
      rw [Measure.map_apply measurable_swap (measurableSet_singleton _),
        ← Set.singleton_prod_singleton, Set.preimage_swap_prod, hmass, hmass, h.apply]
    intro A B hA hB
    have heq := congrArg (fun ν : Measure (α × α) => ν (B ×ˢ A)) hswap
    simpa only [Measure.map_apply measurable_swap (hB.prod hA), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hB hA] using heq

end ProbabilityTheory.Kernel

namespace Matrix.rowStochastic

variable {α : Type*} [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A stochastic matrix preserves a finite measure exactly when it fixes the measure's
mass row vector. -/
theorem invariant_toKernel_iff_vecMul (M : rowStochastic ℝ≥0 α)
    (μ : Measure α) [IsFiniteMeasure μ] :
    (toKernel M).Invariant μ ↔
      (fun a => (μ {a}).toNNReal) ᵥ* M.val = fun a => (μ {a}).toNNReal := by
  rw [Kernel.invariant_iff_vecMul, toMatrix_toKernel]

/-- A stochastic matrix satisfies detailed balance for a finite measure exactly when
its row-weighted matrix is symmetric. -/
theorem isReversible_toKernel_iff_isSymm_diagonal_mul (M : rowStochastic ℝ≥0 α)
    (μ : Measure α) [IsFiniteMeasure μ] :
    (toKernel M).IsReversible μ ↔
      (diagonal (fun a => (μ {a}).toNNReal) * M.val).IsSymm := by
  rw [Kernel.isReversible_iff_isSymm_diagonal_mul, toMatrix_toKernel]

/-- A PMF is stationary for a stochastic matrix exactly when its nonnegative mass
row vector is a left eigenvector with eigenvalue one. -/
theorem invariant_toKernel_toMeasure_iff_vecMul (M : rowStochastic ℝ≥0 α) (π : PMF α) :
    (toKernel M).Invariant π.toMeasure ↔
      (fun a => (π a).toNNReal) ᵥ* M.val = fun a => (π a).toNNReal := by
  simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using
    invariant_toKernel_iff_vecMul M π.toMeasure

/-- Detailed balance for a probability mass function is symmetry of the stochastic
matrix weighted by that PMF. -/
theorem isReversible_toKernel_toMeasure_iff_isSymm_diagonal_mul
    (M : rowStochastic ℝ≥0 α) (π : PMF α) :
    (toKernel M).IsReversible π.toMeasure ↔
      (diagonal (fun a => (π a).toNNReal) * M.val).IsSymm := by
  simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using
    isReversible_toKernel_iff_isSymm_diagonal_mul M π.toMeasure

end Matrix.rowStochastic
