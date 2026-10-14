/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.BlockAverage.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Measure theory of block averages

Finite block averages preserve `MemLp` at every exponent and commute almost everywhere with
conditional expectation when the sampled coordinates are integrable. These facts apply to
arbitrary real-valued processes and arbitrary finite selections, including repeated coordinates
and the empty block. They require no invariance of the process law and no finiteness of the
ambient measure.

The prefix and following-block lemmas specialize these integrability and conditional-expectation
identities.
Together these results let averaging arguments use the process API independently of any
probability-symmetry hypotheses.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A block average of `Lᵖ` coordinates is itself `Lᵖ`. -/
theorem memLp_blockAverage {p : ℝ≥0∞} {n : ℕ} (k : Fin n → ℕ)
    (hX_Lp : ∀ i, MemLp (X (k i)) p μ) :
    MemLp (blockAverage X k) p μ := by
  rw [blockAverage_eq_sum]
  exact (memLp_finsetSum' _ fun i _ => hX_Lp i).const_smul _

/-- **Conditional expectation commutes with block averages.** The conditional expectation of a
block average of integrable coordinates is the block average of their conditional expectations. -/
theorem condExp_blockAverage {m : MeasurableSpace Ω} {n : ℕ} (k : Fin n → ℕ)
    (hX : ∀ i, Integrable (X (k i)) μ) :
    μ[blockAverage X k | m] =ᵐ[μ] blockAverage (fun i => μ[X i | m]) k := by
  rw [blockAverage_eq_sum]
  refine (condExp_smul _ _ _).trans ?_
  filter_upwards [condExp_finsetSum (μ := μ) (m := m) (s := Finset.univ)
    (f := fun i : Fin n => X (k i)) fun i _ => hX i] with ω hω
  rw [Pi.smul_apply, hω, Finset.sum_apply, blockAverage_apply, smul_eq_mul]

/-- A prefix average of `Lᵖ` coordinates is itself `Lᵖ`. -/
theorem memLp_prefixAverage {p : ℝ≥0∞} (n : ℕ) (hX_Lp : ∀ i : Fin n, MemLp (X i) p μ) :
    MemLp (prefixAverage X n) p μ := by
  rw [prefixAverage_def]
  exact memLp_blockAverage (fun i : Fin n => (i : ℕ)) hX_Lp

/-- Conditional expectation commutes almost everywhere with a prefix average of integrable
coordinates. -/
theorem condExp_prefixAverage {m : MeasurableSpace Ω} (n : ℕ)
    (hX : ∀ i : Fin n, Integrable (X i) μ) :
    μ[prefixAverage X n | m] =ᵐ[μ] prefixAverage (fun i => μ[X i | m]) n := by
  rw [prefixAverage_def, prefixAverage_def]
  exact condExp_blockAverage (mΩ := mΩ) (fun i : Fin n => (i : ℕ)) hX

/-- A following tail average of `Lᵖ` coordinates is itself `Lᵖ`. -/
theorem memLp_followingAverage {p : ℝ≥0∞} (n : ℕ) (hX_Lp : ∀ i : Fin n, MemLp (X (n + i)) p μ) :
    MemLp (followingAverage X n) p μ := by
  rw [followingAverage_def]
  exact memLp_blockAverage (fun i : Fin n => n + (i : ℕ)) hX_Lp

/-- Conditional expectation commutes almost everywhere with a following-block average of
integrable coordinates. -/
theorem condExp_followingAverage {m : MeasurableSpace Ω} (n : ℕ)
    (hX : ∀ i : Fin n, Integrable (X (n + i)) μ) :
    μ[followingAverage X n | m] =ᵐ[μ] followingAverage (fun i => μ[X i | m]) n := by
  rw [followingAverage_def, followingAverage_def]
  exact condExp_blockAverage (mΩ := mΩ) (fun i : Fin n => n + (i : ℕ)) hX

end Probability

end TauCeti
