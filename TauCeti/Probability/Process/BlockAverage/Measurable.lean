/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.BlockAverage.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of block averages

A finite block average is measurable whenever its sampled coordinates are measurable.
This applies to arbitrary real-valued processes and finite selections, including repeated
coordinates and the empty block. No measure or symmetry hypothesis is needed.

Keeping this API separate from integrability and conditional expectation lets arguments about
future σ-algebras use it without importing those analytic dependencies.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : ℕ → Ω → ℝ}

/-- A block average is measurable if its sampled coordinates are measurable. -/
@[fun_prop]
theorem measurable_blockAverage {n : ℕ} (k : Fin n → ℕ)
    (hX : ∀ i, Measurable (X (k i))) : Measurable (blockAverage X k) := by
  rw [blockAverage_eq_sum]
  simpa only [← Finset.sum_apply] using
    (Finset.measurable_sum Finset.univ fun i _ => hX i).const_smul (n : ℝ)⁻¹

/-- A prefix average is measurable if its first `n` coordinates are measurable. -/
@[fun_prop]
theorem measurable_prefixAverage (n : ℕ) (hX : ∀ i : Fin n, Measurable (X i)) :
    Measurable (prefixAverage X n) := by
  rw [prefixAverage_def]
  exact measurable_blockAverage _ hX

/-- A following-block average is measurable if its sampled coordinates are measurable. -/
@[fun_prop]
theorem measurable_followingAverage (n : ℕ) (hX : ∀ i : Fin n, Measurable (X (n + i))) :
    Measurable (followingAverage X n) := by
  rw [followingAverage_def]
  exact measurable_blockAverage _ hX

end TauCeti.Probability
