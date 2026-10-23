/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Uniformly small tails of a function of finite Lebesgue integral

A function `f : α → ℝ≥0∞` of finite Lebesgue integral exceeds a large constant `M` only by an
amount of small integral: `∫⁻ x, f x - M ∂μ → 0` as `M → ∞`. This is dominated convergence with
the bound `f`, since `f x - M` vanishes for `M ≥ f x` and `f` is almost everywhere finite.

## Main statements

* `TauCeti.tendsto_lintegral_tsub_atTop`: the integral of the excess of `f` over the constant `M`
  tends to `0` as `M → ∞`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Uniformly small tails.** If `f : α → ℝ≥0∞` is almost everywhere measurable with finite
Lebesgue integral, then the integral of its excess `f x - M` over a finite level `M` tends to `0`
as `M → ∞`. -/
theorem tendsto_lintegral_tsub_atTop {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun M : ℝ≥0 ↦ ∫⁻ x, f x - M ∂μ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence' (l := atTop)
    (F := fun (M : ℝ≥0) x ↦ f x - M) (f := fun _ ↦ 0) f
    (Eventually.of_forall fun M ↦ hf.sub aemeasurable_const)
    (Eventually.of_forall fun M ↦ ae_of_all _ fun x ↦ tsub_le_self) hfi ?_
  · simpa using h
  -- At a point where `f` is finite, the excess vanishes once `M ≥ f x`.
  filter_upwards [ae_lt_top' hf hfi] with x hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (f x).toNNReal] with M hM
  rw [eq_comm, tsub_eq_zero_iff_le]
  exact (ENNReal.coe_toNNReal hx.ne).symm.trans_le (ENNReal.coe_le_coe.2 hM)

end TauCeti
