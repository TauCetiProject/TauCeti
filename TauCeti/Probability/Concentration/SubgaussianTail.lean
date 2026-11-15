/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Two-sided sub-Gaussian tail around a shifted center

If `g - c` is sub-Gaussian with variance proxy `σ` and the center `c` is within `ε / 2` of a
target `t`, then `g` deviates from `t` by at least `ε` with probability at most
`2 exp (-(ε / 2)² / (2σ))`. This is how a concentration bound centered at the mean transfers to a
nearby target value.

## Main result

* `TauCeti.Probability.measureReal_abs_sub_ge_le_of_hasSubgaussianMGF`

## References

* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`.
  The two-tail calculation is adapted from that file; here it is stated for an arbitrary measure
  and a general sub-Gaussian variable rather than for the graphon sampling law.
-/

public section

open MeasureTheory

open scoped NNReal

namespace TauCeti.Probability

/-- Two-sided sub-Gaussian tail around a shifted center: if `g - c` is sub-Gaussian with variance
proxy `σ` and the center `c` is within `ε / 2` of the target `t`, then `g` deviates from `t` by at
least `ε` with probability at most `2 exp (-(ε / 2)² / (2σ))`. -/
theorem measureReal_abs_sub_ge_le_of_hasSubgaussianMGF {α : Type*} [MeasurableSpace α]
    {P : Measure α} {g : α → ℝ} {c t ε : ℝ} {σ : ℝ≥0}
    (h : ProbabilityTheory.HasSubgaussianMGF (fun x => g x - c) σ P) (hct : |c - t| ≤ ε / 2) :
    P.real {x | ε ≤ |g x - t|} ≤ 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by
  have hε : 0 ≤ ε := by linarith [abs_nonneg (c - t)]
  have : IsFiniteMeasure P := by
    exact (integrable_const_iff_isFiniteMeasure (c := (1 : ℝ)) one_ne_zero).1
      (by simpa using h.integrable_exp_mul 0)
  have htail₁ := h.measure_ge_le (ε := ε / 2) (by positivity)
  have htail₂ := h.neg.measure_ge_le (ε := ε / 2) (by positivity)
  have hincl : {x | ε ≤ |g x - t|} ⊆ {x | ε / 2 ≤ |g x - c|} := fun x hx => by
    rw [Set.mem_ofPred_eq] at hx ⊢
    have htri : |g x - t| ≤ |g x - c| + |c - t| := abs_sub_le _ _ _
    linarith
  calc
    P.real {x | ε ≤ |g x - t|} ≤ P.real {x | ε / 2 ≤ |g x - c|} := measureReal_mono hincl
    _ ≤ P.real {x | ε / 2 ≤ g x - c} + P.real {x | ε / 2 ≤ -(g x - c)} :=
      TauCeti.measureReal_le_abs_le_add (f := fun x => g x - c)
    _ ≤ Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) + Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) :=
      add_le_add htail₁ htail₂
    _ = 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by ring

end TauCeti.Probability
