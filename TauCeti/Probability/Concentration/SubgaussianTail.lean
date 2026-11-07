/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Two-sided sub-Gaussian tail around a shifted center

If `g - c` is sub-Gaussian with variance proxy `σ` and the center `c` is within `ε / 2` of a
target `t`, then `g` deviates from `t` by at least `ε` with probability at most
`2 exp (-(ε / 2)² / (2σ))`. This is how a concentration bound centered at the mean transfers to a
nearby target value.

## Main result

* `TauCeti.Probability.measureReal_abs_sub_ge_le_of_hasSubgaussianMGF`
-/

public section

open MeasureTheory

open scoped NNReal

namespace TauCeti.Probability

/-- Two-sided sub-Gaussian tail around a shifted center: if `g - c` is sub-Gaussian with variance
proxy `σ` and the center `c` is within `ε / 2` of the target `t`, then `g` deviates from `t` by at
least `ε` with probability at most `2 exp (-(ε / 2)² / (2σ))`. -/
theorem measureReal_abs_sub_ge_le_of_hasSubgaussianMGF {α : Type*} [MeasurableSpace α]
    {P : Measure α} [IsProbabilityMeasure P] {g : α → ℝ} {c t ε : ℝ} {σ : ℝ≥0}
    (h : ProbabilityTheory.HasSubgaussianMGF (fun x => g x - c) σ P) (hct : |c - t| ≤ ε / 2)
    (hε : 0 < ε) :
    P.real {x | ε ≤ |g x - t|} ≤ 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by
  have htail₁ := h.measure_ge_le (ε := ε / 2) (half_pos hε).le
  have htail₂ := h.neg.measure_ge_le (ε := ε / 2) (half_pos hε).le
  have hincl : {x | ε ≤ |g x - t|} ⊆ {x | ε / 2 ≤ g x - c} ∪ {x | ε / 2 ≤ -(g x - c)} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx
    have hcenter : ε / 2 ≤ |g x - c| := by
      have htri : |g x - t| ≤ |g x - c| + |c - t| := abs_sub_le _ _ _
      linarith [abs_nonneg (g x - c)]
    rcases le_abs.mp hcenter with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc
    P.real {x | ε ≤ |g x - t|} ≤ P.real ({x | ε / 2 ≤ g x - c} ∪ {x | ε / 2 ≤ -(g x - c)}) :=
      measureReal_mono hincl
    _ ≤ P.real {x | ε / 2 ≤ g x - c} + P.real {x | ε / 2 ≤ -(g x - c)} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) + Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) :=
      add_le_add htail₁ htail₂
    _ = 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by ring

end TauCeti.Probability
