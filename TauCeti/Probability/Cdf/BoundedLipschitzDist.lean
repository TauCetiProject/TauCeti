/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.BoundedLipschitzDist
public import TauCeti.Probability.Cdf.Polya

/-!
# The Kolmogorov distance controls the bounded Lipschitz distance

For probability measures on `ℝ`, closeness in the Kolmogorov distance implies closeness in the
bounded Lipschitz distance, uniformly: for every probability measure `ν` and every `ε > 0` there is
`δ > 0` such that every probability measure `Q` with `kolmogorovDist Q ν < δ` has
`boundedLipschitzDist Q ν < ε`. No continuity of `cdf ν` is needed.

The argument is by contradiction along a sequence. If the modulus failed, there would be laws `Qₙ`
with `kolmogorovDist Qₙ ν → 0` while `boundedLipschitzDist Qₙ ν` stays at least `ε`. Uniform
convergence of distribution functions gives weak convergence `Qₙ → ν`, whatever `ν` is, and on the
Polish space `ℝ` weak convergence is convergence in the bounded Lipschitz distance.

The point masses at `0` and `1 / n` show that there is no modulus in the other direction without
a continuity hypothesis on `cdf ν`: their bounded Lipschitz distance tends to `0` while their
Kolmogorov distance is `1`.

## Main results

* `ProbabilityTheory.exists_pos_forall_kolmogorovDist_lt_boundedLipschitzDist_lt`: the uniform
  modulus;
* `MeasureTheory.ProbabilityMeasure.tendsto_boundedLipschitzDist_of_tendsto_kolmogorovDist`:
  convergence in the Kolmogorov distance implies convergence in the bounded Lipschitz distance,
  along any filter.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemma 2.11.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

/-- **The Kolmogorov distance controls the bounded Lipschitz distance.** For a probability measure
`ν` on `ℝ` and `ε > 0` there is `δ > 0` such that every probability measure within Kolmogorov
distance `δ` of `ν` is within bounded Lipschitz distance `ε` of it. -/
theorem exists_pos_forall_kolmogorovDist_lt_boundedLipschitzDist_lt (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (Q : Measure ℝ) [IsProbabilityMeasure Q],
      kolmogorovDist Q ν < δ → boundedLipschitzDist Q ν < ε := by
  by_contra! h
  choose Q hQ hQν hεQ using fun n : ℕ ↦ h (1 / (n + 1)) Nat.one_div_pos_of_nat
  let Qs : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨Q n, hQ n⟩
  have hK : Tendsto (fun n ↦ kolmogorovDist (Qs n) (⟨ν, inferInstance⟩ : ProbabilityMeasure ℝ))
      atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ kolmogorovDist_nonneg _ _) (fun n ↦ (hQν n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hB := ProbabilityMeasure.tendsto_boundedLipschitzDist_iff_tendsto.2
    (ProbabilityMeasure.tendsto_of_tendsto_kolmogorovDist hK)
  obtain ⟨n, hn⟩ := (hB.eventually (gt_mem_nhds hε)).exists
  exact (hεQ n).not_gt hn

end ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

/-- Convergence of probability measures on `ℝ` in the Kolmogorov distance implies convergence in
the bounded Lipschitz distance, along any filter and whatever the limit. -/
theorem tendsto_boundedLipschitzDist_of_tendsto_kolmogorovDist {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto (fun i ↦ kolmogorovDist (μs i) μ) l (𝓝 0)) :
    Tendsto (fun i ↦ boundedLipschitzDist (μs i : Measure ℝ) μ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hQ⟩ :=
    exists_pos_forall_kolmogorovDist_lt_boundedLipschitzDist_lt (μ : Measure ℝ) hε
  filter_upwards [h.eventually (gt_mem_nhds hδ)] with i hi using (hQ _ hi).le

end MeasureTheory.ProbabilityMeasure
