/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.MeasureTheory.Measure.Tail
import TauCeti.Probability.Moments.SubGaussian.Basic

/-!
# Two-sided sub-Gaussian tails

A random variable `X` that is sub-Gaussian with variance proxy `c` satisfies the two-sided Chernoff
bound `P(ε ≤ |X|) ≤ 2 exp (-ε² / (2c))` for `ε ≥ 0`, the sum of Mathlib's upper-tail bound for `X`
and for `-X`. At the level `√(2cb)` the strict exceedance has probability at most `2 exp (-b)` for
every real `b`, including the degenerate proxy `c = 0`.

**Maximal inequality.** If `Zⱼ`, for `j` in a nonempty finite set `s` of `N` indices, each have
variance proxy `c`, then, with no independence assumed,
`μ {√(2c(log N + t)) < maxⱼ |Zⱼ|} ≤ 2 exp (-t)` for every real `t`. For a confidence level
`0 < δ ≤ 1`, take `t = log (2 / δ)`: outside an event of measure at most `δ`, all the `|Zⱼ|` are
at most `√(2c(log N + log (2 / δ)))` simultaneously. The measure `μ` need not be normalized; the
sub-Gaussian bound forces `μ univ ≤ 1`.

If `g - c` is sub-Gaussian with variance proxy `σ` and the center `c` is within `ε / 2` of a
target `t`, then `g` deviates from `t` by at least `ε` with probability at most
`2 exp (-(ε / 2)² / (2σ))`. This is how a concentration bound centered at the mean transfers to a
nearby target value.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.measureReal_abs_ge_le`
* `ProbabilityTheory.HasSubgaussianMGF.measureReal_abs_gt_sqrt_le`
* `TauCeti.measure_max_abs_gt_le`
* `TauCeti.Probability.measureReal_abs_sub_ge_le_of_hasSubgaussianMGF`

## References

* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`.
  The two-tail calculation is adapted from that file; here it is stated for an arbitrary measure
  and a general sub-Gaussian variable rather than for the graphon sampling law.
* M. J. Wainwright, *High-Dimensional Statistics* (2019), Chapter 2 (maximal inequality).
-/

public section

open MeasureTheory ProbabilityTheory Real Set

open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- **Two-sided Chernoff bound** for a sub-Gaussian random variable: if `X` is sub-Gaussian with
variance proxy `c`, then `|X| ≥ ε` has probability at most `2 exp (-ε² / (2c))` for `ε ≥ 0`. -/
theorem measureReal_abs_ge_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) :=
  calc μ.real {ω | ε ≤ |X ω|} ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} :=
        TauCeti.measureReal_le_abs_le_add
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
        add_le_add (h.measure_ge_le hε) (h.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

/-- **Strict two-sided tail at a square-root level**: if `X` is sub-Gaussian with variance proxy
`c`, then `|X|` strictly exceeds `√(2 * c * b)` with measure at most `2 exp (-b)`, for every real
`b`. Because the exceedance is strict, this also holds for `c = 0`, where `X` vanishes almost
everywhere; for `b < 0` the right side exceeds `1`. -/
theorem measureReal_abs_gt_sqrt_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) (b : ℝ) :
    μ.real {ω | √(2 * c * b) < |X ω|} ≤ 2 * Real.exp (-b) := by
  have : IsFiniteMeasure μ := h.isFiniteMeasure
  rcases lt_or_ge b 0 with hb | hb
  · have hreal : μ.real Set.univ ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h.measure_univ_le_one)
    have hexp : 1 ≤ Real.exp (-b) := Real.one_le_exp (by linarith)
    exact (measureReal_mono (Set.subset_univ _)).trans (by linarith)
  rcases eq_or_ne c 0 with rfl | hc0
  · have hnull : μ.real {ω | √(2 * ((0 : ℝ≥0) : ℝ) * b) < |X ω|} = 0 := by
      refine (measureReal_eq_zero_iff (by finiteness)).2 (measure_mono_null (fun ω hω ↦ ?_)
        (ae_iff.1 h.ae_eq_zero_of_hasSubgaussianMGF_zero))
      simpa using hω
    rw [hnull]
    positivity
  calc μ.real {ω | √(2 * c * b) < |X ω|}
      ≤ μ.real {ω | √(2 * c * b) ≤ |X ω|} := measureReal_mono fun ω (hω : _ < _) ↦ hω.le
    _ ≤ 2 * Real.exp (-√(2 * c * b) ^ 2 / (2 * c)) := h.measureReal_abs_ge_le (Real.sqrt_nonneg _)
    _ = 2 * Real.exp (-b) := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp [NNReal.coe_ne_zero.2 hc0]

end ProbabilityTheory.HasSubgaussianMGF

namespace TauCeti.Probability

/-- Two-sided sub-Gaussian tail around a shifted center: if `g - c` is sub-Gaussian with variance
proxy `σ` and the center `c` is within `ε / 2` of the target `t`, then `g` deviates from `t` by at
least `ε` with probability at most `2 exp (-(ε / 2)² / (2σ))`. -/
theorem measureReal_abs_sub_ge_le_of_hasSubgaussianMGF {α : Type*} [MeasurableSpace α]
    {P : Measure α} {g : α → ℝ} {c t ε : ℝ} {σ : ℝ≥0}
    (h : ProbabilityTheory.HasSubgaussianMGF (fun x => g x - c) σ P) (hct : |c - t| ≤ ε / 2) :
    P.real {x | ε ≤ |g x - t|} ≤ 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by
  have hε : 0 ≤ ε := by linarith [abs_nonneg (c - t)]
  have : IsFiniteMeasure P := h.isFiniteMeasure
  have hincl : {x | ε ≤ |g x - t|} ⊆ {x | ε / 2 ≤ |g x - c|} := fun x hx => by
    rw [Set.mem_ofPred_eq] at hx ⊢
    have htri : |g x - t| ≤ |g x - c| + |c - t| := abs_sub_le _ _ _
    linarith
  exact (measureReal_mono hincl).trans (h.measureReal_abs_ge_le (by positivity))

end TauCeti.Probability

namespace TauCeti

/-- **Maximal inequality** for finitely many sub-Gaussian variables, without independence: if
`Zⱼ` has variance proxy `c` for each `j` in a nonempty finite set `s` of `N` indices, then the
event that the maximum over `s` of the `|Zⱼ|` strictly exceeds `√(2c(log N + t))` has
`μ`-measure at most `2 exp (-t)`. The measure `μ` need not be normalized, and the bound is
trivial for `t < 0`, so no sign condition on `t` is needed. -/
theorem measure_max_abs_gt_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : Finset ι}
    (hs : s.Nonempty) {Z : ι → Ω → ℝ} {c : ℝ≥0} (hZ : ∀ j ∈ s, HasSubgaussianMGF (Z j) c μ)
    (t : ℝ) :
    μ.real {ω | √(2 * c * (Real.log s.card + t)) < s.sup' hs (fun j ↦ |Z j ω|)} ≤
      2 * exp (-t) := by
  have : IsFiniteMeasure μ := (hZ _ hs.choose_spec).isFiniteMeasure
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  set r := √(2 * c * (Real.log s.card + t))
  have hset : {ω | r < s.sup' hs (fun j ↦ |Z j ω|)} = ⋃ j ∈ s, {ω | r < |Z j ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact Finset.lt_sup'_iff _
  calc μ.real {ω | r < s.sup' hs (fun j ↦ |Z j ω|)}
      ≤ ∑ j ∈ s, μ.real {ω | r < |Z j ω|} := by
        rw [hset]
        exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ s, 2 * exp (-(Real.log s.card + t)) :=
        Finset.sum_le_sum fun j hj ↦ (hZ j hj).measureReal_abs_gt_sqrt_le _
    _ = 2 * exp (-t) := by
        rw [Finset.sum_const, nsmul_eq_mul, neg_add, Real.exp_add, Real.exp_neg,
          Real.exp_log hN]
        field_simp

end TauCeti
