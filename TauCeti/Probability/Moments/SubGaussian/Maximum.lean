/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.Probability.Concentration.SubgaussianTail

/-!
# Maximal inequality for finitely many sub-Gaussian variables

If `Zⱼ`, for `j` in a nonempty finite set `s` of `N` indices, each satisfy a sub-Gaussian
moment-generating function bound with variance proxy `c`, then, with no independence assumed,
`μ {√(2c(log N + t)) < maxⱼ |Zⱼ|} ≤ 2 exp (-t)` for every real `t` (for `t < 0` the right side
exceeds `1`). The proof is a union bound over the two-sided sub-Gaussian tails of the `Zⱼ`
(`ProbabilityTheory.HasSubgaussianMGF.measureReal_abs_ge_le`). The measure `μ` need not be
normalized; the sub-Gaussian bound forces `μ univ ≤ 1`.

The exceedance is strict: for `c = 0` every `Zⱼ` vanishes almost everywhere, so the strict event
is null, whereas the closed event `{0 ≤ maxⱼ |Zⱼ|}` has full measure.

## Main result

* `TauCeti.measure_max_abs_gt_le`

## References

* M. J. Wainwright, *High-Dimensional Statistics* (2019), Chapter 2.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Maximal inequality** for finitely many sub-Gaussian variables, without independence: if
`Zⱼ` has variance proxy `c` for each `j` in a nonempty finite set `s` of `N` indices, then the
event that the maximum over `s` of the `|Zⱼ|` strictly exceeds `√(2c(log N + t))` has
`μ`-measure at most `2 exp (-t)`. The measure `μ` need not be normalized, and the bound is
trivial for `t < 0`, so no sign condition on `t` is needed. -/
theorem measure_max_abs_gt_le {s : Finset ι} (hs : s.Nonempty) {Z : ι → Ω → ℝ} {c : ℝ≥0}
    (hZ : ∀ j ∈ s, HasSubgaussianMGF (Z j) c μ) (t : ℝ) :
    μ.real {ω | √(2 * c * (Real.log s.card + t)) < s.sup' hs (fun j ↦ |Z j ω|)} ≤
      2 * exp (-t) := by
  set L := Real.log s.card
  set r := √(2 * c * (L + t))
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hs.card_pos)
  obtain ⟨j₀, hj₀⟩ := hs
  have huniv : μ Set.univ ≤ 1 := by
    simpa using (HasSubgaussianMGF_iff_kernel.1 (hZ j₀ hj₀)).measure_univ_le_one
  have : IsFiniteMeasure μ := ⟨huniv.trans_lt ENNReal.one_lt_top⟩
  rcases lt_or_ge t 0 with ht | ht
  · have hexp : 1 ≤ exp (-t) := Real.one_le_exp (by linarith)
    have hreal : μ.real Set.univ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa)
    exact (measureReal_mono (Set.subset_univ _)).trans (by linarith)
  -- The tail of one variable at the level `r`; the strict exceedance covers `c = 0`.
  have hone : ∀ j ∈ s, μ.real {ω | r < |Z j ω|} ≤ 2 * exp (-(L + t)) := by
    intro j hj
    rcases eq_or_ne c 0 with rfl | hc0
    · have hnull : μ.real {ω | r < |Z j ω|} = 0 := by
        refine (measureReal_eq_zero_iff (by finiteness)).2 (measure_mono_null (fun ω hω ↦ ?_)
          (ae_iff.1 (hZ j hj).ae_eq_zero_of_hasSubgaussianMGF_zero))
        simpa [r] using hω
      rw [hnull]
      positivity
    calc μ.real {ω | r < |Z j ω|}
        ≤ μ.real {ω | r ≤ |Z j ω|} := measureReal_mono fun ω (hω : r < |Z j ω|) ↦ hω.le
      _ ≤ 2 * exp (-r ^ 2 / (2 * c)) :=
        (hZ j hj).measureReal_abs_ge_le (Real.sqrt_nonneg _)
      _ = 2 * exp (-(L + t)) := by
        rw [Real.sq_sqrt (by positivity)]
        field_simp [NNReal.coe_ne_zero.2 hc0]
  have hset : {ω | r < s.sup' ⟨j₀, hj₀⟩ (fun j ↦ |Z j ω|)} = ⋃ j ∈ s, {ω | r < |Z j ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact Finset.lt_sup'_iff _
  have hexpL : exp (-L) = (s.card : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hN]
  calc μ.real {ω | r < s.sup' ⟨j₀, hj₀⟩ (fun j ↦ |Z j ω|)}
      ≤ ∑ j ∈ s, μ.real {ω | r < |Z j ω|} := by
        rw [hset]
        exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ s, 2 * exp (-(L + t)) := Finset.sum_le_sum hone
    _ = s.card * (2 * (exp (-L) * exp (-t))) := by
        rw [Finset.sum_const, nsmul_eq_mul, neg_add, Real.exp_add]
    _ = 2 * exp (-t) := by
        rw [hexpL]
        field_simp

end TauCeti
