/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Maximal inequality for finitely many sub-Gaussian variables

If `Z₁, …, Z_N` (`N ≥ 1`) each satisfy a sub-Gaussian moment-generating function bound with
variance proxy `c`, then, with no independence assumed,
`μ {√(2c(log N + t)) < maxⱼ |Zⱼ|} ≤ 2 exp (-t)` for every real `t` (for `t < 0` the right side
exceeds `1`). The proof is a union bound over the two-sided Chernoff tails of the `Zⱼ`.

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

/-- The tail bound of one sub-Gaussian variable at the level `√(2c(L + t))`, in the form used by
the union bound of `measure_max_abs_gt_le`. The strict exceedance keeps the case `c = 0`. -/
private theorem measureReal_sqrt_lt_abs_le {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {L t : ℝ} (hLt : 0 ≤ L + t) :
    μ.real {ω | √(2 * c * (L + t)) < |X ω|} ≤ 2 * exp (-(L + t)) := by
  have : IsFiniteMeasure μ := by
    simpa using (HasSubgaussianMGF_iff_kernel.1 hX).isFiniteMeasure
  rcases eq_or_ne c 0 with rfl | hc0
  · have hnull : μ.real {ω | √(2 * ((0 : ℝ≥0) : ℝ) * (L + t)) < |X ω|} = 0 := by
      refine (measureReal_eq_zero_iff (by finiteness)).2 (measure_mono_null (fun ω hω ↦ ?_)
        (ae_iff.1 hX.ae_eq_zero_of_hasSubgaussianMGF_zero))
      simpa using hω
    rw [hnull]
    positivity
  set s := √(2 * c * (L + t))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hexp : -s ^ 2 / (2 * c) = -(L + t) := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp [NNReal.coe_ne_zero.2 hc0]
  calc μ.real {ω | s < |X ω|}
      ≤ μ.real {ω | s ≤ |X ω|} := measureReal_mono fun ω (hω : s < |X ω|) ↦ hω.le
    _ ≤ μ.real {ω | s ≤ X ω} + μ.real {ω | s ≤ -X ω} := measureReal_le_abs_le_add
    _ ≤ exp (-s ^ 2 / (2 * c)) + exp (-s ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hs) (hX.neg.measure_ge_le hs)
    _ = 2 * exp (-(L + t)) := by rw [hexp]; ring

/-- **Maximal inequality** for finitely many sub-Gaussian variables, without independence: if
each `Zⱼ` has variance proxy `c`, then for `t ≥ 0` the maximum of the `|Zⱼ|` exceeds
`√(2c(log N + t))`, with `N` the number of variables, with probability at most `2 exp (-t)`.
The bound is trivial for `t < 0`, so no sign condition on `t` is needed. -/
theorem measure_max_abs_gt_le [Fintype ι] [Nonempty ι] {Z : ι → Ω → ℝ} {c : ℝ≥0}
    (hZ : ∀ j, HasSubgaussianMGF (Z j) c μ) (t : ℝ) :
    μ.real {ω | √(2 * c * (Real.log (Fintype.card ι) + t)) <
      Finset.univ.sup' Finset.univ_nonempty (fun j ↦ |Z j ω|)} ≤ 2 * exp (-t) := by
  set L := Real.log (Fintype.card ι)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  rcases lt_or_ge t 0 with ht | ht
  · obtain ⟨j⟩ := ‹Nonempty ι›
    have : IsFiniteMeasure μ := by
      simpa using (HasSubgaussianMGF_iff_kernel.1 (hZ j)).isFiniteMeasure
    have huniv : μ.real Set.univ ≤ 1 := by simpa [mgf] using (hZ j).mgf_le 0
    have hexp : 1 ≤ exp (-t) := Real.one_le_exp (by linarith)
    exact (measureReal_mono (Set.subset_univ _)).trans (by linarith)
  have hset : {ω | √(2 * c * (L + t)) <
      Finset.univ.sup' Finset.univ_nonempty (fun j ↦ |Z j ω|)} =
      ⋃ j, {ω | √(2 * c * (L + t)) < |Z j ω|} := by
    ext ω
    simp [Finset.lt_sup'_iff]
  calc μ.real {ω | √(2 * c * (L + t)) <
        Finset.univ.sup' Finset.univ_nonempty (fun j ↦ |Z j ω|)}
      ≤ ∑ j, μ.real {ω | √(2 * c * (L + t)) < |Z j ω|} := by
        rw [hset]
        exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : ι, 2 * exp (-(L + t)) :=
        Finset.sum_le_sum fun j _ ↦ measureReal_sqrt_lt_abs_le (hZ j) (by linarith)
    _ = 2 * exp (-t) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, neg_add, Real.exp_add,
          Real.exp_neg, Real.exp_log hN]
        field_simp

end TauCeti
