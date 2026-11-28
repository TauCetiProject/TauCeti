/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.GaltonWatson.Kernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Fixed points of the offspring generating function

Let `ν` be an offspring law, a probability measure on `ℕ`, with generating function
`f = pgf id ν` and mean `m = ν.offspringMean` in `[0, ∞]`. The probability that a Galton–Watson
process with offspring law `ν` has died out by generation `n` is the iterate `f^[n] 0`, and its
extinction probability is the limit of these iterates, which by
`TauCeti.Probability.isLeast_iSup_iterate_pgf_zero` is the least fixed point of `f` in `[0, 1]`;
the general fixed-point analysis of `f`, which does not involve the mean, is in
`TauCeti.Probability.GeneratingFunction`. This file adds the step that involves `m`: because `f`
is convex with `f 1 = 1` and its derivative increases to `m`, the least fixed point is `1` exactly
when `m ≤ 1` and `ν` is not the point mass at `1`.

## Main results

* `MeasureTheory.Measure.isLeast_pgf_eq_self_one_iff`: the least fixed point is `1` if and only if
  `m ≤ 1` and `ν {1} ≠ 1`.

## References

* R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press (2016),
  Section 5.1, Proposition 5.4 and Corollary 5.3.
* R. Durrett, *Probability: Theory and Examples*, fifth edition, Cambridge University Press
  (2019), Section 4.3.4, Theorems 4.3.10 to 4.3.12.
-/

public section

noncomputable section

open Filter Set TauCeti.Probability
open scoped ENNReal Topology

namespace MeasureTheory.Measure

variable (ν : Measure ℕ) [IsProbabilityMeasure ν]

/-- Mean value theorem for the generating function `f` of a probability measure on `ℕ` on the
interval `[t, 1]`, where `f 1 = 1`. -/
private theorem exists_deriv_pgf_eq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ c ∈ Ioo t 1, deriv (pgf id ν) c = (1 - pgf id ν t) / (1 - t) := by
  have hcont : ContinuousOn (pgf id ν) (Icc t 1) :=
    (continuousOn_pgf ν).mono (Icc_subset_Icc (by linarith) le_rfl)
  have hdiff : DifferentiableOn ℝ (pgf id ν) (Ioo t 1) :=
    (analyticOnNhd_pgf ν).differentiableOn.mono (Ioo_subset_Ioo (by linarith) le_rfl)
  simpa using exists_deriv_eq_slope (pgf id ν) ht1 hcont hdiff

/-- If `m > 1`, the generating function `f` of a probability measure on `ℕ` lies below the
diagonal at some point of `[0, 1)`. -/
private theorem exists_pgf_lt_self_of_one_lt_offspringMean (hm : 1 < ν.offspringMean) :
    ∃ t, 0 ≤ t ∧ t < 1 ∧ pgf id ν t < t := by
  -- the derivative tends to `m > 1`, so it exceeds `1` on some interval `(l, 1)`
  rw [offspringMean_def] at hm
  have hev : ∀ᶠ u in 𝓝[<] (1 : ℝ), 1 < ENNReal.ofReal (deriv (pgf id ν) u) :=
    (tendsto_order.1 (tendsto_ofReal_deriv_pgf_nhdsLT_one ν)).1 1 hm
  obtain ⟨l, hl, hlu⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  set t := max l 0
  have ht1 : t < 1 := max_lt hl zero_lt_one
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_pgf_eq ν (le_max_right l 0) ht1
  have hc1 : 1 < deriv (pgf id ν) c :=
    ENNReal.one_lt_ofReal.1 (hlu ⟨(le_max_left l 0).trans_lt hc.1, hc.2⟩)
  rw [hderiv, one_lt_div (by linarith)] at hc1
  exact ⟨t, le_max_right l 0, ht1, by linarith⟩

/-- The least fixed point in `[0, 1]` of the generating function `f` of a probability measure `ν`
on `ℕ` is `1` if and only if the mean `m` of `ν` is at most `1` and `ν` is not the point mass at
`1`. When `ν {1} = 1`, `f` is the identity and its least fixed point is `0`. -/
theorem isLeast_pgf_eq_self_one_iff :
    IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} 1 ↔ ν.offspringMean ≤ 1 ∧ ν {1} ≠ 1 := by
  constructor
  · rintro ⟨-, hle⟩
    refine ⟨?_, fun h1 => ?_⟩
    · -- if `m > 1`, the function `u ↦ f u - u` changes sign on some `[0, t]` with `t < 1`
      by_contra! hm
      obtain ⟨t, ht0, ht1, hft⟩ := exists_pgf_lt_self_of_one_lt_offspringMean ν hm
      have hcont : ContinuousOn (fun u => pgf id ν u - u) (Icc 0 t) :=
        ((continuousOn_pgf ν).mono (Icc_subset_Icc (by norm_num) ht1.le)).sub continuousOn_id
      have hzero : (0 : ℝ) ∈ Icc (pgf id ν t - t) (pgf id ν 0 - 0) :=
        ⟨by linarith, by simp⟩
      obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' ht0 hcont hzero
      exact (hle ⟨hu.1, hu.2.trans ht1.le, sub_eq_zero.1 hfu⟩).not_gt (hu.2.trans_lt ht1)
    · -- if `ν {1} = 1`, then `ν {0} = 0` and `0` is a fixed point
      have h0 : ν {0} = 0 :=
        measure_mono_null (by simp) ((prob_compl_eq_zero_iff (measurableSet_singleton 1)).2 h1)
      exact (hle ⟨le_rfl, zero_le_one, by simp [measureReal_def, h0]⟩).not_gt one_pos
  · rintro ⟨hm, h1⟩
    refine ⟨⟨zero_le_one, le_rfl, by simp⟩, fun s ⟨hs0, _, hfs⟩ => ?_⟩
    by_contra! hs1
    rcases (ν.measure_singleton_add_measure_singleton_le zero_ne_one).lt_or_eq with h | h
    · -- strictly convex case: `f` is below the diagonal on `(s, 1)`, so its slope on `[t, 1]`
      -- exceeds `1` for `t = (s + 1) / 2`, while its derivative is at most `m ≤ 1`
      have ht := pgf_lt_self_of_add_lt_one ν h hs0 le_rfl hfs (by simp)
        (t := (s + 1) / 2) (by linarith) (by linarith)
      obtain ⟨c, hc, hderiv⟩ := exists_deriv_pgf_eq ν (t := (s + 1) / 2) (by linarith)
        (by linarith)
      have hc1 : deriv (pgf id ν) c ≤ 1 := ENNReal.ofReal_le_one.1 <|
        (ofReal_deriv_pgf_le ν ⟨by linarith [hc.1], hc.2⟩).trans (by rwa [offspringMean_def] at hm)
      rw [hderiv, div_le_one (by linarith)] at hc1
      linarith
    · exact hs1.ne (eq_one_of_pgf_eq_self_of_add_eq_one ν h h1 hfs)

end MeasureTheory.Measure
