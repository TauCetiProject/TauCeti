/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.GaltonWatson.Kernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fixed points of the offspring generating function

Let `ν` be an offspring law, a probability measure on `ℕ`, with generating function
`f = pgf id ν` and mean `m = ν.offspringMean` in `[0, ∞]`. The probability that a Galton–Watson
process with offspring law `ν` has died out by generation `n` is the iterate `f^[n] 0`, and its
extinction probability is the limit of these iterates. This file carries out the analysis of `f`
on `[0, 1]` that identifies that limit, independently of the process.

The iterates `f^[n] 0` increase, and they stay below every fixed point of `f` in `[0, 1]`; since
`f` is continuous, their limit is the least fixed point of `f` in `[0, 1]`. Because `f` is
convex with `f 1 = 1` and its derivative increases to `m`, the least fixed point is `1` exactly
when `m ≤ 1` and `ν` is not the point mass at `1`. Unless `ν` is that point mass, `f` has at
most two fixed points in `[0, 1]`, the least one and `1`.

## Main results

* `MeasureTheory.Measure.monotone_iterate_pgf_zero` and
  `MeasureTheory.Measure.iterate_pgf_zero_le`: the iterates `f^[n] 0` increase and lie below every
  nonnegative fixed point of `f`.
* `MeasureTheory.Measure.isLeast_of_tendsto_iterate_pgf_zero` and
  `MeasureTheory.Measure.isLeast_iSup_iterate_pgf_zero`: the limit of the iterates is the least
  fixed point of `f` in `[0, 1]`.
* `MeasureTheory.Measure.isLeast_pgf_eq_self_one_iff`: the least fixed point is `1` if and only if
  `m ≤ 1` and `ν {1} ≠ 1`.
* `MeasureTheory.Measure.setOf_pgf_eq_self_eq_pair`: if `ν {1} ≠ 1`, the fixed points of `f` in
  `[0, 1]` are the least one and `1`.

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

/-- The iterates `f^[n] 0` of the generating function of a probability measure on `ℕ` lie in
`[0, 1]`. -/
private theorem iterate_pgf_zero_mem_Icc (n : ℕ) : (pgf id ν)^[n] 0 ∈ Icc (0 : ℝ) 1 :=
  (mapsTo_pgf_Icc ν).iterate n ⟨le_rfl, zero_le_one⟩

/-- The iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ` form a
nondecreasing sequence. -/
theorem monotone_iterate_pgf_zero : Monotone fun n => (pgf id ν)^[n] 0 := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact (iterate_pgf_zero_mem_Icc ν 1).1
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (n + 1)]
    exact monotoneOn_pgf ν (iterate_pgf_zero_mem_Icc ν n) (iterate_pgf_zero_mem_Icc ν (n + 1)) ih

/-- The iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ` lie
below every nonnegative fixed point of `f`. -/
theorem iterate_pgf_zero_le {s : ℝ} (hs : 0 ≤ s) (hfs : pgf id ν s = s) (n : ℕ) :
    (pgf id ν)^[n] 0 ≤ s := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rcases le_or_gt s 1 with hs1 | hs1
    · rw [Function.iterate_succ_apply', ← hfs]
      exact monotoneOn_pgf ν (iterate_pgf_zero_mem_Icc ν n) ⟨hs, hs1⟩ ih
    · exact (iterate_pgf_zero_mem_Icc ν (n + 1)).2.trans hs1.le

/-- If the iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ`
converge to `q`, then `q` is the least fixed point of `f` in `[0, 1]`. -/
theorem isLeast_of_tendsto_iterate_pgf_zero {q : ℝ}
    (hq : Tendsto (fun n => (pgf id ν)^[n] 0) atTop (𝓝 q)) :
    IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} q := by
  have hmem : q ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hq (Eventually.of_forall (iterate_pgf_zero_mem_Icc ν))
  have hcont : ContinuousWithinAt (pgf id ν) (Icc 0 1) q :=
    ((continuousOn_pgf ν).mono (Icc_subset_Icc (by norm_num) le_rfl)) q hmem
  have hlim : Tendsto (fun n => pgf id ν ((pgf id ν)^[n] 0)) atTop (𝓝 (pgf id ν q)) :=
    hcont.tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hq, Eventually.of_forall (iterate_pgf_zero_mem_Icc ν)⟩)
  have hshift : Tendsto (fun n => pgf id ν ((pgf id ν)^[n] 0)) atTop (𝓝 q) := by
    simpa only [Function.iterate_succ_apply'] using (tendsto_add_atTop_iff_nat 1).2 hq
  refine ⟨⟨hmem.1, hmem.2, tendsto_nhds_unique hlim hshift⟩, fun s hs => ?_⟩
  exact le_of_tendsto' hq (iterate_pgf_zero_le ν hs.1 hs.2.2)

/-- The iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ`
converge to their supremum. -/
theorem tendsto_iterate_pgf_zero :
    Tendsto (fun n => (pgf id ν)^[n] 0) atTop (𝓝 (⨆ n, (pgf id ν)^[n] 0)) :=
  tendsto_atTop_ciSup (monotone_iterate_pgf_zero ν)
    ⟨1, forall_mem_range.2 fun n => (iterate_pgf_zero_mem_Icc ν n).2⟩

/-- The generating function `f` of a probability measure on `ℕ` has a least fixed point in
`[0, 1]`, the supremum of the iterates `f^[n] 0`. -/
theorem isLeast_iSup_iterate_pgf_zero :
    IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} (⨆ n, (pgf id ν)^[n] 0) :=
  isLeast_of_tendsto_iterate_pgf_zero ν (tendsto_iterate_pgf_zero ν)

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

/-- The masses of `0` and `1` under a probability measure on `ℕ` add up to at most `1`. -/
private theorem measure_zero_add_measure_one_le : ν {0} + ν {1} ≤ 1 :=
  (measure_union (by simp) (measurableSet_singleton 1)).symm.trans_le prob_le_one

/-- If `ν {0} + ν {1} < 1`, the generating function `f` of a probability measure on `ℕ` lies
strictly below the diagonal between two fixed points in `[0, 1]`. -/
private theorem pgf_lt_self_of_add_lt_one (h : ν {0} + ν {1} < 1) {a b t : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ 1) (hfa : pgf id ν a = a) (hfb : pgf id ν b = b) (hat : a < t) (htb : t < b) :
    pgf id ν t < t := by
  have hab : 0 < b - a := by linarith
  have hl : 0 < (b - t) / (b - a) := div_pos (by linarith) hab
  have hr : 0 < (t - a) / (b - a) := div_pos (by linarith) hab
  have hconv := (strictConvexOn_pgf_of_add_lt_one ν h).2 (⟨ha, by linarith⟩ : a ∈ Icc (0 : ℝ) 1)
    (⟨by linarith, hb⟩ : b ∈ Icc (0 : ℝ) 1) (sub_pos.1 hab).ne hl hr (by field_simp; ring)
  have hcomb : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by
    field_simp; ring
  simpa only [smul_eq_mul, hfa, hfb, hcomb] using hconv

/-- If `ν {0} + ν {1} = 1` and `ν {1} ≠ 1`, the only fixed point of the generating function of a
probability measure on `ℕ` is `1`. -/
private theorem eq_one_of_pgf_eq_self_of_add_eq_one (h : ν {0} + ν {1} = 1) (h1 : ν {1} ≠ 1)
    {s : ℝ} (hfs : pgf id ν s = s) : s = 1 := by
  have hreal : ν.real {0} + ν.real {1} = 1 := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add (measure_ne_top ν _)
      (measure_ne_top ν _), h, ENNReal.toReal_one]
  have h1' : 1 - ν.real {1} ≠ 0 :=
    sub_ne_zero.2 fun h' => h1 ((ENNReal.toReal_eq_one_iff _).1 h'.symm)
  rw [pgf_eq_of_add_eq_one ν h] at hfs
  have : (1 - ν.real {1}) * (1 - s) = 0 := by linear_combination hfs - hreal
  linarith [(mul_eq_zero.1 this).resolve_left h1']

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
    rcases (measure_zero_add_measure_one_le ν).lt_or_eq with h | h
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

/-- Unless every individual has exactly one child, the fixed points in `[0, 1]` of the generating
function of a probability measure on `ℕ` are its least fixed point `q` there and `1`. -/
theorem setOf_pgf_eq_self_eq_pair (h1 : ν {1} ≠ 1) {q : ℝ}
    (hq : IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} q) :
    {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} = {q, 1} := by
  ext s
  refine ⟨fun hs => ?_, ?_⟩
  · rcases hs.2.1.lt_or_eq with hs1 | rfl
    · left
      rcases (measure_zero_add_measure_one_le ν).lt_or_eq with h | h
      · refine (hq.2 hs).antisymm' (not_lt.1 fun hqs => ?_)
        exact (pgf_lt_self_of_add_lt_one ν h hq.1.1 le_rfl hq.1.2.2 (by simp) hqs hs1).ne
          hs.2.2
      · exact absurd (eq_one_of_pgf_eq_self_of_add_eq_one ν h h1 hs.2.2) hs1.ne
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact hq.1
    · exact ⟨zero_le_one, le_rfl, by simp⟩

end MeasureTheory.Measure
