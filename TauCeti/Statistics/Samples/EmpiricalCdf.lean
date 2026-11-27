/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.Probability.Process.EmpiricalMeasure
public import TauCeti.Probability.Quantile

/-!
# The empirical distribution function and the sample quantile

For a finite real sample `x : κ → ℝ`, the *empirical distribution function* is the proportion of
observations at most `t`,

`empiricalCdf x t = #{i | x i ≤ t} / card κ`,

and the *sample quantile* at level `p` is its left generalized inverse,

`sampleQuantile x p = sInf {t | p ≤ empiricalCdf x t}`.

For a nonempty sample these are the distribution function and the quantile function of the
empirical distribution `TauCeti.Probability.empiricalFiniteMeasure x`, so the general theory of
`ProbabilityTheory.cdf` and `MeasureTheory.Measure.quantile` applies to them. The statements below
are what is specific to a finite sample: the empirical distribution function takes the values
`k / card κ`, vanishing below every observation and equal to `1` above every observation, and the
sample quantile at a level in `(0, 1]` is a sample point, namely an explicit order statistic. In
particular the Galois inequality `sampleQuantile x p ≤ t ↔ p ≤ empiricalCdf x t` holds at the
endpoint level `p = 1` as well, which is not the case for an arbitrary law on `ℝ`.

These are the objects through which asymptotic statements about empirical processes and sample
quantiles (Glivenko–Cantelli, Donsker, the Bahadur representation) are formulated: a statistic
of an i.i.d. sample of size `n` is a function of `x : Fin n → ℝ`, and the sequence form, the first
`n` observations of `x : ℕ → ℝ`, is `fun i : Fin n ↦ x i`.

## Main definitions

* `TauCeti.empiricalCdf` — the empirical distribution function of a finite sample;
* `TauCeti.sampleQuantile` — the sample quantile, the left generalized inverse of
  `TauCeti.empiricalCdf`.

## Main statements

* `TauCeti.cdf_empiricalFiniteMeasure` and `TauCeti.sampleQuantile_eq_quantile` — the two
  objects are the distribution function and the quantile function of the empirical distribution;
* `TauCeti.cdf_empiricalMeasure` and `TauCeti.empiricalCdf_fin_eq_card_filter_range` — the
  sequence forms;
* `TauCeti.monotone_empiricalCdf`, `TauCeti.continuousWithinAt_Ici_empiricalCdf`,
  `TauCeti.tendsto_empiricalCdf_atBot` and `TauCeti.tendsto_empiricalCdf_atTop` — the empirical
  distribution function is a distribution function;
* `TauCeti.sampleQuantile_le_iff` — the Galois inequality at every level `p ∈ (0, 1]`;
* `TauCeti.sampleQuantile_mem_range` and `TauCeti.sampleQuantile_eq_orderStatistic` — the sample
  `p`-quantile of `n` observations is the order statistic in position `⌈n p⌉ - 1`;
* `TauCeti.measurable_empiricalCdf` and `TauCeti.measurable_sampleQuantile` — measurability in
  the sample.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §19.1 (p. 265)
  for the empirical distribution function and Lemma 21.1 (p. 304) for the Galois inequality.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Finset Topology
open TauCeti.Probability (empiricalFiniteMeasure empiricalMeasure)
open scoped ENNReal

namespace TauCeti

variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-! ### The empirical distribution function -/

/-- The **empirical distribution function** of a finite real sample `x : κ → ℝ`: the proportion
`#{i | x i ≤ t} / card κ` of observations at most `t`, counted with multiplicity.

For a nonempty sample it is the distribution function of the empirical distribution
(`TauCeti.cdf_empiricalFiniteMeasure`). For an empty sample it is the junk value `0`, whereas
Mathlib's `ProbabilityTheory.cdf` of the zero measure is a genuine distribution function. -/
def empiricalCdf (x : κ → ℝ) (t : ℝ) : ℝ :=
  (#{i | x i ≤ t} : ℝ) / Fintype.card κ

/-- The empirical distribution function is the proportion of observations at most `t`. The
definition's body is not exposed, so this is the lemma downstream modules rewrite with. -/
theorem empiricalCdf_def (x : κ → ℝ) (t : ℝ) :
    empiricalCdf x t = (#{i | x i ≤ t} : ℝ) / Fintype.card κ := (rfl)

/-- The empirical distribution function of an empty sample is the junk value `0`. -/
@[simp]
theorem empiricalCdf_of_isEmpty [IsEmpty κ] (x : κ → ℝ) (t : ℝ) : empiricalCdf x t = 0 := by
  simp [empiricalCdf_def]

/-- The empirical distribution function is nonnegative. -/
theorem empiricalCdf_nonneg (x : κ → ℝ) (t : ℝ) : 0 ≤ empiricalCdf x t := by
  rw [empiricalCdf_def]
  positivity

/-- The empirical distribution function is at most `1`. -/
theorem empiricalCdf_le_one (x : κ → ℝ) (t : ℝ) : empiricalCdf x t ≤ 1 := by
  rw [empiricalCdf_def]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (Nat.cast_nonneg _)

/-- The values of the empirical distribution function are the multiples of `1 / card κ`: scaled
by the sample size it counts the observations at most `t`. -/
theorem card_mul_empiricalCdf (x : κ → ℝ) (t : ℝ) :
    (Fintype.card κ : ℝ) * empiricalCdf x t = #{i | x i ≤ t} := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · rw [empiricalCdf_def, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero

/-- The empirical distribution function is monotone. -/
theorem monotone_empiricalCdf (x : κ → ℝ) : Monotone (empiricalCdf x) := by
  intro s t hst
  rw [empiricalCdf_def, empiricalCdf_def]
  gcongr

/-- The empirical distribution function vanishes exactly below every observation. -/
@[simp]
theorem empiricalCdf_eq_zero_iff {x : κ → ℝ} {t : ℝ} :
    empiricalCdf x t = 0 ↔ ∀ i, t < x i := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · simp [empiricalCdf_def, Fintype.card_ne_zero, filter_eq_empty_iff]

/-- The empirical distribution function of a nonempty sample is `1` exactly above every
observation. -/
@[simp]
theorem empiricalCdf_eq_one_iff [Nonempty κ] {x : κ → ℝ} {t : ℝ} :
    empiricalCdf x t = 1 ↔ ∀ i, x i ≤ t := by
  rw [empiricalCdf_def, div_eq_one_iff_eq (by exact_mod_cast Fintype.card_ne_zero), Nat.cast_inj,
    ← card_univ, card_filter_eq_iff]
  simp

/-- The empirical distribution function is invariant under reindexing the sample. -/
@[simp]
theorem empiricalCdf_comp_equiv (e : κ' ≃ κ) (x : κ → ℝ) :
    empiricalCdf (x ∘ e) = empiricalCdf x := by
  ext t
  rw [empiricalCdf_def, empiricalCdf_def, Fintype.card_congr e]
  congr 2
  exact card_equiv e (by simp)

/-- The empirical distribution function of a nonempty sample is the distribution function of its
empirical distribution. -/
theorem cdf_empiricalFiniteMeasure [Nonempty κ] (x : κ → ℝ) (t : ℝ) :
    cdf (empiricalFiniteMeasure x : Measure ℝ) t = empiricalCdf x t := by
  have hsum : ∑ i, (Iic t).indicator (1 : ℝ → ℝ≥0∞) (x i) = (#{i | x i ≤ t} : ℝ≥0∞) := by
    simp [indicator_apply]
  rw [cdf_eq_real, measureReal_def, Probability.empiricalFiniteMeasure_apply measurableSet_Iic,
    hsum, empiricalCdf_def]
  simp [div_eq_inv_mul]

/-- **Sequence form.** The empirical probability measure of the first `n + 1` terms of a real
sequence has as distribution function the empirical distribution function of those terms. -/
theorem cdf_empiricalMeasure (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    cdf (empiricalMeasure x n : Measure ℝ) t = empiricalCdf (fun i : Fin (n + 1) ↦ x i) t := by
  rw [← cdf_empiricalFiniteMeasure, Probability.empiricalMeasure_toMeasure,
    Probability.empiricalFiniteMeasure_toMeasure, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun i ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)) (n + 1)]

/-- **Sequence form.** The empirical distribution function of the first `n` terms of a real
sequence is `#{i < n | x i ≤ t} / n`. -/
theorem empiricalCdf_fin_eq_card_filter_range (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    empiricalCdf (fun i : Fin n ↦ x i) t = (#{i ∈ range n | x i ≤ t} : ℝ) / n := by
  rw [empiricalCdf_def, Fintype.card_fin, card_filter, card_filter,
    Fin.sum_univ_eq_sum_range (fun i ↦ if x i ≤ t then 1 else 0) n]

/-- The empirical distribution function is right continuous. -/
theorem continuousWithinAt_Ici_empiricalCdf (x : κ → ℝ) (t : ℝ) :
    ContinuousWithinAt (empiricalCdf x) (Ici t) t := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have h : empiricalCdf x = fun _ ↦ 0 := funext (empiricalCdf_of_isEmpty x)
    rw [h]
    exact continuousWithinAt_const
  · have h : empiricalCdf x = cdf (empiricalFiniteMeasure x : Measure ℝ) :=
      funext fun s ↦ (cdf_empiricalFiniteMeasure x s).symm
    rw [h]
    exact (cdf _).right_continuous t

/-- The empirical distribution function vanishes below the least observation. -/
theorem tendsto_empiricalCdf_atBot (x : κ → ℝ) : Tendsto (empiricalCdf x) atBot (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_all.2 fun i ↦ eventually_lt_atBot (x i)] with t ht
  exact (empiricalCdf_eq_zero_iff.2 ht).symm

/-- The empirical distribution function of a nonempty sample is `1` above the greatest
observation. -/
theorem tendsto_empiricalCdf_atTop [Nonempty κ] (x : κ → ℝ) :
    Tendsto (empiricalCdf x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_all.2 fun i ↦ eventually_ge_atTop (x i)] with t ht
  exact (empiricalCdf_eq_one_iff.2 ht).symm

/-- At each point, the empirical distribution function is a measurable function of the
sample. -/
@[fun_prop]
theorem measurable_empiricalCdf (t : ℝ) : Measurable fun x : κ → ℝ ↦ empiricalCdf x t := by
  have h : (fun x : κ → ℝ ↦ empiricalCdf x t) =
      fun x ↦ (∑ i, (Iic t).indicator (1 : ℝ → ℝ) (x i)) / Fintype.card κ := by
    ext x
    simp [empiricalCdf_def, indicator_apply]
  rw [h]
  exact (Finset.measurable_sum _ fun i _ ↦
    (measurable_const.indicator measurableSet_Iic).comp (measurable_pi_apply i)).div_const _

/-! ### The sample quantile -/

/-- The **sample quantile** of a finite real sample `x : κ → ℝ` at level `p`: the least point at
which the empirical distribution function reaches `p`.

It is the quantile function of the empirical distribution (`TauCeti.sampleQuantile_eq_quantile`),
and for a nonempty sample at levels `p ∈ (0, 1]` it is a sample point
(`TauCeti.sampleQuantile_mem_range`). At levels `p ≤ 0` and `1 < p`, and for an empty sample, the
defining infimum ranges over all of `ℝ` or over the empty set, and the value is the junk
value `0`. -/
def sampleQuantile (x : κ → ℝ) (p : ℝ) : ℝ :=
  sInf {t | p ≤ empiricalCdf x t}

/-- The sample quantile is the infimum of the points at which the empirical distribution function
reaches the level. The definition's body is not exposed, so this is the lemma downstream modules
rewrite with. -/
theorem sampleQuantile_def (x : κ → ℝ) (p : ℝ) :
    sampleQuantile x p = sInf {t | p ≤ empiricalCdf x t} := (rfl)

/-- At a nonpositive level the sample quantile takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_nonpos (x : κ → ℝ) {p : ℝ} (hp : p ≤ 0) : sampleQuantile x p = 0 := by
  have h : {t | p ≤ empiricalCdf x t} = univ :=
    eq_univ_of_forall fun t ↦ hp.trans (empiricalCdf_nonneg x t)
  rw [sampleQuantile_def, h, Real.sInf_univ]

/-- Above the level `1` the sample quantile takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_one_lt (x : κ → ℝ) {p : ℝ} (hp : 1 < p) : sampleQuantile x p = 0 := by
  have h : {t | p ≤ empiricalCdf x t} = ∅ := Set.eq_empty_of_forall_notMem
    fun t (ht : p ≤ empiricalCdf x t) ↦ (hp.trans_le (ht.trans (empiricalCdf_le_one x t))).false
  rw [sampleQuantile_def, h, Real.sInf_empty]

/-- The sample quantile of an empty sample takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_isEmpty [IsEmpty κ] (x : κ → ℝ) (p : ℝ) : sampleQuantile x p = 0 := by
  rcases le_or_gt p 0 with hp | hp
  · exact sampleQuantile_of_nonpos x hp
  · have h : {t | p ≤ empiricalCdf x t} = ∅ := Set.eq_empty_of_forall_notMem
      fun t (ht : p ≤ empiricalCdf x t) ↦ (hp.trans_le (by simpa using ht)).false
    rw [sampleQuantile_def, h, Real.sInf_empty]

/-- The sample quantile is the quantile function of the empirical distribution. For an empty
sample both sides are the junk value `0`. -/
theorem sampleQuantile_eq_quantile (x : κ → ℝ) (p : ℝ) :
    sampleQuantile x p = (empiricalFiniteMeasure x : Measure ℝ).quantile p := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · simp only [sampleQuantile_def, Measure.quantile_def, cdf_empiricalFiniteMeasure]

/-- The sample quantile is invariant under reindexing the sample. -/
@[simp]
theorem sampleQuantile_comp_equiv (e : κ' ≃ κ) (x : κ → ℝ) :
    sampleQuantile (x ∘ e) = sampleQuantile x := by
  ext p
  rw [sampleQuantile_def, sampleQuantile_def, empiricalCdf_comp_equiv]

/-- At a level `p ∈ (0, 1]`, the points at which the empirical distribution function of a
nonempty sample reaches `p` form the closed ray above one of the observations. -/
private theorem exists_setOf_le_empiricalCdf_eq_Ici [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : ∃ i, {t | p ≤ empiricalCdf x t} = Ici (x i) := by
  -- Among the observations at which the level is reached (the greatest observation is one),
  -- take a least one, `x i₀`.
  have hS : ({i | p ≤ empiricalCdf x (x i)} : Finset κ).Nonempty := by
    obtain ⟨j, -, hj⟩ := exists_max_image univ x univ_nonempty
    exact ⟨j, by simpa [empiricalCdf_eq_one_iff.2 fun i ↦ hj i (mem_univ i)] using hp1⟩
  obtain ⟨i₀, hi₀, hmin⟩ := exists_min_image _ x hS
  refine ⟨i₀, Set.ext fun t ↦ ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩⟩
  · -- The greatest observation `x j ≤ t` has the same empirical distribution function value as
    -- `t`, so the level is reached at `x j`, whence `x i₀ ≤ x j ≤ t`.
    have hT : ({i | x i ≤ t} : Finset κ).Nonempty := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≤ t := by
        by_contra! h
        exact (hp0.trans_le ht).ne' (empiricalCdf_eq_zero_iff.2 h)
      exact ⟨j, mem_filter.2 ⟨mem_univ j, hj⟩⟩
    obtain ⟨j, hj, hmax⟩ := exists_max_image _ x hT
    have hjt : x j ≤ t := (mem_filter.1 hj).2
    have heq : empiricalCdf x (x j) = empiricalCdf x t := by
      rw [empiricalCdf_def, empiricalCdf_def]
      congr 3
      exact filter_congr fun i _ ↦
        ⟨fun h ↦ h.trans hjt, fun h ↦ hmax i (mem_filter.2 ⟨mem_univ i, h⟩)⟩
    exact (hmin j (mem_filter.2 ⟨mem_univ j, heq ▸ ht⟩)).trans hjt
  · exact (mem_filter.1 hi₀).2.trans (monotone_empiricalCdf x ht)

/-- **The Galois inequality.** For a nonempty sample and a level `p ∈ (0, 1]`, the sample
`p`-quantile is at most `t` exactly when the empirical distribution function reaches `p` at `t`.
Unlike `MeasureTheory.Measure.quantile_le_iff` for an arbitrary law, this includes the endpoint
level `p = 1`. -/
@[simp]
theorem sampleQuantile_le_iff [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} : sampleQuantile x p ≤ t ↔ p ≤ empiricalCdf x t := by
  obtain ⟨i, hi⟩ := exists_setOf_le_empiricalCdf_eq_Ici x hp0 hp1
  rw [sampleQuantile_def, hi, csInf_Ici, ← Set.mem_Ici, ← hi, Set.mem_ofPred_eq]

/-- The set-level form of the Galois inequality `TauCeti.sampleQuantile_le_iff`: at a level
`p ∈ (0, 1]`, the empirical distribution function of a nonempty sample reaches `p` exactly on the
closed ray above the sample quantile. -/
theorem setOf_le_empiricalCdf_eq_Ici [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : {t | p ≤ empiricalCdf x t} = Ici (sampleQuantile x p) :=
  Set.ext fun _ ↦ (sampleQuantile_le_iff x hp0 hp1).symm

/-- The negation of the Galois inequality `TauCeti.sampleQuantile_le_iff`. -/
@[simp]
theorem lt_sampleQuantile_iff [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} : t < sampleQuantile x p ↔ empiricalCdf x t < p := by
  simpa only [not_le] using (sampleQuantile_le_iff x hp0 hp1 (t := t)).not

/-- The empirical distribution function of a nonempty sample reaches the level at the sample
quantile, at every level `p ≤ 1`. -/
theorem le_empiricalCdf_sampleQuantile [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp1 : p ≤ 1) :
    p ≤ empiricalCdf x (sampleQuantile x p) := by
  rcases le_or_gt p 0 with hp0 | hp0
  · exact hp0.trans (empiricalCdf_nonneg x _)
  · exact (sampleQuantile_le_iff x hp0 hp1).1 le_rfl

/-- At a level `p ∈ (0, 1]` the sample quantile of a nonempty sample is one of the
observations. -/
theorem sampleQuantile_mem_range [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    sampleQuantile x p ∈ range x := by
  obtain ⟨i, hi⟩ := exists_setOf_le_empiricalCdf_eq_Ici x hp0 hp1
  exact ⟨i, by rw [sampleQuantile_def, hi, csInf_Ici]⟩

/-- **The sample quantile is an order statistic.** For `n` observations and a level `p > 0`, the
sample `p`-quantile is the order statistic in position `⌈n p⌉ - 1` (counted from `0`). That this
position is below `n` forces `p ≤ 1`. -/
theorem sampleQuantile_eq_orderStatistic {n : ℕ} (x : Fin n → ℝ) {p : ℝ} (hp : 0 < p)
    (k : Fin n) (hk : (k : ℕ) = ⌈n * p⌉₊ - 1) : sampleQuantile x p = orderStatistic k x := by
  have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
  have hceil : 0 < ⌈n * p⌉₊ := Nat.ceil_pos.2 (mul_pos hn hp)
  have hp1 : p ≤ 1 := by
    have h : (n : ℝ) * p ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈n * p⌉₊ ≤ n))
    exact (mul_le_iff_le_one_right hn).1 h
  have : Nonempty (Fin n) := ⟨k⟩
  refine eq_of_forall_ge_iff fun t ↦ ?_
  rw [sampleQuantile_le_iff x hp hp1, orderStatistic_le_iff, empiricalCdf_def, Fintype.card_fin,
    le_div_iff₀ hn, mul_comm, ← Nat.ceil_le, hk]
  omega

/-- At each level, the sample quantile is a measurable function of the sample. -/
@[fun_prop]
theorem measurable_sampleQuantile (p : ℝ) : Measurable fun x : κ → ℝ ↦ sampleQuantile x p := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  rcases le_or_gt p 0 with hp0 | hp0
  · simp [sampleQuantile_of_nonpos _ hp0]
  rcases le_or_gt p 1 with hp1 | hp1
  · refine measurable_of_Iic fun t ↦ ?_
    have h : (fun x : κ → ℝ ↦ sampleQuantile x p) ⁻¹' Iic t = {x | p ≤ empiricalCdf x t} :=
      Set.ext fun x ↦ sampleQuantile_le_iff x hp0 hp1
    rw [h]
    exact measurableSet_le measurable_const (measurable_empiricalCdf t)
  · simp [sampleQuantile_of_one_lt _ hp1]

end TauCeti
