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
observations at most `t`, the mass that the empirical distribution
`TauCeti.Probability.empiricalFiniteMeasure x` gives to `Iic t`,

`empiricalCdf x t = #{i | x i ≤ t} / card κ`,

and the *sample quantile* at level `p` is the quantile function of the empirical distribution, the
left generalized inverse

`sampleQuantile x p = sInf {t | p ≤ empiricalCdf x t}`.

For a nonempty sample these are the distribution function and the quantile function of the
empirical distribution, so the general theory of `ProbabilityTheory.cdf` and
`MeasureTheory.Measure.quantile` applies to them; for an empty sample both are the junk value `0`.
The statements below are what is specific to a finite sample. The empirical distribution function
takes the values `k / card κ` and vanishes below every observation; for a nonempty sample it is
equal to `1` above every observation. For a nonempty sample and a level `p ∈ (0, 1]`, the sample
quantile is a sample point, namely an explicit order statistic, and the Galois inequality
`sampleQuantile x p ≤ t ↔ p ≤ empiricalCdf x t` holds, at the endpoint level `p = 1` as well,
which is not the case for an arbitrary law on `ℝ`.

These are the objects through which asymptotic statements about empirical processes and sample
quantiles (Glivenko–Cantelli, Donsker, the Bahadur representation) are formulated: a statistic
of an i.i.d. sample of size `n` is a function of `x : Fin n → ℝ`, and the sequence form, the first
`n` observations of `x : ℕ → ℝ`, is `fun i : Fin n ↦ x i`.

## Main definitions

* `TauCeti.empiricalCdf` — the empirical distribution function of a finite sample;
* `TauCeti.sampleQuantile` — the sample quantile, the left generalized inverse of
  `TauCeti.empiricalCdf`.

## Main statements

* `TauCeti.empiricalCdf_eq_card_filter_div` and `TauCeti.sampleQuantile_eq_sInf` — the defining
  formulas of the empirical distribution function and the sample quantile;
* `TauCeti.cdf_empiricalFiniteMeasure` — for a nonempty sample, the empirical distribution
  function is the distribution function of the empirical distribution;
* `TauCeti.cdf_empiricalMeasure` and `TauCeti.empiricalCdf_fin_eq_card_filter_range_div` — the
  sequence forms;
* `TauCeti.monotone_empiricalCdf`, `TauCeti.continuousWithinAt_Ici_empiricalCdf`,
  `TauCeti.tendsto_empiricalCdf_atBot` and `TauCeti.tendsto_empiricalCdf_atTop` — the empirical
  distribution function of a nonempty sample is a distribution function;
* `TauCeti.sampleQuantile_le_iff` — the Galois inequality for a nonempty sample at every level
  `p ∈ (0, 1]`, and `TauCeti.monotoneOn_sampleQuantile` — monotonicity on `(0, 1]`;
* `TauCeti.sampleQuantile_mem_range` and `TauCeti.sampleQuantile_eq_orderStatistic` — for a
  nonempty sample and `p ∈ (0, 1]`, the sample `p`-quantile of `n` observations is the order
  statistic in position `⌈n p⌉ - 1`;
* `TauCeti.measurable_uncurry_empiricalCdf` and `TauCeti.measurable_uncurry_sampleQuantile` —
  joint measurability in the sample and the point or level.

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

/-- The **empirical distribution function** of a finite real sample `x : κ → ℝ`: the mass
`F̂(t)` that the empirical distribution `TauCeti.Probability.empiricalFiniteMeasure x` gives to
`Iic t`, that is the proportion `#{i | x i ≤ t} / card κ` of observations at most `t`, counted
with multiplicity (`TauCeti.empiricalCdf_eq_card_filter_div`).

For a nonempty sample it is the distribution function of the empirical distribution
(`TauCeti.cdf_empiricalFiniteMeasure`). For an empty sample it is the junk value `0`, whereas
Mathlib's `ProbabilityTheory.cdf` of the zero measure is a genuine distribution function. -/
def empiricalCdf (x : κ → ℝ) (t : ℝ) : ℝ :=
  (empiricalFiniteMeasure x : Measure ℝ).real (Iic t)

/-- The empirical distribution function is the mass of `Iic t` under the empirical distribution.
The definition's body is not exposed, so this is the lemma downstream modules rewrite with. -/
theorem empiricalCdf_def (x : κ → ℝ) (t : ℝ) :
    empiricalCdf x t = (empiricalFiniteMeasure x : Measure ℝ).real (Iic t) := (rfl)

/-- The empirical distribution function is the proportion of observations at most `t`. -/
theorem empiricalCdf_eq_card_filter_div (x : κ → ℝ) (t : ℝ) :
    empiricalCdf x t = (#{i | x i ≤ t} : ℝ) / Fintype.card κ := by
  have hsum : ∑ i, (Iic t).indicator (1 : ℝ → ℝ≥0∞) (x i) = (#{i | x i ≤ t} : ℝ≥0∞) := by
    simp [indicator_apply]
  rw [empiricalCdf_def, measureReal_def, Probability.empiricalFiniteMeasure_apply measurableSet_Iic,
    hsum]
  simp [div_eq_inv_mul]

/-- The empirical distribution function of an empty sample is the junk value `0`. -/
@[simp]
theorem empiricalCdf_of_isEmpty [IsEmpty κ] (x : κ → ℝ) (t : ℝ) : empiricalCdf x t = 0 := by
  simp [empiricalCdf_def]

/-- The empirical distribution function is nonnegative. -/
theorem empiricalCdf_nonneg (x : κ → ℝ) (t : ℝ) : 0 ≤ empiricalCdf x t :=
  measureReal_nonneg

/-- The empirical distribution function is at most `1`. -/
theorem empiricalCdf_le_one (x : κ → ℝ) (t : ℝ) : empiricalCdf x t ≤ 1 := by
  rw [empiricalCdf_eq_card_filter_div]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (Nat.cast_nonneg _)

/-- The values of the empirical distribution function are the multiples of `1 / card κ`: scaled
by the sample size it counts the observations at most `t`. -/
theorem card_mul_empiricalCdf (x : κ → ℝ) (t : ℝ) :
    (Fintype.card κ : ℝ) * empiricalCdf x t = #{i | x i ≤ t} := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · rw [empiricalCdf_eq_card_filter_div, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero

/-- The empirical distribution function is monotone. -/
theorem monotone_empiricalCdf (x : κ → ℝ) : Monotone (empiricalCdf x) := by
  intro s t hst
  rw [empiricalCdf_eq_card_filter_div, empiricalCdf_eq_card_filter_div]
  gcongr

/-- The empirical distribution function vanishes exactly below every observation. -/
@[simp]
theorem empiricalCdf_eq_zero_iff {x : κ → ℝ} {t : ℝ} :
    empiricalCdf x t = 0 ↔ ∀ i, t < x i := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · simp [empiricalCdf_eq_card_filter_div, Fintype.card_ne_zero, filter_eq_empty_iff]

/-- The empirical distribution function of a nonempty sample is `1` exactly above every
observation. -/
@[simp]
theorem empiricalCdf_eq_one_iff [Nonempty κ] {x : κ → ℝ} {t : ℝ} :
    empiricalCdf x t = 1 ↔ ∀ i, x i ≤ t := by
  rw [empiricalCdf_eq_card_filter_div,
    div_eq_one_iff_eq (by exact_mod_cast Fintype.card_ne_zero), Nat.cast_inj, ← card_univ,
    card_filter_eq_iff]
  simp

/-- The empirical distribution function is invariant under reindexing the sample. -/
@[simp]
theorem empiricalCdf_comp_equiv (e : κ' ≃ κ) (x : κ → ℝ) :
    empiricalCdf (x ∘ e) = empiricalCdf x := by
  ext t
  rw [empiricalCdf_def, empiricalCdf_def, Probability.empiricalFiniteMeasure_comp_equiv]

/-- The empirical distribution function of a nonempty sample is the distribution function of its
empirical distribution. -/
theorem cdf_empiricalFiniteMeasure [Nonempty κ] (x : κ → ℝ) (t : ℝ) :
    cdf (empiricalFiniteMeasure x : Measure ℝ) t = empiricalCdf x t := by
  rw [cdf_eq_real, empiricalCdf_def]

/-- **Sequence form.** The empirical probability measure of the first `n + 1` terms of a real
sequence has as distribution function the empirical distribution function of those terms. -/
theorem cdf_empiricalMeasure (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    cdf (empiricalMeasure x n : Measure ℝ) t = empiricalCdf (fun i : Fin (n + 1) ↦ x i) t := by
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    Probability.toFiniteMeasure_empiricalMeasure, cdf_empiricalFiniteMeasure]

/-- **Sequence form.** The empirical distribution function of the first `n` terms of a real
sequence is `#{i < n | x i ≤ t} / n`. -/
theorem empiricalCdf_fin_eq_card_filter_range_div (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    empiricalCdf (fun i : Fin n ↦ x i) t = (#{i ∈ range n | x i ≤ t} : ℝ) / n := by
  rw [empiricalCdf_eq_card_filter_div, Fintype.card_fin, card_filter, card_filter,
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

/-- The empirical distribution function is jointly measurable in the sample and the point. -/
@[fun_prop]
theorem measurable_uncurry_empiricalCdf :
    Measurable (Function.uncurry (empiricalCdf : (κ → ℝ) → ℝ → ℝ)) := by
  have h : Function.uncurry (empiricalCdf : (κ → ℝ) → ℝ → ℝ) =
      fun q ↦ (∑ i, {q : (κ → ℝ) × ℝ | q.1 i ≤ q.2}.indicator (1 : (κ → ℝ) × ℝ → ℝ) q) /
        Fintype.card κ := by
    ext ⟨x, t⟩
    simp [empiricalCdf_eq_card_filter_div, indicator_apply]
  rw [h]
  exact (Finset.measurable_sum _ fun i _ ↦ measurable_const.indicator
    (measurableSet_le ((measurable_pi_apply i).comp measurable_fst) measurable_snd)).div_const _

/-- At each point, the empirical distribution function is a measurable function of the
sample. -/
@[fun_prop]
theorem measurable_empiricalCdf (t : ℝ) : Measurable fun x : κ → ℝ ↦ empiricalCdf x t :=
  measurable_uncurry_empiricalCdf.comp (measurable_id.prodMk measurable_const)

/-! ### The sample quantile -/

/-- The **sample quantile** of a finite real sample `x : κ → ℝ` at level `p`: the quantile
function of the empirical distribution `TauCeti.Probability.empiricalFiniteMeasure x`, that is the
infimum `sInf {t | p ≤ empiricalCdf x t}` of the points at which the empirical distribution
function reaches `p` (`TauCeti.sampleQuantile_eq_sInf`).

For a nonempty sample at levels `p ∈ (0, 1]` this infimum is attained, so the sample quantile is
the least such point, and it is a sample point (`TauCeti.sampleQuantile_mem_range`). At levels
`p ≤ 0` and `1 < p`, and for an empty sample, the defining infimum ranges over all of `ℝ` or over
the empty set, and the value is the junk value `0`. -/
def sampleQuantile (x : κ → ℝ) (p : ℝ) : ℝ :=
  (empiricalFiniteMeasure x : Measure ℝ).quantile p

/-- The sample quantile is the quantile function of the empirical distribution. The definition's
body is not exposed, so this is the lemma downstream modules rewrite with. -/
theorem sampleQuantile_eq_quantile (x : κ → ℝ) (p : ℝ) :
    sampleQuantile x p = (empiricalFiniteMeasure x : Measure ℝ).quantile p := (rfl)

/-- At a nonpositive level the sample quantile takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_nonpos (x : κ → ℝ) {p : ℝ} (hp : p ≤ 0) : sampleQuantile x p = 0 :=
  Measure.quantile_of_nonpos _ hp

/-- Above the level `1` the sample quantile takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_one_lt (x : κ → ℝ) {p : ℝ} (hp : 1 < p) : sampleQuantile x p = 0 :=
  Measure.quantile_of_one_lt _ hp

/-- The sample quantile of an empty sample takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_isEmpty [IsEmpty κ] (x : κ → ℝ) (p : ℝ) : sampleQuantile x p = 0 := by
  simp [sampleQuantile_eq_quantile]

/-- The sample quantile is the infimum of the points at which the empirical distribution function
reaches the level. For an empty sample both sides are the junk value `0`. -/
theorem sampleQuantile_eq_sInf (x : κ → ℝ) (p : ℝ) :
    sampleQuantile x p = sInf {t | p ≤ empiricalCdf x t} := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rcases le_or_gt p 0 with hp | hp
    · simp [hp]
    · simp [not_le.2 hp]
  · simp only [sampleQuantile_eq_quantile, Measure.quantile_def, cdf_empiricalFiniteMeasure]

/-- The sample quantile is invariant under reindexing the sample. -/
@[simp]
theorem sampleQuantile_comp_equiv (e : κ' ≃ κ) (x : κ → ℝ) :
    sampleQuantile (x ∘ e) = sampleQuantile x := by
  ext p
  rw [sampleQuantile_eq_quantile, sampleQuantile_eq_quantile,
    Probability.empiricalFiniteMeasure_comp_equiv]

/-- For `n` observations and a level `p > 0`, the points at which the empirical distribution
function reaches `p` form the closed ray above the order statistic in position `⌈n p⌉ - 1`. -/
private theorem setOf_le_empiricalCdf_eq_Ici_orderStatistic {n : ℕ} (x : Fin n → ℝ) {p : ℝ}
    (hp : 0 < p) (k : Fin n) (hk : (k : ℕ) = ⌈n * p⌉₊ - 1) :
    {t | p ≤ empiricalCdf x t} = Ici (orderStatistic k x) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
  have hceil : 0 < ⌈n * p⌉₊ := Nat.ceil_pos.2 (mul_pos hn hp)
  ext t
  rw [Set.mem_ofPred_eq, Set.mem_Ici, orderStatistic_le_iff, empiricalCdf_eq_card_filter_div,
    Fintype.card_fin, le_div_iff₀ hn, mul_comm, ← Nat.ceil_le, hk]
  omega

/-- At a level `p ∈ (0, 1]`, the points at which the empirical distribution function of a
nonempty sample reaches `p` form the closed ray above one of the observations: after listing the
sample along `Fintype.equivFin κ`, the order statistic in position `⌈(card κ) p⌉ - 1`. -/
private theorem exists_setOf_le_empiricalCdf_eq_Ici [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : ∃ i, {t | p ≤ empiricalCdf x t} = Ici (x i) := by
  set e := Fintype.equivFin κ
  have hk : ⌈Fintype.card κ * p⌉₊ - 1 < Fintype.card κ :=
    Nat.sub_one_lt_of_le (Nat.ceil_pos.2 (mul_pos (by exact_mod_cast Fintype.card_pos) hp0))
      (Nat.ceil_le.2 (mul_le_of_le_one_right (Nat.cast_nonneg _) hp1))
  refine ⟨e.symm (Tuple.sort (x ∘ e.symm) ⟨_, hk⟩), ?_⟩
  rw [← empiricalCdf_comp_equiv e.symm x,
    setOf_le_empiricalCdf_eq_Ici_orderStatistic (x ∘ e.symm) hp0 ⟨_, hk⟩ rfl, orderStatistic_def,
    Function.comp_apply]

/-- **The Galois inequality.** For a nonempty sample and a level `p ∈ (0, 1]`, the sample
`p`-quantile is at most `t` exactly when the empirical distribution function reaches `p` at `t`.
Unlike `MeasureTheory.Measure.quantile_le_iff` for an arbitrary law, this includes the endpoint
level `p = 1`. -/
@[simp]
theorem sampleQuantile_le_iff [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} : sampleQuantile x p ≤ t ↔ p ≤ empiricalCdf x t := by
  obtain ⟨i, hi⟩ := exists_setOf_le_empiricalCdf_eq_Ici x hp0 hp1
  rw [sampleQuantile_eq_sInf, hi, csInf_Ici, ← Set.mem_Ici, ← hi, Set.mem_ofPred_eq]

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

/-- The sample quantile is monotone in the level on `(0, 1]`, the endpoint level `1` included.
`MeasureTheory.Measure.monotoneOn_quantile` for an arbitrary law only covers `(0, 1)`. -/
theorem monotoneOn_sampleQuantile (x : κ → ℝ) : MonotoneOn (sampleQuantile x) (Ioc 0 1) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · intro p _ q _ _
    simp
  · intro p hp q hq hpq
    exact (sampleQuantile_le_iff x hp.1 hp.2).2 (hpq.trans (le_empiricalCdf_sampleQuantile x hq.2))

/-- At a level `p ∈ (0, 1]` the sample quantile of a nonempty sample is one of the
observations. -/
theorem sampleQuantile_mem_range [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    sampleQuantile x p ∈ range x := by
  obtain ⟨i, hi⟩ := exists_setOf_le_empiricalCdf_eq_Ici x hp0 hp1
  exact ⟨i, by rw [sampleQuantile_eq_sInf, hi, csInf_Ici]⟩

/-- **The sample quantile is an order statistic.** For `n > 0` observations and a level
`p ∈ (0, 1]`, the sample `p`-quantile is the order statistic in position `⌈n p⌉ - 1` (counted
from `0`). -/
theorem sampleQuantile_eq_orderStatistic {n : ℕ} [NeZero n] (x : Fin n → ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    sampleQuantile x p = orderStatistic ⟨⌈n * p⌉₊ - 1,
      Nat.sub_one_lt_of_le (Nat.ceil_pos.2 (mul_pos (Nat.cast_pos.2 (NeZero.pos n)) hp0))
        (Nat.ceil_le.2 (mul_le_of_le_one_right (Nat.cast_nonneg n) hp1))⟩ x := by
  exact (sampleQuantile_eq_sInf x p).trans
    ((congrArg sInf (setOf_le_empiricalCdf_eq_Ici_orderStatistic x hp0 _ (by rfl))).trans csInf_Ici)

/-- The sample quantile is jointly measurable in the sample and the level. -/
@[fun_prop]
theorem measurable_uncurry_sampleQuantile :
    Measurable (Function.uncurry (sampleQuantile : (κ → ℝ) → ℝ → ℝ)) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have h : Function.uncurry (sampleQuantile : (κ → ℝ) → ℝ → ℝ) = fun _ ↦ 0 := by
      ext ⟨x, p⟩
      simp
    rw [h]
    exact measurable_const
  refine measurable_of_Iic fun t ↦ ?_
  have h : Function.uncurry (sampleQuantile : (κ → ℝ) → ℝ → ℝ) ⁻¹' Iic t =
      {q : (κ → ℝ) × ℝ | q.2 ∈ Set.Ioc 0 1 ∧ q.2 ≤ empiricalCdf q.1 t} ∪
        {q | q.2 ∉ Set.Ioc 0 1 ∧ 0 ≤ t} := by
    ext ⟨x, p⟩
    by_cases hp : p ∈ Set.Ioc 0 1
    · simp only [Set.mem_preimage, Function.uncurry_apply_pair, Set.mem_Iic, Set.mem_union,
        Set.mem_ofPred_eq, hp, true_and, not_true_eq_false, false_and, or_false,
        sampleQuantile_le_iff x hp.1 hp.2]
    · have h0 : sampleQuantile x p = 0 := by
        rcases le_or_gt p 0 with hp0 | hp0
        · exact sampleQuantile_of_nonpos x hp0
        · exact sampleQuantile_of_one_lt x (lt_of_not_ge fun hp1 ↦ hp ⟨hp0, hp1⟩)
      simp only [Set.mem_preimage, Function.uncurry_apply_pair, Set.mem_Iic, Set.mem_union,
        Set.mem_ofPred_eq, hp, false_and, not_false_eq_true, true_and, false_or, h0]
  have hI : MeasurableSet {q : (κ → ℝ) × ℝ | q.2 ∈ Set.Ioc 0 1} :=
    measurable_snd measurableSet_Ioc
  rw [h]
  exact (hI.inter (measurableSet_le measurable_snd ((measurable_empiricalCdf t).comp
    measurable_fst))).union (hI.compl.inter (MeasurableSet.const _))

/-- At each level, the sample quantile is a measurable function of the sample. -/
@[fun_prop]
theorem measurable_sampleQuantile (p : ℝ) : Measurable fun x : κ → ℝ ↦ sampleQuantile x p :=
  measurable_uncurry_sampleQuantile.comp (measurable_id.prodMk measurable_const)

end TauCeti
