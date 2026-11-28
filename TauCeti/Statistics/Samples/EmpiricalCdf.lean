/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.Probability.Process.EmpiricalMeasure
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Quantile.Finite

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
takes its values in the grid `{k / card κ}` and vanishes below every observation; for a nonempty
sample it is equal to `1` above every observation. For a nonempty sample and a level
`p ∈ (0, 1]`, the sample quantile is a sample point, namely an explicit order statistic, and the
Galois inequality `sampleQuantile x p ≤ t ↔ p ≤ empiricalCdf x t` holds, at the endpoint level
`p = 1` as well, which is not the case for an arbitrary law on `ℝ`.

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
* `TauCeti.cdf_empiricalMeasure`, `TauCeti.cdf_empiricalMeasure_sub_one` and
  `TauCeti.empiricalCdf_fin_eq_card_filter_range_div` — the sequence forms;
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
  rw [empiricalCdf_def, measureReal_def,
    Probability.empiricalFiniteMeasure_apply_eq_card_filter measurableSet_Iic]
  simp [div_eq_inv_mul]

/-- The empirical distribution function of an empty sample is the junk value `0`. -/
@[simp]
theorem empiricalCdf_of_isEmpty [IsEmpty κ] (x : κ → ℝ) (t : ℝ) : empiricalCdf x t = 0 := by
  simp [empiricalCdf_def]

/-- The empirical distribution function is nonnegative. -/
theorem empiricalCdf_nonneg (x : κ → ℝ) (t : ℝ) : 0 ≤ empiricalCdf x t := by
  rw [empiricalCdf_def]
  exact measureReal_nonneg

/-- The empirical distribution function is at most `1`. -/
theorem empiricalCdf_le_one (x : κ → ℝ) (t : ℝ) : empiricalCdf x t ≤ 1 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · rw [empiricalCdf_def]
    exact measureReal_le_one

/-- Scaled by the sample size, the empirical distribution function counts the observations at
most `t`: its value at `t` is `k / card κ`, where `k` is the number of observations at most `t`. -/
theorem card_mul_empiricalCdf (x : κ → ℝ) (t : ℝ) :
    (Fintype.card κ : ℝ) * empiricalCdf x t = #{i | x i ≤ t} := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · rw [empiricalCdf_eq_card_filter_div, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero

/-- The empirical distribution function is monotone. -/
theorem monotone_empiricalCdf (x : κ → ℝ) : Monotone (empiricalCdf x) := by
  intro s t hst
  rw [empiricalCdf_def, empiricalCdf_def]
  exact measureReal_mono (Iic_subset_Iic.2 hst)

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
  have hcount : #{i | x i ≤ t} = Fintype.card κ ↔ ∀ i, x i ≤ t := by
    rw [← card_univ, card_filter_eq_iff]
    simp
  rw [empiricalCdf_eq_card_filter_div,
    div_eq_one_iff_eq (by exact_mod_cast Fintype.card_ne_zero), Nat.cast_inj, hcount]

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

/-- The function form of `TauCeti.cdf_empiricalFiniteMeasure`, through which the empirical
distribution function of a nonempty sample inherits the properties of `ProbabilityTheory.cdf`. -/
private theorem empiricalCdf_eq_cdf [Nonempty κ] (x : κ → ℝ) :
    empiricalCdf x = cdf (empiricalFiniteMeasure x : Measure ℝ) :=
  funext fun t ↦ (cdf_empiricalFiniteMeasure x t).symm

/-- **Sequence form.** The empirical probability measure of the first `n + 1` terms of a real
sequence has as distribution function the empirical distribution function of those terms. -/
theorem cdf_empiricalMeasure (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    cdf (empiricalMeasure x n : Measure ℝ) t = empiricalCdf (fun i : Fin (n + 1) ↦ x i) t := by
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    Probability.toFiniteMeasure_empiricalMeasure, cdf_empiricalFiniteMeasure]

/-- **Sequence form, indexed by the sample size.** For `n > 0`, the empirical probability measure
`empiricalMeasure x (n - 1)` of the first `n` terms of a real sequence has as distribution function
the empirical distribution function of those terms. -/
theorem cdf_empiricalMeasure_sub_one (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    cdf (empiricalMeasure x (n - 1) : Measure ℝ) t = empiricalCdf (fun i : Fin n ↦ x i) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact cdf_empiricalMeasure x m t

/-- **Sequence form.** The empirical distribution function of the first `n` terms of a real
sequence is `#{i < n | x i ≤ t} / n`. -/
theorem empiricalCdf_fin_eq_card_filter_range_div (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    empiricalCdf (fun i : Fin n ↦ x i) t = (#{i ∈ range n | x i ≤ t} : ℝ) / n := by
  have hcount : #{i : Fin n | x i ≤ t} = #{i ∈ range n | x i ≤ t} := by
    simp only [card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ if x i ≤ t then 1 else 0) n
  rw [empiricalCdf_eq_card_filter_div, Fintype.card_fin, hcount]

/-- The empirical distribution function is right continuous. -/
theorem continuousWithinAt_Ici_empiricalCdf (x : κ → ℝ) (t : ℝ) :
    ContinuousWithinAt (empiricalCdf x) (Ici t) t := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have h : empiricalCdf x = fun _ ↦ 0 := funext (empiricalCdf_of_isEmpty x)
    rw [h]
    exact continuousWithinAt_const
  · rw [empiricalCdf_eq_cdf]
    exact (cdf _).right_continuous t

/-- The empirical distribution function of any sample tends to `0` at `-∞`. -/
theorem tendsto_empiricalCdf_atBot (x : κ → ℝ) : Tendsto (empiricalCdf x) atBot (𝓝 0) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have h : empiricalCdf x = fun _ ↦ 0 := funext (empiricalCdf_of_isEmpty x)
    rw [h]
    exact tendsto_const_nhds
  · rw [empiricalCdf_eq_cdf]
    exact tendsto_cdf_atBot _

/-- The empirical distribution function of a nonempty sample tends to `1` at `+∞`. -/
theorem tendsto_empiricalCdf_atTop [Nonempty κ] (x : κ → ℝ) :
    Tendsto (empiricalCdf x) atTop (𝓝 1) := by
  rw [empiricalCdf_eq_cdf]
  exact tendsto_cdf_atTop _

/-- The empirical distribution function is jointly measurable in the sample and the point. -/
@[fun_prop]
theorem measurable_uncurry_empiricalCdf :
    Measurable (Function.uncurry (empiricalCdf : (κ → ℝ) → ℝ → ℝ)) := by
  -- This is the mass of `Iic t` under the empirical distribution, measurable in the sample.
  have h : Function.uncurry (empiricalCdf : (κ → ℝ) → ℝ → ℝ) =
      Function.uncurry (fun (μ : FiniteMeasure ℝ) (t : ℝ) ↦ (μ : Measure ℝ).real (Iic t)) ∘
        Prod.map empiricalFiniteMeasure id := by
    ext ⟨x, t⟩
    rw [Function.comp_apply, Prod.map_apply, Function.uncurry_apply_pair,
      Function.uncurry_apply_pair, empiricalCdf_def, id]
  rw [h]
  exact FiniteMeasure.measurable_uncurry_measureReal_Iic.comp
    (Probability.measurable_empiricalFiniteMeasure.prodMap measurable_id)

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
`p ≤ 0` and `1 < p` the value is the junk value `0` of `MeasureTheory.Measure.quantile`. For an
empty sample the empirical distribution is the zero measure, whose quantile is the junk value `0`
at every level (`MeasureTheory.Measure.quantile_zero`), even though the cumulative distribution
function of the zero measure reaches every level `p ∈ (0, 1]` exactly on `Ici 0`. In the formula
of `TauCeti.sampleQuantile_eq_sInf` for an empty sample, the level set
`{t | p ≤ empiricalCdf x t}` is all of `ℝ` for `p ≤ 0` and empty otherwise, and its infimum is `0`
as well. -/
def sampleQuantile (x : κ → ℝ) (p : ℝ) : ℝ :=
  (empiricalFiniteMeasure x : Measure ℝ).quantile p

/-- The sample quantile is the quantile function of the empirical distribution. The definition's
body is not exposed, so this is the lemma downstream modules rewrite with. -/
theorem sampleQuantile_eq_quantile (x : κ → ℝ) (p : ℝ) :
    sampleQuantile x p = (empiricalFiniteMeasure x : Measure ℝ).quantile p := (rfl)

/-- At a nonpositive level the sample quantile takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_nonpos (x : κ → ℝ) {p : ℝ} (hp : p ≤ 0) : sampleQuantile x p = 0 := by
  rw [sampleQuantile_eq_quantile]
  exact Measure.quantile_of_nonpos _ hp

/-- Above the level `1` the sample quantile takes the junk value `0`. -/
@[simp]
theorem sampleQuantile_of_one_lt (x : κ → ℝ) {p : ℝ} (hp : 1 < p) : sampleQuantile x p = 0 := by
  rw [sampleQuantile_eq_quantile]
  exact Measure.quantile_of_one_lt _ hp

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
  have hpos : 0 < ⌈n * p⌉₊ := Nat.ceil_pos.2 (mul_pos hn hp)
  -- A count `m` of observations reaches the level `p` exactly when `⌈n p⌉ ≤ m`.
  have hceil (m : ℕ) : p ≤ (m : ℝ) / n ↔ ⌈n * p⌉₊ ≤ m := by
    rw [le_div_iff₀ hn, mul_comm, Nat.ceil_le]
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_Ici, orderStatistic_le_iff,
    empiricalCdf_eq_card_filter_div, Fintype.card_fin, hceil, hk]
  omega

/-- **The Galois inequality.** For a nonempty sample and a level `p ∈ (0, 1]`, the sample
`p`-quantile is at most `t` exactly when the empirical distribution function reaches `p` at `t`.
Unlike `MeasureTheory.Measure.quantile_le_iff` for an arbitrary law, this includes the endpoint
level `p = 1`: the empirical distribution is carried by the finite set of observations, so it
reaches every level `p ≤ 1` (`MeasureTheory.Measure.quantile_le_iff_of_nonempty`). -/
@[simp]
theorem sampleQuantile_le_iff [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} : sampleQuantile x p ≤ t ↔ p ≤ empiricalCdf x t := by
  rw [sampleQuantile_eq_quantile, ← cdf_empiricalFiniteMeasure,
    Measure.quantile_le_iff_of_nonempty _ hp0 (Measure.nonempty_setOf_le_cdf_of_ae_mem_finset _
      (Probability.ae_mem_image_empiricalFiniteMeasure x) hp1)]

/-- The set-level form of the Galois inequality `TauCeti.sampleQuantile_le_iff`: at a level
`p ∈ (0, 1]`, the empirical distribution function of a nonempty sample reaches `p` exactly on the
closed ray above the sample quantile. -/
theorem setOf_le_empiricalCdf_eq_Ici [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : {t | p ≤ empiricalCdf x t} = Ici (sampleQuantile x p) :=
  Set.ext fun _ ↦ (sampleQuantile_le_iff x hp0 hp1).symm

/-- The strict form of the Galois inequality `TauCeti.sampleQuantile_le_iff`: for a nonempty
sample and a level `p ∈ (0, 1]`, a point lies below the sample quantile exactly when the empirical
distribution function there is below `p`. -/
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
`MeasureTheory.Measure.monotoneOn_quantile` for an arbitrary law only covers `(0, 1)`; this is the
case of `MeasureTheory.Measure.monotoneOn_quantile_of_nonempty` for a law carried by a finite
set. -/
theorem monotoneOn_sampleQuantile (x : κ → ℝ) : MonotoneOn (sampleQuantile x) (Ioc 0 1) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · intro p _ q _ _
    simp
  · rw [funext (sampleQuantile_eq_quantile x)]
    exact (Measure.monotoneOn_quantile_of_nonempty _).mono fun p hp ↦
      ⟨hp.1, Measure.nonempty_setOf_le_cdf_of_ae_mem_finset _
        (Probability.ae_mem_image_empiricalFiniteMeasure x) hp.2⟩

/-- At a level `p ∈ (0, 1]` the sample quantile of a nonempty sample is one of the
observations. -/
theorem sampleQuantile_mem_range [Nonempty κ] (x : κ → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    sampleQuantile x p ∈ range x := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Measure.quantile_mem_finset _
    (Probability.ae_mem_image_empiricalFiniteMeasure x) ⟨hp0, hp1⟩)
  exact ⟨i, hi.trans (sampleQuantile_eq_quantile x p).symm⟩

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
  -- This is the quantile of the empirical probability measure, measurable in the sample.
  have h : Function.uncurry (sampleQuantile : (κ → ℝ) → ℝ → ℝ) =
      Function.uncurry (fun (P : ProbabilityMeasure ℝ) (p : ℝ) ↦ (P : Measure ℝ).quantile p) ∘
        Prod.map Probability.empiricalMeasureOfFintype id := by
    ext ⟨x, p⟩
    rw [Function.comp_apply, Prod.map_apply, Function.uncurry_apply_pair,
      Function.uncurry_apply_pair, sampleQuantile_eq_quantile,
      ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
      Probability.toFiniteMeasure_empiricalMeasureOfFintype, id]
  rw [h]
  exact Measure.measurable_uncurry_quantile_probabilityMeasure.comp
    (Probability.measurable_empiricalMeasureOfFintype.prodMap measurable_id)

/-- At each level, the sample quantile is a measurable function of the sample. -/
@[fun_prop]
theorem measurable_sampleQuantile (p : ℝ) : Measurable fun x : κ → ℝ ↦ sampleQuantile x p :=
  measurable_uncurry_sampleQuantile.comp (measurable_id.prodMk measurable_const)

end TauCeti
