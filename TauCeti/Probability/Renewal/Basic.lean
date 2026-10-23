/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Arrival times and counts of an ordinary renewal process

Let `T 0, T 1, …` be nonnegative increments, with `T i` the waiting time between the `i`-th and
the `(i + 1)`-st renewal. This file defines the arrival times and the counting process

```text
arrival T n = T 0 + ⋯ + T (n - 1),     renewalCount T t = #{n ≥ 1 | arrival T n ≤ t},
```

so that `arrival T 0 = 0` is the artificial arrival at time zero, which is not counted, while
genuine arrivals at time zero (zero increments) are counted with multiplicity. Time and increments
live in `ℝ≥0`. The count is extended-valued, `renewalCount T t ω : ℝ≥0∞`, so that it is defined and
measurable before one knows that it is finite.

The deterministic part of the file relates the two objects: `n ≤ renewalCount T t ω` exactly when
`arrival T n ω ≤ t`; the count equals `n` exactly when `arrival T n ω ≤ t < arrival T (n + 1) ω`;
it is infinite exactly when every arrival is at most `t`; it is nondecreasing and right-continuous
in `t`; and it is finite for every `t` exactly when the arrival times tend to infinity.

The probabilistic part shows that the process does not explode: if the increments are independent
and identically distributed and not almost surely zero, then almost surely the arrival times tend
to infinity, and hence almost surely `renewalCount T t` is finite simultaneously for all `t`. The
proof applies the second Borel–Cantelli lemma to the events `{a ≤ T n}` for a threshold `a > 0` of
positive probability. Finally, the law of each count depends only on the common law `F` of the
increments: it is the law of the count of the coordinate process under the product measure
`Measure.infinitePi (fun _ ↦ F)`, on which Mathlib's `iIndepFun_infinitePi` constructs the
increments.

## Main definitions

* `TauCeti.Probability.arrival` — the `n`-th arrival time `∑ i ∈ Finset.range n, T i`.
* `TauCeti.Probability.renewalCount` — the extended number of arrivals with index `n ≥ 1` in
  `[0, t]`.

## Main results

* `TauCeti.Probability.natCast_le_renewalCount_iff` — `n ≤ N t ↔ arrival n ≤ t`.
* `TauCeti.Probability.renewalCount_eq_natCast_iff` — `N t = n ↔ arrival n ≤ t < arrival (n + 1)`.
* `TauCeti.Probability.continuousWithinAt_renewalCount_Ici` — right continuity of the count.
* `TauCeti.Probability.tendsto_arrival_atTop_iff` — nonexplosion is finiteness of every count.
* `TauCeti.Probability.ae_tendsto_arrival_atTop`, `TauCeti.Probability.ae_renewalCount_lt_top` —
  i.i.d. increments that are not almost surely zero do not explode.
* `TauCeti.Probability.map_renewalCount_eq_infinitePi_map` — the law of a count is computed on the
  canonical product space.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} (T : ℕ → Ω → ℝ≥0)

/-! ### Arrival times -/

/-- The `n`-th arrival time `T 0 + ⋯ + T (n - 1)` of the renewal process with increments `T`.
The artificial arrival at time zero is `arrival T 0 = 0`. -/
def arrival (n : ℕ) (ω : Ω) : ℝ≥0 :=
  ∑ i ∈ Finset.range n, T i ω

lemma arrival_def (n : ℕ) (ω : Ω) : arrival T n ω = ∑ i ∈ Finset.range n, T i ω := (rfl)

@[simp]
lemma arrival_zero (ω : Ω) : arrival T 0 ω = 0 := by
  simp [arrival_def]

lemma arrival_succ (n : ℕ) (ω : Ω) : arrival T (n + 1) ω = arrival T n ω + T n ω := by
  simp [arrival_def, Finset.sum_range_succ]

/-- The arrival times are nondecreasing. -/
lemma monotone_arrival (ω : Ω) : Monotone fun n ↦ arrival T n ω :=
  monotone_nat_of_le_succ fun n ↦ by simp [arrival_succ]

@[fun_prop]
lemma measurable_arrival [MeasurableSpace Ω] {T : ℕ → Ω → ℝ≥0} (hT : ∀ n, Measurable (T n))
    (n : ℕ) : Measurable (arrival T n) := by
  simp only [funext (arrival_def T n)]
  exact Finset.measurable_fun_sum _ fun i _ ↦ hT i

/-! ### The counting process -/

/-- The number `#{n ≥ 1 | arrival T n ω ≤ t}` of arrivals in `[0, t]`, counted with multiplicity,
as an extended nonnegative number. The artificial arrival `arrival T 0 = 0` is not counted. -/
def renewalCount (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, if arrival T (n + 1) ω ≤ t then 1 else 0

lemma renewalCount_def (t : ℝ≥0) (ω : Ω) :
    renewalCount T t ω = ∑' n : ℕ, if arrival T (n + 1) ω ≤ t then 1 else 0 := (rfl)

@[fun_prop]
lemma measurable_renewalCount [MeasurableSpace Ω] {T : ℕ → Ω → ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (t : ℝ≥0) : Measurable (renewalCount T t) := by
  simp only [funext (renewalCount_def T t)]
  refine Measurable.tsum fun n ↦ Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (measurable_arrival hT _) measurable_const

variable {T}

/-- If `t < arrival T (n + 1) ω`, only the first `n` terms of the series defining the count can
be nonzero. -/
private lemma renewalCount_eq_sum_range {t : ℝ≥0} {ω : Ω} {n : ℕ}
    (h : t < arrival T (n + 1) ω) :
    renewalCount T t ω = ∑ k ∈ Finset.range n, if arrival T (k + 1) ω ≤ t then 1 else 0 := by
  rw [renewalCount_def]
  refine tsum_eq_sum fun k hk ↦ ite_eq_right (not_le.2 (h.trans_le (monotone_arrival T ω ?_)))
  simpa using hk

/-- At least `n` arrivals occur in `[0, t]` exactly when the `n`-th arrival time is at most `t`.
For `n = 0` both sides hold trivially. -/
@[simp]
lemma natCast_le_renewalCount_iff {t : ℝ≥0} {ω : Ω} {n : ℕ} :
    (n : ℝ≥0∞) ≤ renewalCount T t ω ↔ arrival T n ω ≤ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases n with _ | n
    · simp
    by_contra! ht
    have : renewalCount T t ω ≤ n := by
      rw [renewalCount_eq_sum_range ht]
      refine (Finset.sum_le_card_nsmul _ _ 1 fun k _ ↦ ?_).trans (by simp)
      split_ifs <;> simp
    exact absurd (h.trans this) (by rw [Nat.cast_le]; omega)
  · calc (n : ℝ≥0∞) = ∑ k ∈ Finset.range n, (1 : ℝ≥0∞) := by simp
      _ = ∑ k ∈ Finset.range n, if arrival T (k + 1) ω ≤ t then 1 else 0 :=
        Finset.sum_congr rfl fun k hk ↦
          (ite_eq_left <| (monotone_arrival T ω (Finset.mem_range.1 hk)).trans h).symm
      _ ≤ renewalCount T t ω := ENNReal.sum_le_tsum _

/-- The count at time `t` equals `n` exactly when `arrival T n ω ≤ t < arrival T (n + 1) ω`. -/
lemma renewalCount_eq_natCast_iff {t : ℝ≥0} {ω : Ω} {n : ℕ} :
    renewalCount T t ω = n ↔ arrival T n ω ≤ t ∧ t < arrival T (n + 1) ω := by
  refine ⟨fun h ↦ ⟨natCast_le_renewalCount_iff.1 h.ge, not_le.1 fun h' ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · have := natCast_le_renewalCount_iff.2 h'
    rw [h, Nat.cast_le] at this
    omega
  · rw [renewalCount_eq_sum_range h₂]
    calc ∑ k ∈ Finset.range n, (if arrival T (k + 1) ω ≤ t then 1 else 0 : ℝ≥0∞)
        = ∑ k ∈ Finset.range n, (1 : ℝ≥0∞) :=
          Finset.sum_congr rfl fun k hk ↦
            ite_eq_left <| (monotone_arrival T ω (Finset.mem_range.1 hk)).trans h₁
      _ = n := by simp

/-- The count at time `t` is infinite exactly when every arrival time is at most `t`. -/
@[simp]
lemma renewalCount_eq_top_iff {t : ℝ≥0} {ω : Ω} :
    renewalCount T t ω = ⊤ ↔ ∀ n, arrival T n ω ≤ t := by
  refine ⟨fun h n ↦ natCast_le_renewalCount_iff.1 (h ▸ le_top), fun h ↦ ?_⟩
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
  exact (natCast_le_renewalCount_iff.2 (h n)).not_gt hn

/-- The count at time `t` is finite exactly when some arrival time exceeds `t`. -/
@[simp]
lemma renewalCount_lt_top_iff {t : ℝ≥0} {ω : Ω} :
    renewalCount T t ω < ⊤ ↔ ∃ n, t < arrival T n ω := by
  simp [lt_top_iff_ne_top, renewalCount_eq_top_iff]

/-- A finite count is a natural number. -/
lemma exists_renewalCount_eq_natCast {t : ℝ≥0} {ω : Ω} (h : renewalCount T t ω ≠ ⊤) :
    ∃ n : ℕ, renewalCount T t ω = n := by
  classical
  have hex := renewalCount_lt_top_iff.1 (lt_top_iff_ne_top.2 h)
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 :=
    Nat.exists_eq_add_one.2 <| Nat.pos_of_ne_zero fun h0 ↦ by
      simpa [h0] using Nat.find_spec hex
  refine ⟨m, renewalCount_eq_natCast_iff.2 ⟨not_lt.1 (Nat.find_min hex (by omega)), ?_⟩⟩
  simpa [hm] using Nat.find_spec hex

/-- The count is nondecreasing in time. -/
lemma monotone_renewalCount (ω : Ω) : Monotone fun t ↦ renewalCount T t ω := by
  intro s t hst
  simp only [renewalCount_def]
  refine ENNReal.tsum_le_tsum fun n ↦ ?_
  by_cases h : arrival T (n + 1) ω ≤ s
  · simp [h, h.trans hst]
  · simp [h]

/-- The count is locally constant to the right of every time. -/
lemma eventually_renewalCount_eq_nhdsGE (t : ℝ≥0) (ω : Ω) :
    ∀ᶠ s in 𝓝[≥] t, renewalCount T s ω = renewalCount T t ω := by
  by_cases htop : renewalCount T t ω = ⊤
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [htop, ← top_le_iff, ← htop]
    exact monotone_renewalCount ω hs
  · obtain ⟨n, hn⟩ := exists_renewalCount_eq_natCast htop
    obtain ⟨h₁, h₂⟩ := renewalCount_eq_natCast_iff.1 hn
    filter_upwards [Ico_mem_nhdsGE h₂] with s hs
    rw [hn, renewalCount_eq_natCast_iff]
    exact ⟨h₁.trans hs.1, hs.2⟩

/-- The count is right-continuous in time. -/
lemma continuousWithinAt_renewalCount_Ici (t : ℝ≥0) (ω : Ω) :
    ContinuousWithinAt (fun s ↦ renewalCount T s ω) (Ici t) t :=
  tendsto_const_nhds.congr' <|
    (eventually_renewalCount_eq_nhdsGE t ω).mono fun _ hs ↦ hs.symm

/-- The process does not explode at `ω`, i.e. its arrival times tend to infinity, exactly when
every count is finite. -/
lemma tendsto_arrival_atTop_iff {ω : Ω} :
    Tendsto (fun n ↦ arrival T n ω) atTop atTop ↔ ∀ t, renewalCount T t ω < ⊤ := by
  simp only [tendsto_atTop_atTop_iff_of_monotone (monotone_arrival T ω), renewalCount_lt_top_iff]
  exact ⟨fun h t ↦ (h (t + 1)).imp fun n hn ↦ (lt_add_one t).trans_le hn,
    fun h t ↦ (h t).imp fun n hn ↦ hn.le⟩

/-- If infinitely many increments are at least `a > 0`, the arrival times tend to infinity. -/
lemma tendsto_arrival_atTop_of_frequently_le {ω : Ω} {a : ℝ≥0} (ha : 0 < a)
    (h : ∃ᶠ n in atTop, a ≤ T n ω) : Tendsto (fun n ↦ arrival T n ω) atTop atTop := by
  have key : ∀ k : ℕ, ∃ n, k • a ≤ arrival T n ω := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hmn, hm⟩ := frequently_atTop.1 h n
      refine ⟨m + 1, ?_⟩
      rw [succ_nsmul, arrival_succ]
      exact add_le_add (hn.trans (monotone_arrival T ω hmn)) hm
  rw [tendsto_atTop_atTop_iff_of_monotone (monotone_arrival T ω)]
  intro b
  obtain ⟨k, hk⟩ := Archimedean.arch b ha
  exact (key k).imp fun n hn ↦ hk.trans hn

/-! ### Nonexplosion for i.i.d. increments -/

section Probability

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- **Nonexplosion of a renewal process.** If the increments are independent, identically
distributed and not almost surely zero, then almost surely the arrival times tend to infinity. -/
theorem ae_tendsto_arrival_atTop (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop := by
  have := hindep.isProbabilityMeasure
  -- Since `T 0` is not almost surely zero, some threshold `a > 0` has `0 < P (a ≤ T 0)`.
  obtain ⟨k, hpos⟩ : ∃ k : ℕ, 0 < P (T 0 ⁻¹' Ici (1 / (k + 1))) := by
    refine exists_measure_pos_of_not_measure_iUnion_null fun h0 ↦ hzero.ne ?_
    rw [← prob_compl_eq_zero_iff (measurableSet_eq_fun (hT 0) measurable_const)]
    refine measure_mono_null (fun ω (hω : T 0 ω ≠ 0) ↦ ?_) h0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (pos_iff_ne_zero.2 hω)
    exact mem_iUnion.2 ⟨k, hk.le⟩
  set a : ℝ≥0 := 1 / (k + 1)
  have ha : 0 < a := by positivity
  -- The events `{a ≤ T n}` are independent with a common positive probability, so by the second
  -- Borel–Cantelli lemma almost surely infinitely many of them occur.
  have hsm : ∀ n, MeasurableSet (T n ⁻¹' Ici a) := fun n ↦ hT n measurableSet_Ici
  have hindep_s : iIndepSet (fun n ↦ T n ⁻¹' Ici a) P :=
    (iIndepSet_iff_meas_biInter hsm).2 fun S ↦
      hindep.meas_biInter fun i _ ↦ ⟨Ici a, measurableSet_Ici, rfl⟩
  have hsum : ∑' n, P (T n ⁻¹' Ici a) = ∞ := by
    rw [tsum_congr fun n ↦ (hid n).measure_mem_eq measurableSet_Ici]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hpos.ne'
  have hlimsup : ∀ᵐ ω ∂P, ω ∈ limsup (fun n ↦ T n ⁻¹' Ici a) atTop :=
    mem_ae_iff.2 <| (prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hsm)).2 <|
      measure_limsup_eq_one hsm hindep_s hsum
  filter_upwards [hlimsup] with ω hω
  exact tendsto_arrival_atTop_of_frequently_le ha (mem_limsup_iff_frequently_mem.1 hω)

/-- **Finiteness of the renewal counts.** For independent, identically distributed increments
that are not almost surely zero, almost surely every count `renewalCount T t` is finite. The
almost-sure quantifier is outside the quantifier over all times. -/
theorem ae_renewalCount_lt_top (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) :
    ∀ᵐ ω ∂P, ∀ t, renewalCount T t ω < ⊤ := by
  filter_upwards [ae_tendsto_arrival_atTop hT hindep hid hzero] with ω hω
  exact tendsto_arrival_atTop_iff.1 hω

/-- **Transfer to the canonical product space.** For independent, identically distributed
increments, the law of `renewalCount T t` is the law of the count of the coordinate process under
the product measure whose factors are the common law of the increments. -/
theorem map_renewalCount_eq_infinitePi_map (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (t : ℝ≥0) :
    P.map (renewalCount T t) =
      (Measure.infinitePi fun _ : ℕ ↦ P.map (T 0)).map
        (renewalCount (fun n (w : ℕ → ℝ≥0) ↦ w n) t) := by
  have hcomp : renewalCount T t =
      renewalCount (fun n (w : ℕ → ℝ≥0) ↦ w n) t ∘ fun ω i ↦ T i ω := by
    ext ω
    simp only [Function.comp_apply, renewalCount_def, arrival_def]
  rw [hcomp, ← Measure.map_map (measurable_renewalCount (fun n ↦ measurable_pi_apply n) t)
    (measurable_pi_iff.2 hT), hindep.map_fun_eq_infinitePi_map hT]
  simp_rw [fun n ↦ (hid n).map_eq]

end Probability

end TauCeti.Probability
