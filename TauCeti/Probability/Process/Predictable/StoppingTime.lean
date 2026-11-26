/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.StochasticInterval
public import TauCeti.Probability.Process.Stopping
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Topology.Instances.NNReal
import TauCeti.Topology.Order.WithTop

/-!
# Pointwise and almost-sure announcing sequences

A pointwise predictable time (`TauCeti.IsPredictableTime`) is announced by an increasing sequence of
everywhere finite stopping times (`TauCeti.IsAnnouncingSequence`) which are strictly smaller on its
positive-time event. These requirements hold on every outcome, including convergence to infinity,
without assuming a probability measure, completion, or right continuity of the filtration.

Pointwise announced times are stopping times. Deterministic times, including zero and infinity, are
predictable. Positive deterministic delays of stopping times, finite minima, finite maxima,
countable suprema, pasting along `ℱ 0`-measurable events, and restricting a predictable time to
`{τ ≤ η}` for a stopping time `η` all preserve pointwise predictability. Announcing sequences make
the closed stochastic ray `{(t, ω) | τ ω ≤ t}` predictable, and these closed rays generate the full
predictable sigma-algebra without completeness or right continuity of the filtration.

We also define almost-sure announcing sequences (`TauCeti.IsAEAnnouncingSequence`) with respect to a
measure `P` and upgrade them to pointwise announcing sequences when `ℱ` is `P`-complete or, for
stopping times `τ`, when every ambient-measurable `P`-null set belongs to `ℱ 0`.

## References

* S. Theodorakopoulos, *New proofs to measurable, predictable and optional section theorems*,
  arXiv:2310.13086v2, §4.
* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, North-Holland, 1978,
  Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace TauCeti

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {τ η : Ω → WithTop ℝ≥0} {σ ρ : ℕ → Ω → WithTop ℝ≥0}

/-- A pointwise announcing sequence consists of increasing, everywhere finite stopping times,
converging to the announced time, and strictly below it wherever that time is positive. -/
structure IsAnnouncingSequence (ℱ : Filtration ℝ≥0 m)
    (σ : ℕ → Ω → WithTop ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Prop where
  /-- Every approximant is a stopping time of the original filtration. -/
  isStoppingTime : ∀ n, IsStoppingTime ℱ (σ n)
  /-- The approximants increase on every outcome. -/
  monotone : ∀ ω, Monotone (fun n ↦ σ n ω)
  /-- Convergence includes outcomes on which the announced time is infinite. -/
  tendsto : ∀ ω, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))
  /-- Strict announcement is required on the positive-time event only. -/
  lt : ∀ n ω, 0 < τ ω → σ n ω < τ ω

/-- A time is pointwise predictable if it admits an everywhere finite announcing sequence.
Such a time is automatically a stopping time, even for a raw filtration. -/
def IsPredictableTime (ℱ : Filtration ℝ≥0 m) (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∃ σ, IsAnnouncingSequence ℱ σ τ

/-- Unpack pointwise predictability into an announcing sequence. -/
theorem isPredictableTime_iff : IsPredictableTime ℱ τ ↔ ∃ σ, IsAnnouncingSequence ℱ σ τ :=
  Iff.rfl

namespace IsAnnouncingSequence

/-- An announcing sequence makes its announced time pointwise predictable. -/
theorem isPredictableTime (h : IsAnnouncingSequence ℱ σ τ) : IsPredictableTime ℱ τ :=
  ⟨σ, h⟩

/-- Every announcing approximant is at most its announced time, including at time zero. -/
theorem le (h : IsAnnouncingSequence ℱ σ τ) (n : ℕ) (ω : Ω) : σ n ω ≤ τ ω :=
  (h.monotone ω).ge_of_tendsto (h.tendsto ω) n

/-- Every announcing approximant is finite on every outcome. -/
theorem ne_top (h : IsAnnouncingSequence ℱ σ τ) (n : ℕ) (ω : Ω) : σ n ω ≠ ⊤ := by
  by_cases hτ : 0 < τ ω
  · exact ne_top_of_lt (h.lt n ω hτ)
  · exact ne_top_of_le_ne_top WithTop.zero_ne_top ((h.le n ω).trans (not_lt.mp hτ))

/-- An announced time is exactly the pointwise supremum of its announcing sequence. -/
theorem iSup_eq (h : IsAnnouncingSequence ℱ σ τ) (ω : Ω) : (⨆ n, σ n ω) = τ ω :=
  iSup_eq_of_tendsto (h.monotone ω) (h.tendsto ω)

/-- The limit of an announcing sequence is a stopping time without right continuity. -/
theorem isStoppingTime_limit (h : IsAnnouncingSequence ℱ σ τ) : IsStoppingTime ℱ τ := by
  intro t
  have he : {ω | τ ω ≤ t} = ⋂ n, {ω | σ n ω ≤ t} := by
    ext ω
    simp only [← h.iSup_eq ω, iSup_le_iff, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.iInter fun n ↦ h.isStoppingTime n t

/-- The pointwise minimum of two announcing sequences announces the minimum time. -/
theorem min (hσ : IsAnnouncingSequence ℱ σ τ) (hρ : IsAnnouncingSequence ℱ ρ η) :
    IsAnnouncingSequence ℱ (fun n ω ↦ min (σ n ω) (ρ n ω))
      (fun ω ↦ min (τ ω) (η ω)) where
  isStoppingTime n := (hσ.isStoppingTime n).min (hρ.isStoppingTime n)
  monotone ω := (hσ.monotone ω).min (hρ.monotone ω)
  tendsto ω := (hσ.tendsto ω).min (hρ.tendsto ω)
  lt n ω h := lt_min
    ((min_le_left _ _).trans_lt (hσ.lt n ω (h.trans_le (min_le_left _ _))))
    ((min_le_right _ _).trans_lt (hρ.lt n ω (h.trans_le (min_le_right _ _))))

/-- The pointwise maximum of two announcing sequences announces the maximum time. -/
theorem max (hσ : IsAnnouncingSequence ℱ σ τ) (hρ : IsAnnouncingSequence ℱ ρ η) :
    IsAnnouncingSequence ℱ (fun n ω ↦ max (σ n ω) (ρ n ω))
      (fun ω ↦ max (τ ω) (η ω)) where
  isStoppingTime n := (hσ.isStoppingTime n).max (hρ.isStoppingTime n)
  monotone ω := (hσ.monotone ω).max (hρ.monotone ω)
  tendsto ω := (hσ.tendsto ω).max (hρ.tendsto ω)
  lt n ω h := by
    apply max_lt
    · by_cases hτ : 0 < τ ω
      · exact (hσ.lt n ω hτ).trans_le (le_max_left _ _)
      · exact (hσ.le n ω).trans_lt ((not_lt.mp hτ).trans_lt h)
    · by_cases hη : 0 < η ω
      · exact (hρ.lt n ω hη).trans_le (le_max_right _ _)
      · exact (hρ.le n ω).trans_lt ((not_lt.mp hη).trans_lt h)

/-- The finite diagonal maxima announce the supremum of an `ℕ`-indexed family of times,
even when some or all of the announced times are infinite. -/
theorem iSup {θ : ℕ → Ω → WithTop ℝ≥0} {a : ℕ → ℕ → Ω → WithTop ℝ≥0}
    (ha : ∀ i, IsAnnouncingSequence ℱ (a i) (θ i)) :
    IsAnnouncingSequence ℱ
      (fun n ω ↦ (Finset.range (n + 1)).sup (fun i ↦ a i n ω)) (fun ω ↦ ⨆ i, θ i ω) := by
  have hm (ω : Ω) : Monotone (fun n ↦ (Finset.range (n + 1)).sup (fun i ↦ a i n ω)) := by
    intro n k hnk
    exact Finset.sup_le fun i hi ↦ ((ha i).monotone ω hnk).trans
      (Finset.le_sup (f := fun i ↦ a i k ω)
        (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le
          (Nat.add_le_add_right hnk 1))))
  refine ⟨fun n ↦ (Finset.range (n + 1)).isStoppingTime_sup fun i _ ↦ (ha i).isStoppingTime n,
    hm, ?_, ?_⟩
  · intro ω
    -- Every row is eventually included, and its entries increase along the diagonal.
    have he : (⨆ n, (Finset.range (n + 1)).sup (fun i ↦ a i n ω)) = ⨆ i, θ i ω := by
      apply le_antisymm
      · exact iSup_le fun n ↦ Finset.sup_le fun i _ ↦
          le_iSup_of_le i ((ha i).le n ω)
      · refine iSup_le fun i ↦ ?_
        rw [← (ha i).iSup_eq ω]
        refine iSup_le fun k ↦ le_iSup_of_le (Nat.max i k) ?_
        exact ((ha i).monotone ω (le_max_right i k)).trans
          (Finset.le_sup (f := fun j ↦ a j (Nat.max i k) ω)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left i k))))
    rw [← he]
    exact tendsto_atTop_iSup (hm ω)
  · intro n ω hpos
    apply (Finset.sup_lt_iff hpos).mpr
    intro i _
    by_cases hi : 0 < θ i ω
    · exact ((ha i).lt n ω hi).trans_le (le_iSup (fun i ↦ θ i ω) i)
    · exact ((ha i).le n ω).trans_lt
        (lt_of_le_of_lt (not_lt.mp hi) hpos)

/-- The deterministic times approaching `t` from below announce the finite constant time `t`. -/
theorem _root_.NNReal.isAnnouncingSequence_const (t : ℝ≥0) :
    IsAnnouncingSequence ℱ (fun n _ ↦ (t - 1 / (n + 1 : ℝ≥0) : ℝ≥0))
      (fun _ ↦ (t : WithTop ℝ≥0)) where
  isStoppingTime n := isStoppingTime_const ℱ (t - 1 / (n + 1))
  monotone _ _ _ hnk := WithTop.coe_le_coe.mpr (NNReal.monotone_tsub_one_div_add_one t hnk)
  tendsto _ := NNReal.tendsto_coe_tsub_one_div_add_one t
  lt _ _ ht := WithTop.coe_lt_coe.mpr (tsub_lt_self (WithTop.coe_lt_coe.mp ht) (by positivity))

/-- The constant zero sequence announces time zero. -/
theorem zero : IsAnnouncingSequence ℱ (fun _ _ ↦ 0) (fun _ ↦ 0) := by
  simpa using NNReal.isAnnouncingSequence_const (ℱ := ℱ) 0

/-- The deterministic integer times announce infinity. -/
theorem top : IsAnnouncingSequence ℱ (fun n _ ↦ (n : ℝ≥0)) (fun _ ↦ ⊤) where
  isStoppingTime n := isStoppingTime_const ℱ n
  monotone _ _ _ hnk := WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnk)
  tendsto _ := WithTop.tendsto_coe_natCast_atTop
  lt := by simp

/-- Pasting announcing sequences along an event known at time zero announces the pasted time. -/
theorem piecewise (hσ : IsAnnouncingSequence ℱ σ τ) (hρ : IsAnnouncingSequence ℱ ρ η)
    {s : Set Ω} [DecidablePred (· ∈ s)] (hs : MeasurableSet[ℱ 0] s) :
    IsAnnouncingSequence ℱ (fun n ↦ s.piecewise (σ n) (ρ n)) (s.piecewise τ η) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun n ↦ (hσ.isStoppingTime n).piecewise_of_le (hρ.isStoppingTime n)
      (fun _ ↦ bot_le) (fun _ ↦ bot_le) hs
  · intro ω
    by_cases hω : ω ∈ s
    · simpa [hω] using hσ.monotone ω
    · simpa [hω] using hρ.monotone ω
  · intro ω
    by_cases hω : ω ∈ s
    · simpa [hω] using hσ.tendsto ω
    · simpa [hω] using hρ.tendsto ω
  · intro n ω
    by_cases hω : ω ∈ s
    · simpa [hω] using hσ.lt n ω
    · simpa [hω] using hρ.lt n ω

end IsAnnouncingSequence

namespace IsPredictableTime

/-- Pointwise predictable times are stopping times of their declared filtration. -/
theorem isStoppingTime (h : IsPredictableTime ℱ τ) : IsStoppingTime ℱ τ := by
  obtain ⟨σ, hσ⟩ := h
  exact hσ.isStoppingTime_limit

/-- The minimum of two pointwise predictable times is pointwise predictable. -/
theorem min (hτ : IsPredictableTime ℱ τ) (hη : IsPredictableTime ℱ η) :
    IsPredictableTime ℱ (fun ω ↦ min (τ ω) (η ω)) := by
  obtain ⟨σ, hσ⟩ := hτ
  obtain ⟨ρ, hρ⟩ := hη
  exact ⟨_, hσ.min hρ⟩

/-- The maximum of two pointwise predictable times is pointwise predictable. -/
theorem max (hτ : IsPredictableTime ℱ τ) (hη : IsPredictableTime ℱ η) :
    IsPredictableTime ℱ (fun ω ↦ max (τ ω) (η ω)) := by
  obtain ⟨σ, hσ⟩ := hτ
  obtain ⟨ρ, hρ⟩ := hη
  exact ⟨_, hσ.max hρ⟩

/-- Time zero is pointwise predictable. -/
theorem zero : IsPredictableTime ℱ (fun _ ↦ 0) :=
  IsAnnouncingSequence.zero.isPredictableTime

/-- The infinite time is pointwise predictable. -/
theorem top : IsPredictableTime ℱ (fun _ ↦ ⊤) :=
  IsAnnouncingSequence.top.isPredictableTime

/-- Every deterministic time is pointwise predictable, including zero and infinity. -/
-- Simplify before coercions to `WithTop ℝ≥0` are rewritten to coercions to `ENNReal`.
@[simp↓]
theorem const {t : WithTop ℝ≥0} : IsPredictableTime ℱ (fun _ ↦ t) := by
  cases t with
  | top => exact top
  | coe t => exact t.isAnnouncingSequence_const.isPredictableTime

/-- Countable suprema of pointwise predictable times are pointwise predictable. -/
theorem iSup {ι : Sort*} [Countable ι] {θ : ι → Ω → WithTop ℝ≥0}
    (hθ : ∀ i, IsPredictableTime ℱ (θ i)) :
    IsPredictableTime ℱ (fun ω ↦ ⨆ i, θ i ω) := by
  cases isEmpty_or_nonempty ι with
  | inl h => simp
  | inr h =>
    obtain ⟨f, hf⟩ := exists_surjective_nat ι
    choose a ha using fun n ↦ hθ (f n)
    have he : (fun ω ↦ ⨆ n, θ (f n) ω) = (fun ω ↦ ⨆ i, θ i ω) :=
      funext fun ω ↦ hf.iSup_comp (fun i ↦ θ i ω)
    exact he ▸ (IsAnnouncingSequence.iSup ha).isPredictableTime

/-- The infimum of a finite family of pointwise predictable times is pointwise predictable. -/
theorem finsetInf {ι : Type*} {s : Finset ι} {θ : ι → Ω → WithTop ℝ≥0}
    (hθ : ∀ i ∈ s, IsPredictableTime ℱ (θ i)) :
    IsPredictableTime ℱ (fun ω ↦ s.inf (θ · ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s _ ih =>
    simpa only [Finset.inf_insert] using
      (hθ i (Finset.mem_insert_self i s)).min
        (ih fun j hj ↦ hθ j (Finset.mem_insert_of_mem hj))

/-- The supremum of a finite family of pointwise predictable times is pointwise predictable. -/
theorem finsetSup {ι : Type*} {s : Finset ι} {θ : ι → Ω → WithTop ℝ≥0}
    (hθ : ∀ i ∈ s, IsPredictableTime ℱ (θ i)) :
    IsPredictableTime ℱ (fun ω ↦ s.sup (θ · ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s _ ih =>
    simpa only [Finset.sup_insert] using
      (hθ i (Finset.mem_insert_self i s)).max
        (ih fun j hj ↦ hθ j (Finset.mem_insert_of_mem hj))

/-- Pasting predictable times along an event known at time zero preserves predictability.
Taking the second time to be infinity restricts a predictable time to the event. -/
theorem piecewise (hτ : IsPredictableTime ℱ τ) (hη : IsPredictableTime ℱ η)
    {s : Set Ω} [DecidablePred (· ∈ s)] (hs : MeasurableSet[ℱ 0] s) :
    IsPredictableTime ℱ (s.piecewise τ η) := by
  obtain ⟨σ, hσ⟩ := hτ
  obtain ⟨ρ, hρ⟩ := hη
  exact (hσ.piecewise hρ hs).isPredictableTime

end IsPredictableTime

end TauCeti

namespace TauCeti.IsPredictableTime

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {τ : Ω → WithTop ℝ≥0}

/-- The closed stochastic ray of a pointwise predictable time is predictable, including
`(0, ω)` whenever `τ ω = 0`. No completeness assumption is used. -/
theorem measurableSet_predictable_le (hτ : IsPredictableTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 ≤ p.1} := by
  obtain ⟨σ, hσ⟩ := hτ
  have he : {p : ℝ≥0 × Ω | τ p.2 ≤ p.1} =
      ({0} ×ˢ {ω | τ ω = 0}) ∪ ⋂ n, {p : ℝ≥0 × Ω | σ n p.2 < p.1} := by
    ext ⟨t, ω⟩
    simp only [mem_ofPred_eq, mem_union, mem_prod, mem_singleton_iff, mem_iInter]
    constructor
    · intro h
      by_cases ht : τ ω = 0
      · by_cases ht0 : t = 0
        · exact Or.inl ⟨ht0, ht⟩
        · have hpos : (0 : WithTop ℝ≥0) < (t : WithTop ℝ≥0) := by
            exact_mod_cast (pos_iff_ne_zero.mpr ht0 : 0 < t)
          exact Or.inr fun n ↦ (hσ.le n ω).trans_lt (ht ▸ hpos)
      · exact Or.inr fun n ↦ (hσ.lt n ω (pos_iff_ne_zero.mpr ht)).trans_le h
    · rintro (⟨rfl, h0⟩ | h)
      · simp [h0]
      · rw [← hσ.iSup_eq ω]
        exact iSup_le fun n ↦ (h n).le
  rw [he]
  have hzero : MeasurableSet[ℱ 0] {ω | τ ω = 0} := by
    simpa only [WithTop.coe_zero, nonpos_iff_eq_zero] using hσ.isStoppingTime_limit 0
  exact (measurableSet_predictable_singleton_bot_prod hzero).union
    (MeasurableSet.iInter fun n ↦ (hσ.isStoppingTime n).measurableSet_predictable_lt)

/-- The strict lower ray of a pointwise predictable time is predictable. -/
theorem measurableSet_predictable_gt (hτ : IsPredictableTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < τ p.2} := by
  simpa only [compl_ofPred, not_le] using hτ.measurableSet_predictable_le.compl

/-- The finite graph of a pointwise predictable time is predictable. -/
theorem measurableSet_predictable_eq (hτ : IsPredictableTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 = p.1} := by
  simpa only [← ofPred_and, ← le_antisymm_iff] using
    hτ.measurableSet_predictable_le.inter hτ.isStoppingTime.measurableSet_predictable_ge

/-- A stochastic closed interval with predictable lower and stopping upper endpoint is
predictable. -/
theorem measurableSet_predictable_Icc (hτ : IsPredictableTime ℱ τ)
    {η : Ω → WithTop ℝ≥0} (hη : IsStoppingTime ℱ η) :
    MeasurableSet[ℱ.predictable]
      {p : ℝ≥0 × Ω | τ p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ η p.2} :=
  hτ.measurableSet_predictable_le.inter hη.measurableSet_predictable_ge

/-- A stochastic right-open interval between two predictable times is predictable. -/
theorem measurableSet_predictable_Ico (hτ : IsPredictableTime ℱ τ)
    {η : Ω → WithTop ℝ≥0} (hη : IsPredictableTime ℱ η) :
    MeasurableSet[ℱ.predictable]
      {p : ℝ≥0 × Ω | τ p.2 ≤ p.1 ∧ (p.1 : WithTop ℝ≥0) < η p.2} :=
  hτ.measurableSet_predictable_le.inter hη.measurableSet_predictable_gt

/-- Every `ℱ 0`-measurable event `A` gives a pointwise predictable `0`/`⊤`-valued time whose
closed upper ray is `univ ×ˢ A`. -/
theorem exists_setOf_le_eq_univ_prod {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    ∃ τ : Ω → WithTop ℝ≥0,
      IsPredictableTime ℱ τ ∧ {p : ℝ≥0 × Ω | τ p.2 ≤ p.1} = univ ×ˢ A := by
  classical
  refine ⟨A.piecewise (fun _ ↦ 0) (fun _ ↦ ⊤),
    IsPredictableTime.zero.piecewise IsPredictableTime.top hA, ?_⟩
  ext ⟨t, ω⟩
  by_cases hω : ω ∈ A
  · simp only [hω, piecewise_eq_of_mem, mem_ofPred_eq, mem_prod, mem_univ, true_and, iff_true]
    exact bot_le
  · simp only [hω, not_false_eq_true, piecewise_eq_of_notMem, mem_ofPred_eq, top_le_iff,
      WithTop.coe_ne_top, mem_prod, mem_univ, true_and]

end TauCeti.IsPredictableTime

namespace TauCeti

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {τ η : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

/-- A strictly positive deterministic shift of a stopping time is announced by finite clipped
strictly smaller shifts. -/
theorem _root_.MeasureTheory.IsStoppingTime.isAnnouncingSequence_add_const
    (hτ : IsStoppingTime ℱ τ) {c : ℝ≥0} (hc : 0 < c) :
    IsAnnouncingSequence ℱ
      (fun n ω ↦ min ((n : ℝ≥0) : WithTop ℝ≥0)
        (τ ω + ((c - 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)))
      (fun ω ↦ τ ω + (c : WithTop ℝ≥0)) := by
  refine ⟨fun n ↦ (isStoppingTime_const ℱ n).min (hτ.add_const_of_orderedSub _), ?_, ?_, ?_⟩
  · intro ω n k hnk
    refine min_le_min (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnk)) ?_
    cases τ ω with
    | top => simp
    | coe a =>
      exact_mod_cast add_le_add_right (NNReal.monotone_tsub_one_div_add_one c hnk) a
  · intro ω
    have hg : Tendsto (fun n : ℕ ↦ τ ω + ((c - 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0))
        atTop (𝓝 (τ ω + (c : WithTop ℝ≥0))) := by
      cases τ ω with
      | top =>
        simp only [WithTop.top_add]
        exact tendsto_const_nhds
      | coe a =>
        have hl : Tendsto (fun n : ℕ ↦ a + (c - 1 / (n + 1 : ℝ≥0))) atTop (𝓝 (a + c)) :=
          tendsto_const_nhds.add (NNReal.tendsto_tsub_one_div_add_one c)
        exact_mod_cast (WithTop.continuous_coe.tendsto (a + c)).comp hl
    simpa [min_top_left] using WithTop.tendsto_coe_natCast_atTop.min hg
  · intro n ω _
    cases τ ω with
    | top => exact (min_le_left _ _).trans_lt (WithTop.coe_lt_top _)
    | coe a =>
      refine (min_le_right _ _).trans_lt ?_
      exact_mod_cast add_lt_add_right (tsub_lt_self hc (by positivity)) a

/-- Shifting any stopping time forward by a strictly positive deterministic delay produces a
pointwise predictable time. -/
theorem _root_.MeasureTheory.IsStoppingTime.isPredictableTime_add_const
    (hτ : IsStoppingTime ℱ τ) {c : ℝ≥0} (hc : 0 < c) :
    IsPredictableTime ℱ (fun ω ↦ τ ω + (c : WithTop ℝ≥0)) :=
  (hτ.isAnnouncingSequence_add_const hc).isPredictableTime

/-- Restricting an announcing sequence to `{σ n ≤ η}` and pushing it to infinity after `σ n`
passes the stopping time `η` announces the restriction of `τ` to `{τ ≤ η}`. -/
theorem IsAnnouncingSequence.ite_le (hσ : IsAnnouncingSequence ℱ σ τ)
    (hη : IsStoppingTime ℱ η) :
    IsAnnouncingSequence ℱ
      (fun n ω ↦ if σ n ω ≤ η ω then σ n ω else σ n ω ⊔ ((n : ℝ≥0) : WithTop ℝ≥0))
      (fun ω ↦ if τ ω ≤ η ω then τ ω else ⊤) := by
  refine ⟨fun n ↦ (hσ.isStoppingTime n).ite_le_sup_const hη n, ?_, ?_, ?_⟩
  · intro ω n k hnk
    have hsnk := hσ.monotone ω hnk
    by_cases hn : σ n ω ≤ η ω
    · by_cases hk : σ k ω ≤ η ω
      · simpa only [hn, hk, ↓reduceIte] using hsnk
      · simpa only [hn, hk, ↓reduceIte] using hsnk.trans le_sup_left
    · have hk : ¬ σ k ω ≤ η ω := fun hk ↦ hn (hsnk.trans hk)
      simpa only [hn, hk, ↓reduceIte] using
        sup_le_sup hsnk (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnk))
  · intro ω
    by_cases hle : τ ω ≤ η ω
    · have heq : (fun n ↦ if σ n ω ≤ η ω then σ n ω
          else σ n ω ⊔ ((n : ℝ≥0) : WithTop ℝ≥0)) = fun n ↦ σ n ω :=
        funext fun n ↦ ite_eq_left ((hσ.le n ω).trans hle)
      simpa only [hle, ↓reduceIte, heq] using hσ.tendsto ω
    · have hev : ∀ᶠ n in atTop, η ω < σ n ω :=
        (hσ.tendsto ω).eventually (isOpen_Ioi.mem_nhds (lt_of_not_ge hle))
      simp only [hle, ↓reduceIte]
      refine tendsto_nhds_top_mono WithTop.tendsto_coe_natCast_atTop ?_
      filter_upwards [hev] with n hn
      rw [ite_eq_right (not_le_of_gt hn)]
      exact le_sup_right
  · intro n ω hpos
    by_cases hle : τ ω ≤ η ω
    · have hn : σ n ω ≤ η ω := (hσ.le n ω).trans hle
      rw [ite_eq_left hle] at hpos
      simpa only [hn, hle, ↓reduceIte] using hσ.lt n ω hpos
    · by_cases hn : σ n ω ≤ η ω
      · simpa only [hn, hle, ↓reduceIte] using (hσ.ne_top n ω).lt_top
      · simpa only [hn, hle, ↓reduceIte] using
          sup_lt_iff.mpr ⟨(hσ.ne_top n ω).lt_top, WithTop.coe_lt_top _⟩

/-- Restricting a pointwise predictable time `τ` to `{τ ≤ η}` for a stopping time `η` (with `⊤`
outside that event) yields a pointwise predictable time, without completeness or right
continuity. -/
theorem IsPredictableTime.ite_le (hτ : IsPredictableTime ℱ τ) (hη : IsStoppingTime ℱ η) :
    IsPredictableTime ℱ (fun ω ↦ if τ ω ≤ η ω then τ ω else ⊤) := by
  obtain ⟨σ, hσ⟩ := hτ
  exact (hσ.ite_le hη).isPredictableTime

end TauCeti

/-- A stochastic open interval with stopping lower and predictable upper endpoint is
predictable. -/
theorem MeasureTheory.IsStoppingTime.measurableSet_predictable_Ioo
    {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {τ η : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (hη : TauCeti.IsPredictableTime ℱ η) :
    MeasurableSet[ℱ.predictable]
      {p : ℝ≥0 × Ω | τ p.2 < p.1 ∧ (p.1 : WithTop ℝ≥0) < η p.2} :=
  hτ.measurableSet_predictable_lt.inter hη.measurableSet_predictable_gt

/-- For a stopping time, predictability of its finite graph `[[τ]]` is equivalent to
predictability of its closed upper ray `[τ, ∞)`. -/
theorem MeasureTheory.IsStoppingTime.measurableSet_predictable_eq_iff_le
    {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 = p.1} ↔
      MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | τ p.2 ≤ p.1} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [← ofPred_or, ← le_iff_eq_or_lt] using h.union hτ.measurableSet_predictable_lt
  · simpa only [← ofPred_and, ← le_antisymm_iff] using h.inter hτ.measurableSet_predictable_ge

section GenerateFromPredictableRays

private lemma singleton_zero_prod_mem_generateFrom {Ω : Type*} {m : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 m) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    MeasurableSet[MeasurableSpace.generateFrom
      {u : Set (ℝ≥0 × Ω) | ∃ τ, TauCeti.IsPredictableTime ℱ τ ∧ u = {p | τ p.2 ≤ p.1}}]
      ({(0 : ℝ≥0)} ×ˢ A) := by
  let G := MeasurableSpace.generateFrom
    {u : Set (ℝ≥0 × Ω) | ∃ τ, TauCeti.IsPredictableTime ℱ τ ∧ u = {p | τ p.2 ≤ p.1}}
  have hray {τ : Ω → WithTop ℝ≥0} (hτ : TauCeti.IsPredictableTime ℱ τ) :
      MeasurableSet[G] {p : ℝ≥0 × Ω | τ p.2 ≤ p.1} :=
    MeasurableSpace.measurableSet_generateFrom ⟨τ, hτ, rfl⟩
  obtain ⟨τA, hτA, hτA_eq⟩ := TauCeti.IsPredictableTime.exists_setOf_le_eq_univ_prod hA
  have hA_ray : MeasurableSet[G] (univ ×ˢ A) := hτA_eq ▸ hray hτA
  have h0 : MeasurableSet[G] ({(0 : ℝ≥0)} ×ˢ (univ : Set Ω)) := by
    rw [prod_univ, NNReal.singleton_zero_eq_compl_iUnion_Ici_one_div_add_one, preimage_compl,
      preimage_iUnion]
    refine (MeasurableSet.iUnion fun k ↦ ?_).compl
    have heq : Prod.fst ⁻¹' Ici (1 / (k + 1 : ℝ≥0)) =
        {p : ℝ≥0 × Ω | ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ p.1} := by
      ext p; simp only [mem_preimage, mem_Ici, mem_ofPred_eq, WithTop.coe_le_coe]
    rw [heq]
    exact hray TauCeti.IsPredictableTime.const
  have hinter : ({(0 : ℝ≥0)} ×ˢ (univ : Set Ω)) ∩ (univ ×ˢ A) = {(0 : ℝ≥0)} ×ˢ A := by
    ext ⟨t, ω⟩; simp
  exact hinter ▸ h0.inter hA_ray

private lemma Ioi_prod_mem_generateFrom {Ω : Type*} {m : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 m) {s : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    MeasurableSet[MeasurableSpace.generateFrom
      {u : Set (ℝ≥0 × Ω) | ∃ τ, TauCeti.IsPredictableTime ℱ τ ∧ u = {p | τ p.2 ≤ p.1}}]
      (Ioi s ×ˢ A) := by
  classical
  let η : Ω → WithTop ℝ≥0 := A.piecewise (fun _ ↦ (s : WithTop ℝ≥0)) (fun _ ↦ ⊤)
  have hη : IsStoppingTime ℱ η :=
    (isStoppingTime_const ℱ s).piecewise_of_le (isStoppingTime_top ℱ)
      (fun _ ↦ le_rfl) (fun _ ↦ le_top) hA
  have heq : Ioi s ×ˢ A =
      ⋃ k : ℕ, {p : ℝ≥0 × Ω | η p.2 + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ p.1} := by
    ext ⟨t, ω⟩
    rw [mem_iUnion]
    simp only [mem_ofPred_eq, ← NNReal.lt_coe_iff_exists_add_one_div_add_one_le]
    by_cases hω : ω ∈ A
    · simp only [η, hω, piecewise_eq_of_mem, mem_prod, mem_Ioi, and_true, WithTop.coe_lt_coe]
    · simp only [η, hω, not_false_eq_true, piecewise_eq_of_notMem, mem_prod, mem_Ioi, and_false,
        not_top_lt]
  rw [heq]
  exact MeasurableSet.iUnion fun k ↦ MeasurableSpace.measurableSet_generateFrom
    ⟨_, hη.isPredictableTime_add_const (by positivity), rfl⟩

/-- Closed upper stochastic rays `[τ, ∞)` of pointwise predictable times generate the predictable
sigma-algebra, without completeness or right continuity of the filtration. -/
theorem MeasureTheory.Filtration.predictable_eq_generateFrom_isPredictableTime_le
    {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m) :
    ℱ.predictable = MeasurableSpace.generateFrom
      {u : Set (ℝ≥0 × Ω) | ∃ τ, TauCeti.IsPredictableTime ℱ τ ∧ u = {p | τ p.2 ≤ p.1}} := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
    · simpa only [NNReal.bot_eq_zero] using
        singleton_zero_prod_mem_generateFrom ℱ (by simpa only [NNReal.bot_eq_zero] using hA)
    · exact Ioi_prod_mem_generateFrom ℱ hA
  · rintro _ ⟨_, hτ, rfl⟩
    exact hτ.measurableSet_predictable_le

end GenerateFromPredictableRays

namespace TauCeti

section AEAnnouncingSequence

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {P : Measure Ω} {σ : ℕ → Ω → WithTop ℝ≥0} {τ : Ω → WithTop ℝ≥0}

/-- An almost-sure announcing sequence consists of `ℱ`-stopping times that almost surely increase
to `τ` (including at infinity) and are almost surely strictly smaller than `τ` wherever `0 < τ`. -/
structure IsAEAnnouncingSequence (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    (σ : ℕ → Ω → WithTop ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Prop where
  /-- Every approximant is a stopping time of the filtration. -/
  isStoppingTime : ∀ n, IsStoppingTime ℱ (σ n)
  /-- The approximants increase almost surely. -/
  monotone : ∀ᵐ ω ∂P, Monotone (fun n ↦ σ n ω)
  /-- The approximants converge to `τ` almost surely, including on `{τ = ⊤}`. -/
  tendsto : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))
  /-- Strict announcement holds almost surely wherever `τ` is positive. -/
  lt : ∀ᵐ ω ∂P, ∀ n, 0 < τ ω → σ n ω < τ ω

/-- Every pointwise announcing sequence is an almost-sure announcing sequence for every measure. -/
theorem IsAnnouncingSequence.isAEAnnouncingSequence (h : IsAnnouncingSequence ℱ σ τ)
    (P : Measure Ω) : IsAEAnnouncingSequence ℱ P σ τ where
  isStoppingTime := h.isStoppingTime
  monotone := Eventually.of_forall h.monotone
  tendsto := Eventually.of_forall h.tendsto
  lt := Eventually.of_forall fun ω n hpos ↦ h.lt n ω hpos

namespace IsAEAnnouncingSequence

/-- Almost surely, every approximant of an almost-sure announcing sequence is at most `τ`. -/
theorem ae_le (h : IsAEAnnouncingSequence ℱ P σ τ) : ∀ᵐ ω ∂P, ∀ n, σ n ω ≤ τ ω := by
  filter_upwards [h.monotone, h.tendsto] with ω hmono htend n
  exact hmono.ge_of_tendsto htend n

/-- Almost surely, every approximant of an almost-sure announcing sequence is finite. -/
theorem ae_ne_top (h : IsAEAnnouncingSequence ℱ P σ τ) : ∀ᵐ ω ∂P, ∀ n, σ n ω ≠ ⊤ := by
  filter_upwards [h.ae_le, h.lt] with ω hle hlt n
  by_cases hpos : 0 < τ ω
  · exact ne_top_of_lt (hlt n hpos)
  · exact ne_top_of_le_ne_top WithTop.zero_ne_top ((hle n).trans (not_lt.mp hpos))

/-- Almost surely, `τ` is the supremum of its almost-sure announcing sequence. -/
theorem ae_iSup_eq (h : IsAEAnnouncingSequence ℱ P σ τ) :
    ∀ᵐ ω ∂P, (⨆ n, σ n ω) = τ ω := by
  filter_upwards [h.monotone, h.tendsto] with ω hmono htend
  exact iSup_eq_of_tendsto hmono htend

-- Pointwise fallback approximants used on the exceptional null set when upgrading to a pointwise
-- announcing sequence: `(τ - 1 / (n + 1))^+ ∧ n` on finite values and `n` at infinity.
private def fallbackStep (n : ℕ) : WithTop ℝ≥0 → WithTop ℝ≥0
  | ⊤ => (n : ℝ≥0)
  | (t : ℝ≥0) => min ((n : ℝ≥0) : WithTop ℝ≥0) ((t - 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)

private theorem fallbackStep_properties (x : WithTop ℝ≥0) :
    Monotone (fun n ↦ fallbackStep n x) ∧
      Tendsto (fun n ↦ fallbackStep n x) atTop (𝓝 x) ∧
      (∀ n, 0 < x → fallbackStep n x < x) := by
  cases x with
  | top =>
    exact ⟨fun _ _ hnk ↦ WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnk),
      WithTop.tendsto_coe_natCast_atTop, fun n _ ↦ WithTop.coe_lt_top (n : ℝ≥0)⟩
  | coe t =>
    refine ⟨fun _ _ hnk ↦ min_le_min (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnk))
        (WithTop.coe_le_coe.mpr (NNReal.monotone_tsub_one_div_add_one t hnk)),
      by simpa only [fallbackStep, min_top_left] using
        WithTop.tendsto_coe_natCast_atTop.min (NNReal.tendsto_coe_tsub_one_div_add_one t),
      fun n ht ↦ (min_le_right _ _).trans_lt
        (WithTop.coe_lt_coe.mpr (tsub_lt_self (WithTop.coe_lt_coe.mp ht) (by positivity)))⟩

private theorem measurableSet_fallbackStep_le (hτ : IsStoppingTime ℱ τ) (n : ℕ) (t : ℝ≥0) :
    MeasurableSet {ω | fallbackStep n (τ ω) ≤ t} := by
  by_cases hnt : (n : ℝ≥0) ≤ t
  · have heq : {ω | fallbackStep n (τ ω) ≤ t} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      cases τ ω with
      | top => exact WithTop.coe_le_coe.mpr hnt
      | coe s => exact (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hnt)
    exact heq ▸ MeasurableSet.univ
  · have heq : {ω | fallbackStep n (τ ω) ≤ t} =
        {ω | τ ω ≤ ((t + 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      cases τ ω with
      | top =>
        simp only [fallbackStep, WithTop.coe_le_coe, hnt, top_le_iff, WithTop.coe_ne_top]
      | coe s =>
        simp only [fallbackStep, min_le_iff, WithTop.coe_le_coe, hnt, false_or]
        exact tsub_le_iff_right
    rw [heq]
    exact ℱ.le _ _ (hτ _)

-- The full-measure event on which `σ` satisfies the three pathwise announcement conditions for `τ`.
private def goodSet (σ : ℕ → Ω → WithTop ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Set Ω :=
  {ω | Monotone (fun n ↦ σ n ω) ∧
    Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) ∧ (∀ n, 0 < τ ω → σ n ω < τ ω)}

private theorem measure_compl_goodSet_eq_zero (h : IsAEAnnouncingSequence ℱ P σ τ) :
    P (goodSet σ τ)ᶜ = 0 := by
  rw [← mem_ae_iff]
  filter_upwards [h.monotone, h.tendsto, h.lt] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

-- Shared piecewise upgrade replacing `σ` with `fallbackStep · (τ ·)` outside a subset `s` of
-- `goodSet σ τ`.
private theorem isAnnouncingSequence_piecewise_fallbackStep {s : Set Ω} [DecidablePred (· ∈ s)]
    (hs : s ⊆ goodSet σ τ)
    (hstop : ∀ n t, MeasurableSet[ℱ t] (s ∩ {ω | σ n ω ≤ t}))
    (hfall : ∀ n t, MeasurableSet[ℱ t] (sᶜ ∩ {ω | fallbackStep n (τ ω) ≤ t})) :
    IsAnnouncingSequence ℱ (fun n ↦ s.piecewise (σ n) (fun ω ↦ fallbackStep n (τ ω))) τ where
  isStoppingTime n t := by
    have heq : {ω | s.piecewise (σ n) (fun ω ↦ fallbackStep n (τ ω)) ω ≤ t} =
        (s ∩ {ω | σ n ω ≤ t}) ∪ (sᶜ ∩ {ω | fallbackStep n (τ ω) ≤ t}) := by
      ext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    exact heq ▸ (hstop n t).union (hfall n t)
  monotone ω := by
    by_cases hω : ω ∈ s
    · simpa [hω] using (hs hω).1
    · simpa [hω] using (fallbackStep_properties (τ ω)).1
  tendsto ω := by
    by_cases hω : ω ∈ s
    · simpa [hω] using (hs hω).2.1
    · simpa [hω] using (fallbackStep_properties (τ ω)).2.1
  lt n ω hpos := by
    by_cases hω : ω ∈ s
    · simpa [hω] using (hs hω).2.2 n hpos
    · simpa [hω] using (fallbackStep_properties (τ ω)).2.2 n hpos

/-- When every ambient-measurable `P`-null set belongs to `ℱ 0` (for instance on
`ℱ.ambientNullAugmentation P`), a stopping time `τ` admitting an almost-sure announcing sequence
also admits a pointwise announcing sequence. -/
theorem exists_isAnnouncingSequence_of_null (h : IsAEAnnouncingSequence ℱ P σ τ)
    (hτ : IsStoppingTime ℱ τ)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ σ', IsAnnouncingSequence ℱ σ' τ := by
  classical
  let N : Set Ω := toMeasurable P (goodSet σ τ)ᶜ
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable P _
  have hN_null : P N = 0 := by rw [measure_toMeasurable, h.measure_compl_goodSet_eq_zero]
  have hN_F0 : MeasurableSet[ℱ 0] N := hnull N hN_meas hN_null
  refine ⟨_, isAnnouncingSequence_piecewise_fallbackStep (s := Nᶜ)
    (compl_subset_comm.mp (subset_toMeasurable P _))
    (fun n t ↦ (ℱ.mono bot_le _ hN_F0.compl).inter (h.isStoppingTime n t))
    fun n t ↦ ?_⟩
  rw [compl_compl]
  exact ℱ.mono bot_le _ (hnull _ (hN_meas.inter (measurableSet_fallbackStep_le hτ n t))
    (measure_mono_null inter_subset_left hN_null))

/-- On a `P`-complete filtration, any random time admitting an almost-sure announcing sequence also
admits a pointwise announcing sequence (without assuming a priori that `τ` is measurable or a
stopping time). -/
theorem exists_isAnnouncingSequence [ℱ.IsComplete P] (h : IsAEAnnouncingSequence ℱ P σ τ) :
    ∃ σ', IsAnnouncingSequence ℱ σ' τ := by
  classical
  have hG_null : P (goodSet σ τ)ᶜ = 0 := h.measure_compl_goodSet_eq_zero
  refine ⟨_, isAnnouncingSequence_piecewise_fallbackStep (s := goodSet σ τ) subset_rfl
    (fun n t ↦ ?_) fun n t ↦
      Filtration.IsComplete.measurableSet_of_null (measure_mono_null inter_subset_left hG_null) t⟩
  have hG_meas : MeasurableSet[ℱ t] (goodSet σ τ) :=
    compl_compl (goodSet σ τ) ▸ (Filtration.IsComplete.measurableSet_of_null hG_null t).compl
  exact hG_meas.inter (h.isStoppingTime n t)

/-- On a `P`-complete filtration, every time admitting an almost-sure announcing sequence is
pointwise predictable. -/
theorem isPredictableTime [ℱ.IsComplete P] (h : IsAEAnnouncingSequence ℱ P σ τ) :
    IsPredictableTime ℱ τ := by
  obtain ⟨σ', hσ'⟩ := h.exists_isAnnouncingSequence
  exact hσ'.isPredictableTime

end IsAEAnnouncingSequence

/-- On a `P`-complete filtration, a random time is pointwise predictable if and only if it admits an
almost-sure announcing sequence. -/
theorem isPredictableTime_iff_exists_isAEAnnouncingSequence
    (P : Measure Ω) [ℱ.IsComplete P] :
    IsPredictableTime ℱ τ ↔ ∃ σ, IsAEAnnouncingSequence ℱ P σ τ :=
  ⟨fun h ↦ let ⟨σ, hσ⟩ := isPredictableTime_iff.mp h; ⟨σ, hσ.isAEAnnouncingSequence P⟩,
    fun ⟨_, hσ⟩ ↦ hσ.isPredictableTime⟩

end AEAnnouncingSequence

end TauCeti

end
