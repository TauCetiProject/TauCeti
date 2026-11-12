/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.StochasticInterval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Pointwise announcing sequences

A predictable time is announced by increasing, everywhere finite stopping times which are
strictly smaller on its positive-time event. All requirements here are pointwise, including
convergence to infinity; these are not almost-sure announcing sequences. No probability measure,
completion, or right continuity of the filtration is assumed.

Announced times are stopping times. Deterministic times, including zero and infinity, are
predictable. Finite minima, finite maxima, countable suprema and pasting along `ℱ 0`-measurable
events preserve predictability. Announcing sequences also make the closed stochastic ray
`{(t, ω) | τ ω ≤ t}` predictable; this ray contains `(0, ω)` whenever `τ ω = 0`.
These operations are elementary input to predictable-section constructions.

## References

* S. Theodorakopoulos, *New proofs to measurable, predictable and optional section theorems*,
  arXiv:2310.13086v2, §4.
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
  refine ⟨?_, hm, ?_, ?_⟩
  · intro n t
    simpa only [Finset.sup_le_iff, ofPred_forall] using
      MeasurableSet.iInter (fun i ↦ MeasurableSet.iInter
        (fun (_ : i ∈ Finset.range (n + 1)) ↦ (ha i).isStoppingTime n t))
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
      (fun _ ↦ (t : WithTop ℝ≥0)) := by
  refine ⟨fun n ↦ isStoppingTime_const ℱ (t - 1 / (n + 1)), ?_, ?_, ?_⟩
  · intro _ n k hnk
    apply WithTop.coe_le_coe.mpr
    exact tsub_le_tsub_left (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnk 1)) t
  · intro _
    have hi : Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hl : Tendsto (fun n : ℕ ↦ t - 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.sub hi
    exact WithTop.continuous_coe.continuousAt.tendsto.comp hl
  · intro n _ ht
    exact WithTop.coe_lt_coe.mpr (tsub_lt_self (WithTop.coe_lt_coe.mp ht) (by positivity))

/-- The constant zero sequence announces time zero. -/
theorem zero : IsAnnouncingSequence ℱ (fun _ _ ↦ 0) (fun _ ↦ 0) := by
  simpa using NNReal.isAnnouncingSequence_const (ℱ := ℱ) 0

/-- The deterministic integer times announce infinity. -/
theorem top : IsAnnouncingSequence ℱ (fun n _ ↦ (n : ℝ≥0)) (fun _ ↦ ⊤) := by
  refine ⟨fun n ↦ isStoppingTime_const ℱ n, ?_, ?_, by simp⟩
  · intro _ n k hnk
    exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnk)
  · intro _
    exact WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop

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

end TauCeti.IsPredictableTime

/-- A stochastic open interval with stopping lower and predictable upper endpoint is
predictable. -/
theorem MeasureTheory.IsStoppingTime.measurableSet_predictable_Ioo
    {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {τ η : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (hη : TauCeti.IsPredictableTime ℱ η) :
    MeasurableSet[ℱ.predictable]
      {p : ℝ≥0 × Ω | τ p.2 < p.1 ∧ (p.1 : WithTop ℝ≥0) < η p.2} :=
  hτ.measurableSet_predictable_lt.inter hη.measurableSet_predictable_gt
