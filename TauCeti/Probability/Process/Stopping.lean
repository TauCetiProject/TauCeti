/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.IsLUB
import TauCeti.Probability.Process.Filtration.RightCont

/-!
# Stopping times and stopped paths

A stopping time remains a stopping time for a larger filtration, and its stopping sigma-algebra
embeds into the enlarged one. On a densely ordered unbounded-above index type, stopping times for
the right-continuation `ℱ.rightCont` are characterized by strict sublevel events `{τ < t} ∈ ℱ t`
(`MeasureTheory.isStoppingTime_rightCont_iff`), and their stopping sigma-algebras coincide with the
strict stopping sigma-algebra `{A | A ∈ ⨆ t, ℱ t ∧ ∀ t, A ∩ {τ < t} ∈ ℱ t}`
(`MeasureTheory.IsStoppingTime.measurableSet_rightCont_iff`). Adding a deterministic nonnegative
increment in a canonically ordered cancellative monoid with ordered subtraction preserves the
stopping-time property (`MeasureTheory.IsStoppingTime.add_const_of_orderedSub`) and generates the
post-stopping filtration `MeasureTheory.IsStoppingTime.shiftFiltration`. Finite suprema also
preserve the stopping-time property.

Stopping preserves right continuity at each time, including when the stopping time is infinite.
This pathwise fact requires no measurability or stopping-time hypothesis and lets local-martingale
arguments retain the right continuity of their native stopped stages. Subtracting the stopped
value from the value stopped at `τ + t` recovers the restarted increment on `{τ ≠ ⊤}` and
vanishes at `⊤` (`MeasureTheory.stoppedValue_add_const_sub_stoppedValue`).

Simultaneous almost-sure nonnegativity controls random-time evaluations, including stopped
processes restricted by an indicator (`MeasureTheory.ae_nonneg_stoppedProcess_indicator`).
Pathwise set membership up to the random time also passes to the stopped process. Neither
fact requires a stopping-time or measurability assumption.
-/

public section

namespace MeasureTheory.Filtration

/-- In an index type without a maximum, taking the right-continuation of a filtration leaves its
terminal supremum sigma-algebra unchanged. -/
@[simp]
theorem iSup_rightCont {ι Ω : Type*} [PartialOrder ι] [NoMaxOrder ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) : (⨆ t, ℱ.rightCont t) = ⨆ t, ℱ t := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_mono ℱ.le_rightCont)
  obtain ⟨u, htu⟩ := exists_gt t
  exact (ℱ.rightCont_le_of_lt htu).trans (le_iSup ℱ u)

end MeasureTheory.Filtration

namespace MeasureTheory

section RightCont

open Filter

variable {ι Ω : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [FirstCountableTopology ι] [DenselyOrdered ι] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ι mΩ} {τ : Ω → WithTop ι}

private theorem measurableSet_inter_lt_of_forall_le_rightCont {A : Set Ω}
    (hAle : ∀ s, MeasurableSet[ℱ.rightCont s] (A ∩ {ω | τ ω ≤ s})) (t : ι) :
    MeasurableSet[ℱ t] (A ∩ {ω | τ ω < t}) := by
  by_cases hex : ∃ s, s < t
  · obtain ⟨s₀, hs₀⟩ := hex
    obtain ⟨s, -, hs_mem, hs_lim⟩ := exists_seq_strictMono_tendsto' hs₀
    have heq : {ω | τ ω < t} = ⋃ n, {ω | τ ω ≤ s n} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      refine ⟨fun h => ?_, fun ⟨n, hn⟩ => hn.trans_lt (WithTop.coe_lt_coe.2 (hs_mem n).2)⟩
      cases hτω : τ ω with
      | top => simp [hτω] at h
      | coe a =>
        obtain ⟨n, hn⟩ :=
          (hs_lim.eventually (eventually_gt_nhds (WithTop.coe_lt_coe.1 (hτω ▸ h)))).exists
        exact ⟨n, WithTop.coe_le_coe.2 hn.le⟩
    rw [heq, Set.inter_iUnion]
    exact MeasurableSet.iUnion fun n => ℱ.rightCont_le_of_lt (hs_mem n).2 _ (hAle (s n))
  · have heq : A ∩ {ω | τ ω < t} = ∅ := by
      ext ω
      cases hτω : τ ω with
      | top => simp [hτω]
      | coe a =>
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_and, hτω, WithTop.coe_lt_coe]
        exact fun _ hat => hex ⟨a, hat⟩
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

private theorem measurableSet_inter_le_rightCont_of_forall_lt [NoMaxOrder ι] {A : Set Ω}
    (hAlt : ∀ u, MeasurableSet[ℱ u] (A ∩ {ω | τ ω < u})) (t : ι) :
    MeasurableSet[ℱ.rightCont t] (A ∩ {ω | τ ω ≤ t}) := by
  obtain ⟨s, -, hs_gt, hs_lim⟩ := exists_seq_strictAnti_tendsto t
  rw [ℱ.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  intro htu
  obtain ⟨k, hsk⟩ := (hs_lim.eventually_lt_const htu).exists
  have heq : A ∩ {ω | τ ω ≤ t} = ⋂ (m) (_ : s m ≤ s k), A ∩ {ω | τ ω < s m} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun ⟨hAω, hle⟩ m _ => ⟨hAω, hle.trans_lt (WithTop.coe_lt_coe.2 (hs_gt m))⟩,
      fun h => ⟨(h k le_rfl).1, le_of_forall_gt fun v hv => ?_⟩⟩
    cases v with
    | top => exact (h k le_rfl).2.trans (WithTop.coe_lt_top _)
    | coe b =>
      obtain ⟨m, hsm⟩ := (hs_lim.eventually_lt_const (WithTop.coe_lt_coe.1 hv)).exists
      rcases le_total (s m) (s k) with hmk | hkm
      · exact (h m hmk).2.trans (WithTop.coe_lt_coe.2 hsm)
      · exact (h k le_rfl).2.trans (WithTop.coe_lt_coe.2 (hkm.trans_lt hsm))
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun hm =>
    ℱ.mono (hm.trans hsk.le) _ (hAlt (s m))

/-- On a densely ordered first-countable index type without a maximum, `τ` is a stopping time for
`ℱ.rightCont` if and only if every strict sublevel event `{τ < t}` belongs to `ℱ t` (an *optional*
or *strict* stopping time in the raw filtration). -/
theorem isStoppingTime_rightCont_iff [NoMaxOrder ι] :
    IsStoppingTime ℱ.rightCont τ ↔ ∀ t, MeasurableSet[ℱ t] {ω | τ ω < t} := by
  refine ⟨fun hτ t => ?_, fun hlt t => ?_⟩
  · simpa only [Set.univ_inter] using
      measurableSet_inter_lt_of_forall_le_rightCont (A := Set.univ)
        (fun s => by simpa only [Set.univ_inter] using hτ s) t
  · simpa only [Set.univ_inter] using
      measurableSet_inter_le_rightCont_of_forall_lt (A := Set.univ)
        (fun u => by simpa only [Set.univ_inter] using hlt u) t

end RightCont

end MeasureTheory

namespace MeasureTheory.IsStoppingTime

/-- A stopping time for a filtration is also a stopping time for any larger filtration. -/
theorem mono_filtration {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ 𝒢 : Filtration ι mΩ} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) (h : ℱ ≤ 𝒢) : IsStoppingTime 𝒢 τ :=
  fun t => h t _ (hτ.measurableSet_le t)

/-- Enlarging the filtration enlarges the stopping sigma-algebra of a stopping time. -/
theorem measurableSpace_mono_filtration {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ 𝒢 : Filtration ι mΩ} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) (h : ℱ ≤ 𝒢) :
    hτ.measurableSpace ≤ (hτ.mono_filtration h).measurableSpace :=
  fun _ hs => ⟨iSup_mono h _ hs.1, fun i => h i _ (hs.2 i)⟩

/-- For an `ℱ.rightCont`-stopping time `τ` on a densely ordered first-countable index type without
a maximum, its stopping sigma-algebra coincides with the strict stopping sigma-algebra `ℱ_{τ+}`
characterized by `A ∈ ⨆ t, ℱ t` and `A ∩ {τ < t} ∈ ℱ t` for every `t`. -/
theorem measurableSet_rightCont_iff {ι Ω : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [FirstCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι]
    {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω} :
    MeasurableSet[hτ.measurableSpace] A ↔
      MeasurableSet[⨆ t, ℱ t] A ∧ ∀ t, MeasurableSet[ℱ t] (A ∩ {ω | τ ω < t}) :=
  ⟨fun ⟨hAsup, hAle⟩ => ⟨ℱ.iSup_rightCont ▸ hAsup,
    measurableSet_inter_lt_of_forall_le_rightCont hAle⟩,
   fun ⟨hAsup, hAlt⟩ => ⟨ℱ.iSup_rightCont.symm ▸ hAsup,
    measurableSet_inter_le_rightCont_of_forall_lt hAlt⟩⟩

section OrderedSub

variable {ι Ω : Type*} [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ι mΩ} {τ : Ω → WithTop ι}

/-- Adding a deterministic nonnegative delay preserves the stopping-time property in a
canonically ordered monoid with ordered subtraction, such as `ℝ≥0` or `ℕ`. -/
theorem add_const_of_orderedSub (hτ : IsStoppingTime ℱ τ) (c : ι) :
    IsStoppingTime ℱ (fun ω => τ ω + c) := by
  intro t
  by_cases hct : c ≤ t
  · have heq : {ω | τ ω + (c : WithTop ι) ≤ t} = {ω | τ ω ≤ (t - c : ι)} := by
      ext ω
      cases h : τ ω with
      | top => simp [h]
      | coe a =>
        simp only [Set.mem_ofPred_eq, h, ← WithTop.coe_add, WithTop.coe_le_coe]
        exact (le_tsub_iff_right hct).symm
    rw [heq]
    exact ℱ.mono tsub_le_self _ (hτ.measurableSet_le (t - c))
  · have heq : {ω | τ ω + (c : WithTop ι) ≤ t} = ∅ := by
      ext ω
      cases h : τ ω with
      | top => simp [h]
      | coe a =>
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, h, ← WithTop.coe_add,
          WithTop.coe_le_coe]
        exact fun hle => hct (le_add_self.trans hle)
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- The filtration after a stopping time `τ`, whose time-`t` sigma-algebra is the stopping
sigma-algebra of `τ + t`. -/
def shiftFiltration (hτ : IsStoppingTime ℱ τ) : Filtration ι mΩ where
  seq t := (hτ.add_const_of_orderedSub t).measurableSpace
  mono' _ _ hst := (hτ.add_const_of_orderedSub _).measurableSpace_mono
    (hτ.add_const_of_orderedSub _) fun ω => add_le_add_right (WithTop.coe_le_coe.2 hst) (τ ω)
  le' t := (hτ.add_const_of_orderedSub t).measurableSpace_le

/-- At time `t`, the shifted filtration is the stopping sigma-algebra of `τ + t`. -/
@[simp]
theorem shiftFiltration_apply (hτ : IsStoppingTime ℱ τ) (t : ι) :
    hτ.shiftFiltration t = (hτ.add_const_of_orderedSub t).measurableSpace :=
  (rfl)

/-- At time `0`, the shifted filtration recovers the stopping sigma-algebra of `τ`. -/
theorem shiftFiltration_zero (hτ : IsStoppingTime ℱ τ) :
    hτ.shiftFiltration 0 = hτ.measurableSpace :=
  le_antisymm
    ((hτ.add_const_of_orderedSub 0).measurableSpace_mono hτ fun ω => by simp)
    (hτ.measurableSpace_mono (hτ.add_const_of_orderedSub 0) fun ω => by simp)

/-- Every sigma-algebra of the shifted filtration contains the stopping sigma-algebra of `τ`. -/
theorem le_shiftFiltration (hτ : IsStoppingTime ℱ τ) (t : ι) :
    hτ.measurableSpace ≤ hτ.shiftFiltration t :=
  hτ.shiftFiltration_zero ▸ hτ.shiftFiltration.mono (zero_le (a := t))

end OrderedSub

end MeasureTheory.IsStoppingTime

/-- The finite supremum of stopping times is a stopping time.
The empty supremum is the constant bottom time. -/
theorem Finset.isStoppingTime_sup {κ ι Ω : Type*}
    [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ι mΩ}
    (s : Finset κ) {τ : κ → Ω → WithTop ι}
    (hτ : ∀ j ∈ s, MeasureTheory.IsStoppingTime ℱ (τ j)) :
    MeasureTheory.IsStoppingTime ℱ (fun ω ↦ s.sup (fun j ↦ τ j ω)) := by
  have h := Finset.sup_induction
    (p := fun σ : Ω → WithTop ι ↦ MeasureTheory.IsStoppingTime ℱ σ)
    (MeasureTheory.isStoppingTime_const ℱ ⊥) (fun _ ha _ hb ↦ ha.max hb) hτ
  have heq : s.sup τ = fun ω ↦ s.sup (fun j ↦ τ j ω) := funext (s.sup_apply τ)
  exact heq ▸ h

open Filter Set
open scoped Topology

/-- Stopping preserves right continuity of a path at a given time, without any measurability
assumption on the random time. At an infinite stopping time the path is unchanged. -/
theorem ContinuousWithinAt.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {t : ι}
    (hX : ContinuousWithinAt (X · ω) (Ioi t) t) :
    ContinuousWithinAt (MeasureTheory.stoppedProcess X τ · ω) (Ioi t) t := by
  cases hτ : τ ω with
  | top => simpa [MeasureTheory.stoppedProcess, hτ] using hX
  | coe u =>
    by_cases htu : t < u
    · refine hX.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds htu)] with s hs
        exact MeasureTheory.stoppedProcess_eq_of_le (by simpa [hτ] using hs.le)
      · exact MeasureTheory.stoppedProcess_eq_of_le (by simpa [hτ] using htu.le)
    · have hut : u ≤ t := le_of_not_gt htu
      refine (continuousWithinAt_const (b := X (τ ω).untopA ω)).congr
        (fun s hs => ?_) ?_
      · exact MeasureTheory.stoppedProcess_eq_of_ge (by simpa [hτ] using hut.trans hs.le)
      · exact MeasureTheory.stoppedProcess_eq_of_ge (by simpa [hτ] using hut)

namespace MeasureTheory

/-- A path that stays in a set up to a random time also stays in that set when stopped.
No measurability or stopping-time assumption is needed. -/
theorem stoppedProcess_mem {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {s : Set E}
    (hX : ∀ u : ι, (u : WithTop ι) ≤ τ ω → X u ω ∈ s) (t : ι) :
    stoppedProcess X τ t ω ∈ s := by
  by_cases ht : (t : WithTop ι) ≤ τ ω
  · rw [stoppedProcess_eq_of_le ht]
    exact hX t ht
  · rw [stoppedProcess_eq_of_ge (le_of_not_ge ht)]
    exact hX _ (by cases τ ω <;> simp)

/-- Evaluate the stopped process restricted to the event that its random time is positive.
No measurability or stopping-time assumption is needed. -/
theorem stoppedProcess_indicator_pos_apply {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [Zero E] {X : ι → Ω → E} (τ : Ω → WithTop ι) (t : ι) (ω : Ω) :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω =
      if ⊥ < τ ω then X (min (t : WithTop ι) (τ ω)).untopA ω else 0 := by
  rw [stoppedProcess_indicator_comm]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, stoppedProcess]

/-- At the initial time, stopping leaves any process unchanged. -/
@[simp]
theorem stoppedProcess_bot {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    (u : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess u τ ⊥ = u ⊥ := by
  ext ω
  exact stoppedProcess_eq_of_le (by simp)

variable {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι] [Zero E] [Preorder E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {s : Set Ω}

/-- A simultaneously almost-surely nonnegative process, stopped and restricted by an indicator,
is almost surely nonnegative at each fixed time. The random time need not be a stopping time. -/
theorem ae_nonneg_stoppedProcess_indicator
    (hpos : ∀ᵐ ω ∂P, ∀ t, 0 ≤ X t ω) (τ : Ω → WithTop ι) (t : ι) :
    0 ≤ᵐ[P] stoppedProcess (fun u ↦ s.indicator (X u)) τ t := by
  filter_upwards [hpos] with ω hω
  by_cases ht : (t : WithTop ι) ≤ τ ω
  · rw [stoppedProcess_eq_of_le ht]
    exact Set.indicator_apply_nonneg (fun _ ↦ hω t)
  · rw [stoppedProcess_eq_of_ge (le_of_not_ge ht)]
    exact Set.indicator_apply_nonneg (fun _ ↦ hω _)

/-- At a finite random time `τ ω ≠ ⊤`, evaluating `stoppedValue` at `τ + t` evaluates the
process at `(τ ω).untopA + t`. -/
theorem stoppedValue_add_const_of_ne_top {ι Ω E : Type*} [Add ι] [Nonempty ι]
    (X : ι → Ω → E) {τ : Ω → WithTop ι} (t : ι) {ω : Ω} (h : τ ω ≠ ⊤) :
    stoppedValue X (fun ω' => τ ω' + t) ω = X ((τ ω).untopA + t) ω := by
  cases hτ : τ ω with
  | top => exact absurd hτ h
  | coe s => simp [stoppedValue, hτ, ← WithTop.coe_add]

/-- Subtracting `stoppedValue X τ` from `stoppedValue X (τ + t)` gives the restarted increment
on `{τ ≠ ⊤}` and vanishes on `{τ = ⊤}`. -/
theorem stoppedValue_add_const_sub_stoppedValue {ι Ω E : Type*} [Add ι] [Nonempty ι]
    [AddGroup E] (X : ι → Ω → E) (τ : Ω → WithTop ι) (t : ι) :
    stoppedValue X (fun ω => τ ω + t) - stoppedValue X τ =
      {ω | τ ω ≠ ⊤}.indicator (fun ω => X ((τ ω).untopA + t) ω - X (τ ω).untopA ω) := by
  ext ω
  cases hτ : τ ω with
  | top => simp [stoppedValue, hτ]
  | coe s => simp [stoppedValue, hτ, ← WithTop.coe_add]

end MeasureTheory
