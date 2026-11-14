/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Authors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.IntermediateValue

/-!
# Closed-set hitting times of continuous and right-continuous processes

For right-continuous paths (and in particular continuous paths), the first entrance into a closed
set is attained whenever it is finite, and is strictly after the starting time whenever the initial
value lies outside the target. For monotone right-continuous paths, hitting a closed upper ray
`Set.Ici c` by time `t` reduces to `c ≤ X t` at the single endpoint `t`, making the closed-ray hit
a stopping time on any raw filtration without second-countability, local compactness, right
continuity, or completion assumptions. When a natural-valued right-continuous path starts at or
below `c` and jumps by at most one from earlier times, each finite closed-ray hit is attained with
exact value `c` and strictly precedes the next level hit.

For general closed targets of continuous paths on a compact time interval, entrance is equivalent
to the minimum distance to the target being zero. Measuring that minimum on a second-countable
compact-interval time axis likewise gives a stopping time on the original filtration. Path
regularity here is everywhere, not merely almost sure; arbitrary null-set changes need not preserve
raw adaptation.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, Chapter 1, §2.
* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §§1 and 3.
-/

public section

open Filter Set Metric MeasureTheory
open scoped ENNReal Topology

variable {Ω ι E : Type*} [ConditionallyCompleteLinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι]

namespace IsClosed

variable [TopologicalSpace E] {X : ι → Ω → E} {s : Set E} {a t : ι} {ω : Ω}

/-- A right-continuous path attains its first entrance into a closed set whenever that entrance is
finite. The returned time is at least the declared starting time. -/
theorem exists_hittingAfter_eq_of_isRightContinuous (hs : IsClosed s)
    (hX : IsRightContinuous (X · ω)) (hfinite : hittingAfter X s a ω ≠ ⊤) :
    ∃ u : ι, hittingAfter X s a ω = u ∧ a ≤ u ∧ X u ω ∈ s := by
  classical
  have hex : ∃ u, a ≤ u ∧ X u ω ∈ s := by
    by_contra h
    exact hfinite (hittingAfter_eq_top_iff.mpr (by simpa using h))
  let A := {u | a ≤ u ∧ X u ω ∈ s}
  have hne : A.Nonempty := hex
  have hbdd : BddBelow A := ⟨a, fun _ hu ↦ hu.1⟩
  let u₀ := sInf A
  refine ⟨u₀, by simp [hittingAfter_def, hex, A, u₀], le_csInf hne fun _ hu ↦ hu.1, ?_⟩
  by_cases hmem : u₀ ∈ A
  · exact hmem.2
  · obtain ⟨w, hw⟩ := hne
    have hu₀w : u₀ < w := lt_of_le_of_ne (csInf_le hbdd hw) fun h ↦ hmem (h ▸ hw)
    have hfreq : ∃ᶠ v in 𝓝[>] u₀, X v ω ∈ s := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨z, hz, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hu₀w).mp hU
      obtain ⟨v, hvA, hvz⟩ := exists_lt_of_csInf_lt ⟨w, hw⟩ hz
      have hu₀v : u₀ < v := lt_of_le_of_ne (csInf_le hbdd hvA) fun h ↦ hmem (h ▸ hvA)
      exact ⟨v, hsub ⟨hu₀v, hvz⟩, hvA.2⟩
    exact hs.mem_of_frequently_of_tendsto hfreq (hX u₀)

/-- A continuous path attains its first entrance into a closed set, if that entrance is
finite. The returned time is at least the declared starting time. -/
theorem exists_hittingAfter_eq (hs : IsClosed s)
    (hX : Continuous (X · ω)) (hfinite : hittingAfter X s a ω ≠ ⊤) :
    ∃ u : ι, hittingAfter X s a ω = u ∧ a ≤ u ∧ X u ω ∈ s :=
  hs.exists_hittingAfter_eq_of_isRightContinuous hX.isRightContinuous hfinite

/-- At a finite closed-set entrance of a right-continuous path, the path lies in the target set. -/
theorem hittingAfter_mem_of_isRightContinuous_of_ne_top (hs : IsClosed s)
    (hX : IsRightContinuous (X · ω)) (hfinite : hittingAfter X s a ω ≠ ⊤) :
    X (hittingAfter X s a ω).untopA ω ∈ s := by
  have : Nonempty ι := ⟨a⟩
  obtain ⟨u, hu, -, hus⟩ := hs.exists_hittingAfter_eq_of_isRightContinuous hX hfinite
  simpa [hu] using hus

/-- For a right-continuous path and a closed target, entrance by time `t` means that an actual hit
occurs between the starting time and `t`, including both endpoints. -/
theorem hittingAfter_le_iff_of_isRightContinuous (hs : IsClosed s)
    (hX : IsRightContinuous (X · ω)) :
    hittingAfter X s a ω ≤ t ↔ ∃ u ∈ Icc a t, X u ω ∈ s := by
  constructor
  · intro h
    obtain ⟨u, hu, hau, hus⟩ := hs.exists_hittingAfter_eq_of_isRightContinuous hX
      (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    exact ⟨u, ⟨hau, WithTop.coe_le_coe.mp (hu ▸ h)⟩, hus⟩
  · rintro ⟨u, hu, hus⟩
    exact (hittingAfter_le_of_mem hu.1 hus).trans (WithTop.coe_le_coe.mpr hu.2)

/-- For a continuous path and a closed target, entrance by time `t` means that an
actual hit occurs between the starting time and `t`, including both endpoints. -/
theorem hittingAfter_le_iff (hs : IsClosed s) (hX : Continuous (X · ω)) :
    hittingAfter X s a ω ≤ t ↔ ∃ u ∈ Icc a t, X u ω ∈ s :=
  hs.hittingAfter_le_iff_of_isRightContinuous hX.isRightContinuous

/-- If a right-continuous path starts outside a closed set, its first entrance occurs strictly
after the starting time. -/
theorem lt_hittingAfter_of_isRightContinuous (hs : IsClosed s)
    (hX : IsRightContinuous (X · ω)) (ha : X a ω ∉ s) :
    (a : WithTop ι) < hittingAfter X s a ω := by
  refine lt_of_not_ge fun h ↦ ?_
  obtain ⟨u, hu, hus⟩ := (hs.hittingAfter_le_iff_of_isRightContinuous hX).mp h
  exact ha (le_antisymm hu.2 hu.1 ▸ hus)

end IsClosed

namespace IsRightContinuous

/-- For a monotone right-continuous path into a space with closed upper rays, hitting `Set.Ici c`
after `a` by time `t` is equivalent to `a ≤ t` and `c ≤ X t ω`. -/
theorem hittingAfter_Ici_le_iff_of_monotone {β : Type*} [Preorder β] [TopologicalSpace β]
    [ClosedIciTopology β] {X : ι → Ω → β} {a t : ι} {ω : Ω} {c : β}
    (hrc : IsRightContinuous (X · ω)) (hmono : Monotone (X · ω)) :
    hittingAfter X (Ici c) a ω ≤ t ↔ a ≤ t ∧ c ≤ X t ω := by
  rw [isClosed_Ici.hittingAfter_le_iff_of_isRightContinuous hrc]
  exact ⟨fun ⟨u, hu, hcu⟩ ↦ ⟨hu.1.trans hu.2, hcu.trans (hmono hu.2)⟩,
    fun ⟨hat, hct⟩ ↦ ⟨t, ⟨hat, le_rfl⟩, hct⟩⟩

/-- If a natural-valued right-continuous path starts at most at `c` and jumps by at most one from
strictly earlier times in `[a, t)`, then at any finite hit of `Set.Ici c` its value equals `c`. -/
theorem apply_untopA_hittingAfter_Ici_of_le_add_one {X : ι → Ω → ℕ} {a : ι} {ω : Ω} {c : ℕ}
    (hrc : IsRightContinuous (X · ω)) (ha : X a ω ≤ c)
    (hjump : ∀ ⦃t⦄, a < t → ∃ s ∈ Ico a t, X t ω ≤ X s ω + 1)
    (hfin : hittingAfter X (Ici c) a ω ≠ ⊤) :
    X (hittingAfter X (Ici c) a ω).untopA ω = c := by
  have : Nonempty ι := ⟨a⟩
  obtain ⟨u, hu, hau, hcu⟩ :=
    isClosed_Ici.exists_hittingAfter_eq_of_isRightContinuous hrc hfin
  have huntop : (hittingAfter X (Ici c) a ω).untopA = u := by simp [hu]
  rw [huntop]
  refine le_antisymm ?_ hcu
  rcases hau.eq_or_lt with rfl | hau
  · exact ha
  · obtain ⟨s, ⟨has, hsu⟩, hfs⟩ := hjump hau
    have hlt : X s ω < c := not_le.mp <|
      notMem_of_lt_hittingAfter (hu ▸ WithTop.coe_lt_coe.mpr hsu) has
    exact hfs.trans hlt

/-- Under the same right-continuity and unit-jump hypotheses, a finite hit of `Set.Ici c` strictly
precedes the hit of `Set.Ici (c + 1)`. -/
theorem hittingAfter_Ici_lt_succ_of_le_add_one {X : ι → Ω → ℕ} {a : ι} {ω : Ω} {c : ℕ}
    (hrc : IsRightContinuous (X · ω)) (ha : X a ω ≤ c)
    (hjump : ∀ ⦃t⦄, a < t → ∃ s ∈ Ico a t, X t ω ≤ X s ω + 1)
    (hfin : hittingAfter X (Ici c) a ω ≠ ⊤) :
    hittingAfter X (Ici c) a ω < hittingAfter X (Ici (c + 1)) a ω := by
  obtain ⟨u, hu, -, -⟩ :=
    isClosed_Ici.exists_hittingAfter_eq_of_isRightContinuous hrc hfin
  have hXu : X u ω = c := by
    have : Nonempty ι := ⟨a⟩
    simpa [hu] using hrc.apply_untopA_hittingAfter_Ici_of_le_add_one ha hjump hfin
  rw [hu]
  refine lt_of_not_ge fun hle ↦ ?_
  obtain ⟨v, ⟨hav, hvu⟩, hcv⟩ :=
    (isClosed_Ici.hittingAfter_le_iff_of_isRightContinuous hrc).mp hle
  rcases hvu.eq_or_lt with rfl | hvu
  · exact (Nat.lt_succ_self c).not_ge (hXu ▸ hcv)
  · exact notMem_of_lt_hittingAfter (hu ▸ WithTop.coe_lt_coe.mpr hvu) hav
      (Nat.le_of_succ_le hcv)

end IsRightContinuous

/-- A continuous ordered-valued path starting below a level stays at most at that level up to and
including its first closed-level hit. This is a pathwise statement, with no stopping-time
or measurability hypothesis. -/
theorem Continuous.le_of_le_hittingAfter_Ici [DenselyOrdered ι]
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
    {X : ι → Ω → β} {a t : ι} {ω : Ω} {C : β} (hX : Continuous (X · ω))
    (hat : a ≤ t) (hstart : X a ω ≤ C)
    (ht : (t : WithTop ι) ≤ MeasureTheory.hittingAfter X (Set.Ici C) a ω) :
    X t ω ≤ C := by
  by_contra h
  have hCt : C < X t ω := lt_of_not_ge h
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc hat hX.continuousOn ⟨hstart, hCt.le⟩
  have hut : u < t := lt_of_le_of_ne hu.2 (fun hut ↦ hCt.ne (hut ▸ hue).symm)
  have hhit := MeasureTheory.hittingAfter_le_of_mem (u := X) (s := Set.Ici C) hu.1 hue.ge
  exact (WithTop.coe_lt_coe.mpr hut).not_ge (ht.trans hhit)

namespace MeasureTheory

/-- First entrance into a closed upper ray `Set.Ici c` by an adapted process with everywhere
monotone right-continuous paths is a stopping time on any raw filtration. Neither second
countability, compact intervals, right continuity, nor completeness is required. -/
theorem Adapted.isStoppingTime_hittingAfter_Ici_of_monotone_of_isRightContinuous
    {β : Type*} [Preorder β] [TopologicalSpace β] [ClosedIciTopology β]
    [MeasurableSpace β] [OpensMeasurableSpace β]
    {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ} {X : ι → Ω → β}
    (hX : Adapted ℱ X) (hmono : ∀ ω, Monotone (X · ω))
    (hrc : ∀ ω, IsRightContinuous (X · ω)) (c : β) (a : ι) :
    IsStoppingTime ℱ (hittingAfter X (Ici c) a) := by
  intro t
  by_cases hat : a ≤ t
  · convert hX t (isClosed_Ici (a := c)).measurableSet using 1
    ext ω
    simp [(hrc ω).hittingAfter_Ici_le_iff_of_monotone (hmono ω), hat]
  · convert @MeasurableSet.empty Ω (ℱ t) using 1
    ext ω
    simp [(hrc ω).hittingAfter_Ici_le_iff_of_monotone (hmono ω), hat]

section Stopping

variable [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology ι] [CompactIccSpace ι]
  {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {X : ι → Ω → E} {s : Set E}

/-- Closed-set entrance of an everywhere-continuous adapted process is a stopping time
on an arbitrary filtration. Neither right continuity nor completeness is required. -/
theorem Adapted.isStoppingTime_hittingAfter_of_isClosed (hX : Adapted ℱ X)
    (hc : ∀ ω, Continuous (X · ω)) (hs : IsClosed s) (a : ι) :
    IsStoppingTime ℱ (hittingAfter X s a) := by
  classical
  intro t
  by_cases hat : a ≤ t
  · let K := Icc a t
    have hK : K.Nonempty := nonempty_Icc.mpr hat
    let : Nonempty K := hK.to_subtype
    have hcont (ω : Ω) : Continuous (fun u : K ↦ infEDist (X u ω) s) :=
      continuous_infEDist.comp ((hc ω).comp continuous_subtype_val)
    have hm : @Measurable Ω ℝ≥0∞ (ℱ t) _
        (fun ω ↦ ⨅ u : K, infEDist (X u ω) s) := by
      have hm' : @Measurable Ω ℝ≥0∞ (ℱ t) _
          (⨅ u : K, fun ω ↦ infEDist (X u ω) s) := by
        apply measurable_iInf_of_upperSemicontinuous
        · intro u
          exact continuous_infEDist.measurable.comp
            ((hX u).mono (ℱ.mono u.property.2) le_rfl)
        · exact fun ω ↦ (hcont ω).upperSemicontinuous
      convert hm' using 1
      exact funext fun ω ↦ (iInf_apply (f := fun (u : K) ω ↦
        infEDist (X u ω) s) (a := ω)).symm
    convert hm (measurableSet_singleton 0) using 1
    ext ω
    rw [mem_ofPred_eq, hs.hittingAfter_le_iff (hc ω)]
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨u, hu, hus⟩
      exact le_antisymm ((iInf_le _ (⟨u, hu⟩ : K)).trans_eq
        (infEDist_zero_of_mem hus)) bot_le
    · intro hz
      obtain ⟨u, _, hmin⟩ := isCompact_univ.exists_isMinOn
        (Set.univ_nonempty : (Set.univ : Set K).Nonempty) (hcont ω).continuousOn
      have hu : infEDist (X u ω) s = 0 := by
        apply le_antisymm _ bot_le
        exact (le_iInf fun v ↦ hmin (mem_univ v)).trans_eq hz
      exact ⟨u, u.property, (mem_iff_infEDist_zero_of_closed hs).mpr hu⟩
  · have heq : {ω | hittingAfter X s a ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, hs.hittingAfter_le_iff (hc ω), mem_empty_iff_false,
        iff_false, not_exists, not_and]
      exact fun u hu _ ↦ hat (hu.1.trans hu.2)
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- First exit from an open domain, including an immediate exit when the initial state
is outside, is a stopping time for a continuous adapted process on a raw filtration. -/
theorem Adapted.isStoppingTime_hittingAfter_compl_of_isOpen (hX : Adapted ℱ X)
    (hc : ∀ ω, Continuous (X · ω)) {U : Set E} (hU : IsOpen U) (a : ι) :
    IsStoppingTime ℱ (hittingAfter X Uᶜ a) :=
  hX.isStoppingTime_hittingAfter_of_isClosed hc hU.isClosed_compl a

end Stopping

end MeasureTheory
