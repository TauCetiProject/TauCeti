/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Authors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Probability.Process.Version

/-!
# Closed-set hitting times of continuous adapted processes

For continuous paths, the first entrance into a closed set is attained whenever it is
finite. On a compact time interval, entrance is equivalent to the minimum distance to
the target being zero. The minimum can be measured through a countable dense set of
times, giving a stopping time on the original filtration, without right continuity or
completion assumptions. For ordered-valued continuous paths, first entrance into a
singleton coincides with first entrance into the corresponding closed half-line when the
initial state lies on the opposite side, and a path starting in `[a, b]` remains in
`[a, b]` up to its first exit from `(a, b)` and hits `{a, b}` when that exit is finite.

For arbitrary processes and state spaces—without order, topology, or path-continuity
hypotheses—post-composition and negation pull target sets back through preimages, entrance
into a union of two sets is the minimum of the two individual entrance times, and
indistinguishable processes have almost everywhere equal hitting times.

These results apply in particular to exits from open domains and to closed-level
localization of continuous adapted processes. Stopping-time measurability on a raw
filtration requires everywhere path continuity, whereas ambient almost-everywhere
measurability holds for almost-surely continuous processes via an indistinguishable
continuous version.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, Chapter 1, §2.
-/

public section

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Indistinguishable

/-- Indistinguishable processes have almost everywhere equal first hitting times of any set after
any starting time. -/
theorem hittingAfter_ae_eq {ι Ω E : Type*} [Preorder ι] [InfSet ι] {_ : MeasurableSpace Ω}
    {P : Measure Ω} {X Y : ι → Ω → E} (h : X ≡ᵐ[P] Y) (s : Set E) (a : ι) :
    hittingAfter X s a =ᵐ[P] hittingAfter Y s a := by
  classical exact h.mono fun _ hω ↦ by simp only [hittingAfter_def, hω]

end ProbabilityTheory.Indistinguishable

namespace MeasureTheory

/-- First entrance of `f (X t ω)` into `s` equals first entrance of `X` into `f ⁻¹' s`. -/
theorem hittingAfter_comp {Ω ι E F : Type*} [Preorder ι] [InfSet ι]
    (f : E → F) (X : ι → Ω → E) (s : Set F) (a : ι) :
    hittingAfter (fun t ω ↦ f (X t ω)) s a = hittingAfter X (f ⁻¹' s) a := by
  classical ext ω; simp only [hittingAfter_def, mem_preimage]

/-- First entrance of `-X` into `s` equals first entrance of `X` into `Neg.neg ⁻¹' s`. -/
theorem hittingAfter_neg {Ω ι E : Type*} [Preorder ι] [InfSet ι] [Neg E]
    (X : ι → Ω → E) (s : Set E) (a : ι) :
    hittingAfter (-X) s a = hittingAfter X (Neg.neg ⁻¹' s) a :=
  Pi.neg_def (f := X) ▸ hittingAfter_comp Neg.neg X s a

end MeasureTheory

variable {Ω ι E : Type*} [ConditionallyCompleteLinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι]

namespace IsClosed

variable [TopologicalSpace E] {X : ι → Ω → E} {s : Set E} {a t : ι} {ω : Ω}

/-- A continuous path attains its first entrance into a closed set, if that entrance is
finite. The returned time is at least the declared starting time. -/
theorem exists_hittingAfter_eq (hs : IsClosed s)
    (hX : Continuous (X · ω)) (hfinite : hittingAfter X s a ω ≠ ⊤) :
    ∃ u : ι, hittingAfter X s a ω = u ∧ a ≤ u ∧ X u ω ∈ s := by
  classical
  have hne : ∃ u, a ≤ u ∧ X u ω ∈ s := by
    by_contra h
    exact hfinite (hittingAfter_eq_top_iff.mpr (by simpa using h))
  have hclosed : IsClosed {u | a ≤ u ∧ X u ω ∈ s} :=
    isClosed_Ici.inter (hs.preimage hX)
  have hmem := hclosed.csInf_mem hne ⟨a, fun _ hu ↦ hu.1⟩
  exact ⟨_, by simp [hittingAfter_def, hne], hmem⟩

/-- For a continuous path and a closed target, entrance by time `t` means that an
actual hit occurs between the starting time and `t`, including both endpoints. -/
theorem hittingAfter_le_iff (hs : IsClosed s) (hX : Continuous (X · ω)) :
    hittingAfter X s a ω ≤ t ↔ ∃ u ∈ Icc a t, X u ω ∈ s := by
  constructor
  · intro h
    obtain ⟨u, hu, hau, hus⟩ := hs.exists_hittingAfter_eq hX
      (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    exact ⟨u, ⟨hau, WithTop.coe_le_coe.mp (hu ▸ h)⟩, hus⟩
  · rintro ⟨u, hu, hus⟩
    exact (hittingAfter_le_of_mem hu.1 hus).trans (WithTop.coe_le_coe.mpr hu.2)

end IsClosed

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

section OrderedPath

variable [DenselyOrdered ι] {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
  {X : ι → Ω → β} {ω : Ω}

/-- A continuous ordered-valued path starting above a level stays at least at that level up to and
including its first closed lower-level hit. -/
theorem Continuous.ge_of_le_hittingAfter_Iic {a t : ι} {C : β} (hX : Continuous (X · ω))
    (hat : a ≤ t) (hstart : C ≤ X a ω)
    (ht : (t : WithTop ι) ≤ MeasureTheory.hittingAfter X (Set.Iic C) a ω) : C ≤ X t ω :=
  hX.le_of_le_hittingAfter_Ici (β := βᵒᵈ) hat hstart ht

/-- A continuous ordered-valued path starting at or below `C` hits `{C}` at the same time as it
hits `[C, ∞)`. -/
theorem Continuous.hittingAfter_singleton_eq_Ici {a : ι} {C : β} (hX : Continuous (X · ω))
    (hstart : X a ω ≤ C) :
    MeasureTheory.hittingAfter X {C} a ω = MeasureTheory.hittingAfter X (Set.Ici C) a ω := by
  refine le_antisymm ?_ (MeasureTheory.hittingAfter_apply_anti X a ω (singleton_subset_iff.mpr
    (mem_Ici.mpr le_rfl)))
  cases ht : MeasureTheory.hittingAfter X (Set.Ici C) a ω using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    obtain ⟨u, hu, hus⟩ := (isClosed_Ici.hittingAfter_le_iff hX).mp ht.le
    obtain ⟨v, hv, hvC⟩ := intermediate_value_Icc hu.1 hX.continuousOn ⟨hstart, hus⟩
    exact (MeasureTheory.hittingAfter_le_of_mem hv.1 hvC).trans
      (WithTop.coe_le_coe.mpr (hv.2.trans hu.2))

/-- A continuous ordered-valued path starting at or above `C` hits `{C}` at the same time as
`(-∞, C]`. -/
theorem Continuous.hittingAfter_singleton_eq_Iic {a : ι} {C : β} (hX : Continuous (X · ω))
    (hstart : C ≤ X a ω) :
    MeasureTheory.hittingAfter X {C} a ω = MeasureTheory.hittingAfter X (Set.Iic C) a ω :=
  hX.hittingAfter_singleton_eq_Ici (β := βᵒᵈ) hstart

/-- A continuous ordered-valued path starting in `[a, b]` remains in `[a, b]` up to and including
its first exit from `(a, b)`. -/
theorem Continuous.mem_Icc_of_le_hittingAfter_compl_Ioo {u t : ι} {a b : β}
    (hX : Continuous (X · ω)) (hut : u ≤ t) (hstart : X u ω ∈ Icc a b)
    (ht : (t : WithTop ι) ≤ MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω) : X t ω ∈ Icc a b :=
  ⟨hX.ge_of_le_hittingAfter_Iic hut hstart.1
      (ht.trans (MeasureTheory.hittingAfter_apply_anti X u ω fun _ hy h ↦ hy.not_gt h.1)),
    hX.le_of_le_hittingAfter_Ici hut hstart.2
      (ht.trans (MeasureTheory.hittingAfter_apply_anti X u ω fun _ hy h ↦ hy.not_gt h.2))⟩

/-- A continuous ordered-valued path starting in `[a, b]` evaluates to `a` or `b` at any finite
first exit time from `(a, b)`. -/
theorem Continuous.eval_untopA_hittingAfter_compl_Ioo_eq_or_eq [Nonempty ι] {u : ι} {a b : β}
    (hX : Continuous (X · ω)) (hstart : X u ω ∈ Icc a b)
    (hfin : MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω ≠ ⊤) :
    X (MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω).untopA ω = a ∨
      X (MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω).untopA ω = b := by
  obtain ⟨t, ht, hut, hts⟩ := isOpen_Ioo.isClosed_compl.exists_hittingAfter_eq hX hfin
  have hmem := hX.mem_Icc_of_le_hittingAfter_compl_Ioo hut hstart ht.symm.le
  simp only [ht, WithTop.untopA, WithTop.untopD_coe]
  exact hmem.1.eq_or_lt.imp Eq.symm fun hlt ↦ hmem.2.eq_or_lt.resolve_right (hts ⟨hlt, ·⟩)

end OrderedPath

namespace MeasureTheory

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- First entrance into a union of two sets is the minimum of the first entrances into each set,
pointwise on paths. -/
theorem hittingAfter_union_apply (X : ι → Ω → E) (s₁ s₂ : Set E) (a : ι) (ω : Ω) :
    hittingAfter X (s₁ ∪ s₂) a ω = min (hittingAfter X s₁ a ω) (hittingAfter X s₂ a ω) := by
  refine le_antisymm (le_min (hittingAfter_apply_anti X a ω subset_union_left)
    (hittingAfter_apply_anti X a ω subset_union_right)) (le_of_forall_gt fun b hb ↦ ?_)
  cases b with
  | top =>
    rw [lt_top_iff_ne_top]; intro htop
    rw [min_eq_top, hittingAfter_eq_top_iff, hittingAfter_eq_top_iff] at htop
    exact hb.ne_top (hittingAfter_eq_top_iff.mpr fun j hj h ↦ h.elim (htop.1 j hj) (htop.2 j hj))
  | coe d =>
    obtain ⟨j, hj, h | h⟩ := hittingAfter_lt_iff.mp hb
    · exact min_lt_iff.mpr (.inl (hittingAfter_lt_iff.mpr ⟨j, hj, h⟩))
    · exact min_lt_iff.mpr (.inr (hittingAfter_lt_iff.mpr ⟨j, hj, h⟩))

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- First entrance into a union of two sets is the minimum of the first entrances into each set. -/
@[simp] theorem hittingAfter_union (X : ι → Ω → E) (s₁ s₂ : Set E) (a : ι) :
    hittingAfter X (s₁ ∪ s₂) a = min (hittingAfter X s₁ a) (hittingAfter X s₂ a) :=
  funext fun ω ↦ hittingAfter_union_apply X s₁ s₂ a ω

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

/-- Closed-set entrance of an everywhere-continuous process with measurable evaluations is
measurable on the ambient measurable space. -/
theorem measurable_hittingAfter_of_isClosed {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology ι] [CompactIccSpace ι] {mΩ : MeasurableSpace Ω}
    {X : ι → Ω → E} {s : Set E} (hX : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous (X · ω)) (hs : IsClosed s) (a : ι) :
    Measurable (hittingAfter X s a) :=
  let : PseudoMetricSpace E := TopologicalSpace.pseudoMetrizableSpacePseudoMetric E
  (Adapted.isStoppingTime_hittingAfter_of_isClosed (ℱ := Filtration.const ι mΩ le_rfl)
    hX hc hs a).measurable'

/-- Closed-set entrance of an almost-surely continuous process with almost everywhere strongly
measurable evaluations is almost everywhere measurable. -/
theorem aemeasurable_hittingAfter_of_isClosed {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [SecondCountableTopology ι] [CompactIccSpace ι]
    {_ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {s : Set E}
    (hX : ∀ t, AEStronglyMeasurable (X t) P) (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hs : IsClosed s) (a : ι) :
    AEMeasurable (hittingAfter X s a) P := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨Y, hYm, hYc, hYX⟩ := TauCeti.Probability.exists_stronglyMeasurable_continuous_indist hX hc
  exact (measurable_hittingAfter_of_isClosed (fun t ↦ (hYm t).measurable) hYc hs
    a).aemeasurable.congr (hYX.hittingAfter_ae_eq s a)

end MeasureTheory
