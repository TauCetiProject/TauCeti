/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Authors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import TauCeti.Probability.Process.HittingTime.Basic
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Probability.Process.Version
import TauCeti.Topology.Order.LeftRight

/-!
# Closed-set hitting times of continuous and right-continuous processes

For right-continuous paths (and in particular continuous paths), the first entrance into a closed
set is attained whenever it is finite, and is strictly after the starting time whenever the initial
value lies outside the target. Hitting a clopen set along an everywhere right-continuous adapted
process on a densely ordered separable time axis is a stopping time on any raw filtration, without
compact intervals, right continuity, or completion assumptions. When a natural-valued
right-continuous path starts at or below `c` and jumps by at most one from earlier times, each
finite closed-ray hit is attained with exact value `c` and strictly precedes the next level hit.

For general closed targets of continuous paths on a compact time interval, entrance is equivalent
to the minimum distance to the target being zero. Measuring that minimum on a second-countable
compact-interval time axis likewise gives a stopping time on the original filtration, without right
continuity or completion assumptions, whereas ambient almost-everywhere measurability holds for
almost-surely continuous processes via an indistinguishable continuous version. For ordered-valued
continuous paths, first entrance into a singleton coincides with first entrance into the
corresponding closed half-line when the initial state lies on the opposite side, and a path
starting in `[a, b]` remains in `[a, b]` up to its first exit from `(a, b)` (so the stopped path
stays in `[a, b]` thereafter) and hits `{a, b}` when that exit is finite.

Without topology or path-continuity hypotheses, post-composition and negation (including negated
shifted processes over a `SubtractionCommMonoid`) pull target sets back through preimages,
indistinguishable processes have a.e. equal hitting times, and entrance into a union of two sets
is the minimum of the two entrances (on a conditionally complete linear order).

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, Chapter 1, §2.
* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §§1 and 3.
-/

public section

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.Indistinguishable

/-- Indistinguishable processes have almost everywhere equal first hitting times of any set after
any starting time. -/
theorem hittingAfter_ae_eq {ι Ω E : Type*} [Preorder ι] [InfSet ι] {_ : MeasurableSpace Ω}
    {P : Measure Ω} {X Y : ι → Ω → E} (h : X ≡ᵐ[P] Y) (s : Set E) (a : ι) :
    hittingAfter X s a =ᵐ[P] hittingAfter Y s a := by
  classical exact h.mono fun _ hω ↦ by simp only [hittingAfter_def, hω]

end ProbabilityTheory.Indistinguishable

namespace MeasureTheory

/-- First entrance of `-X` into `s` equals first entrance of `X` into `Neg.neg ⁻¹' s`. -/
theorem hittingAfter_neg {Ω ι E : Type*} [Preorder ι] [InfSet ι] [Neg E]
    (X : ι → Ω → E) (s : Set E) (a : ι) :
    hittingAfter (-X) s a = hittingAfter X (Neg.neg ⁻¹' s) a :=
  Pi.neg_def (f := X) ▸ hittingAfter_comp X Neg.neg s a

/-- First entrance of `-x + (-X)` into `s` equals that of `x + X` into `Neg.neg ⁻¹' s`. -/
theorem hittingAfter_neg_const_add_neg {Ω ι E : Type*} [Preorder ι] [InfSet ι]
    [SubtractionCommMonoid E] (x : E) (X : ι → Ω → E) (s : Set E) (a : ι) :
    hittingAfter (fun t ω ↦ -x + (-X) t ω) s a =
      hittingAfter (fun t ω ↦ x + X t ω) (Neg.neg ⁻¹' s) a := by
  simp only [Pi.neg_apply, ← neg_add]; exact hittingAfter_comp (fun t ω ↦ x + X t ω) Neg.neg s a

end MeasureTheory

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
  · have hA_sub : A ⊆ Ioi u₀ := fun v hv ↦
      lt_of_le_of_ne (csInf_le hbdd hv) fun h ↦ hmem (h ▸ hv)
    have : (𝓝[A] u₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (csInf_mem_closure hne hbdd)
    exact hs.mem_of_tendsto ((hX u₀).mono_left (nhdsWithin_mono u₀ hA_sub))
      (eventually_nhdsWithin_of_forall fun _ hv ↦ hv.2)

/-- At a finite closed-set entrance of a right-continuous path, the path lies in the target set. -/
theorem hittingAfter_mem_set_of_isRightContinuous_of_ne_top (hs : IsClosed s)
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

/-- If a natural-valued right-continuous path starts at most at `c` (`X a ω ≤ c`) and jumps by at
most one from strictly earlier times in `[a, t)`, then any finite hit of `Set.Ici c` strictly
precedes the hit of `Set.Ici (c + 1)`. -/
theorem hittingAfter_Ici_lt_hittingAfter_Ici_add_one_of_le_add_one {X : ι → Ω → ℕ}
    {a : ι} {ω : Ω} {c : ℕ}
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
    obtain ⟨u, hu, hus⟩ :=
      (isClosed_Ici.hittingAfter_le_iff_of_isRightContinuous hX.isRightContinuous).mp ht.le
    obtain ⟨v, hv, hvC⟩ := intermediate_value_Icc hu.1 hX.continuousOn ⟨hstart, hus⟩
    exact (MeasureTheory.hittingAfter_le_of_mem hv.1 hvC).trans (WithTop.coe_le_coe.mpr
      (hv.2.trans hu.2))

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

/-- Stopping a continuous ordered-valued path at its first exit from `(a, b)` after `u` keeps it in
`[a, b]` at every time `t ≥ u`, provided it starts in `[a, b]` at `u`. -/
theorem Continuous.stoppedProcess_hittingAfter_compl_Ioo_mem_Icc [Nonempty ι] {u t : ι} {a b : β}
    (hX : Continuous (X · ω)) (hut : u ≤ t) (hstart : X u ω ∈ Icc a b) :
    MeasureTheory.stoppedProcess X (MeasureTheory.hittingAfter X (Ioo a b)ᶜ u) t ω ∈ Icc a b := by
  by_cases ht : (t : WithTop ι) ≤ MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω
  · rw [MeasureTheory.stoppedProcess_eq_of_le ht]
    exact hX.mem_Icc_of_le_hittingAfter_compl_Ioo hut hstart ht
  · rw [MeasureTheory.stoppedProcess_eq_of_ge (le_of_not_ge ht)]
    cases hs : MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω with
    | top => exact absurd (hs ▸ le_of_not_ge ht) (not_le.mpr (WithTop.coe_lt_top t))
    | coe s =>
      simpa only [WithTop.untopA, WithTop.untopD_coe] using hX.mem_Icc_of_le_hittingAfter_compl_Ioo
        (WithTop.coe_le_coe.mp (hs ▸ MeasureTheory.le_hittingAfter ω)) hstart hs.symm.le

/-- A continuous ordered-valued path starting in `[a, b]` evaluates to `a` or `b` at any finite
first exit time from `(a, b)`. -/
theorem Continuous.eval_untopA_hittingAfter_compl_Ioo_eq_or_eq [Nonempty ι] {u : ι} {a b : β}
    (hX : Continuous (X · ω)) (hstart : X u ω ∈ Icc a b)
    (hfin : MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω ≠ ⊤) :
    X (MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω).untopA ω = a ∨
      X (MeasureTheory.hittingAfter X (Ioo a b)ᶜ u ω).untopA ω = b := by
  obtain ⟨t, ht, hut, hts⟩ :=
    isOpen_Ioo.isClosed_compl.exists_hittingAfter_eq_of_isRightContinuous hX.isRightContinuous hfin
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
    rw [lt_top_iff_ne_top]; intro htop; rw [min_eq_top] at htop
    rw [hittingAfter_eq_top_iff, hittingAfter_eq_top_iff] at htop
    exact hb.ne_top (hittingAfter_eq_top_iff.mpr fun j hj h ↦ h.elim (htop.1 j hj) (htop.2 j hj))
  | coe d =>
    rcases hittingAfter_lt_iff.mp hb with ⟨j, hj, h | h⟩
    · exact min_lt_iff.mpr (.inl (hittingAfter_lt_iff.mpr ⟨j, hj, h⟩))
    · exact min_lt_iff.mpr (.inr (hittingAfter_lt_iff.mpr ⟨j, hj, h⟩))

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- First entrance into a union of two sets is the minimum of the first entrances into each set. -/
@[simp] theorem hittingAfter_union (X : ι → Ω → E) (s₁ s₂ : Set E) (a : ι) :
    hittingAfter X (s₁ ∪ s₂) a = min (hittingAfter X s₁ a) (hittingAfter X s₂ a) :=
  funext fun ω ↦ hittingAfter_union_apply X s₁ s₂ a ω

/-- First entrance into a clopen set `s` by an adapted process with everywhere right-continuous
paths on a densely ordered separable time axis is a stopping time on any raw filtration. Neither
compact intervals, right-continuity of the filtration, nor completeness is required. -/
theorem Adapted.isStoppingTime_hittingAfter_of_isClopen_of_isRightContinuous
    [DenselyOrdered ι] [TopologicalSpace.SeparableSpace ι]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {s : Set E}
    (hX : Adapted ℱ X) (hrc : ∀ ω, IsRightContinuous (X · ω)) (hs : IsClopen s) (a : ι) :
    IsStoppingTime ℱ (hittingAfter X s a) := by
  have : Nonempty ι := ⟨a⟩
  let q : ℕ → ι := TopologicalSpace.denseSeq ι
  have hdense : DenseRange q := TopologicalSpace.denseRange_denseSeq ι
  intro t
  by_cases hat : a ≤ t
  · have heq : {ω | hittingAfter X s a ω ≤ t} =
        X t ⁻¹' s ∪ ⋃ (n : ℕ) (_ : q n ∈ Icc a t), X (q n) ⁻¹' s := by
      ext ω
      simp only [mem_ofPred_eq, hs.isClosed.hittingAfter_le_iff_of_isRightContinuous (hrc ω),
        mem_union, mem_preimage, mem_iUnion, exists_prop]
      simpa only [mem_range, exists_exists_eq_and] using
        Dense.exists_mem_Icc_apply_mem_iff_of_isOpen hdense hat (fun u _ ↦ hrc ω u) hs.isOpen
    rw [heq]
    exact (hX t hs.isOpen.measurableSet).union
      (.iUnion fun n ↦ .iUnion fun hqn ↦
        ((hX (q n)).mono (ℱ.mono hqn.2) le_rfl) hs.isOpen.measurableSet)
  · have heq : {ω | hittingAfter X s a ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, hs.isClosed.hittingAfter_le_iff_of_isRightContinuous (hrc ω),
        mem_empty_iff_false, iff_false, not_exists, not_and]
      exact fun u hu _ ↦ hat (hu.1.trans hu.2)
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

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
      continuous_infEDist.comp ((hc ω).comp continuous_subtypeVal)
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
    rw [mem_ofPred_eq, hs.hittingAfter_le_iff_of_isRightContinuous (hc ω).isRightContinuous]
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
      simp only [mem_ofPred_eq,
        hs.hittingAfter_le_iff_of_isRightContinuous (hc ω).isRightContinuous,
        mem_empty_iff_false, iff_false, not_exists, not_and]
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
