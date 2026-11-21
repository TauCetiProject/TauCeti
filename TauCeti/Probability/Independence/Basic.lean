/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Powerset
import TauCeti.Probability.HasLaw

/-!
# Basic criteria for independence

A dependent family of random variables is independent if all but at most one coordinate are
almost surely constant; no measurability assumption or restriction on the index type is needed
(`TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_subsingleton`).

Under a zero or probability measure `P`, a random variable `Z` is independent of a sub-σ-algebra `m`
whenever restricting `P` to every `m`-measurable event `A` (or `A ∩ F` for an almost-surely holding
event `F`) gives `Z` the scalar-multiple law `P A • ν` (respectively `P (A ∩ F) • ν`): see
`ProbabilityTheory.indep_comap_of_forall_hasLaw_restrict` and
`ProbabilityTheory.indep_comap_of_forall_hasLaw_restrict_inter`.

An independent, identically distributed family admits a measurable version agreeing almost
everywhere at each index, preserving independence and identical distribution
(`ProbabilityTheory.iIndepFun.exists_measurable_ae_eq_of_identDistrib`).

Independence within rows also gives a union bound for row counts. For a finite array of events
whose rows consist of independent events of measure at most `p`, the measure that some row
contains at least `q` occurring events is at most `p ^ q` times the sum over rows of the number of
`q`-element subsets of the row indices (`TauCeti.Probability.measure_exists_le_card_filter_mem_le`).
This bound needs no probability-measure assumption.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (β i)] {μ : Measure Ω}

open scoped Classical in
/-- For a finite array of events, each row consisting of independent events with measures at
most `p`, the measure that some row contains at least `q` occurring events is bounded by
`p ^ q` times the sum, over rows, of the number of `q`-element subsets of entry indices
in that row. -/
theorem measure_exists_le_card_filter_mem_le {κ : ι → Type*} [Fintype ι]
    [∀ i, Fintype (κ i)] (E : (i : ι) → κ i → Set Ω) (hE : ∀ i, iIndepSet (E i) μ)
    {p : ℝ≥0∞} (hp : ∀ i j, μ (E i j) ≤ p) (q : ℕ) :
    μ {ω | ∃ i, q ≤ (Finset.univ.filter fun j ↦ ω ∈ E i j).card} ≤
      ∑ i, ((Fintype.card (κ i)).choose q : ℝ≥0∞) * p ^ q := by
  let U (i : ι) := ⋃ S ∈ (Finset.univ : Finset (κ i)).powersetCard q, ⋂ j ∈ S, E i j
  have hcover : {ω | ∃ i, q ≤ (Finset.univ.filter fun j ↦ ω ∈ E i j).card} ⊆ ⋃ i, U i := by
    rintro ω ⟨i, hi⟩
    obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hi
    refine mem_iUnion.2 ⟨i, mem_iUnion₂.2 ⟨S, Finset.mem_powersetCard.2 ⟨
      Finset.subset_univ _, hcard⟩, ?_⟩⟩
    exact mem_iInter₂.2 fun j hj ↦ (Finset.mem_filter.1 (hsub hj)).2
  refine ((measure_mono hcover).trans (measure_iUnion_fintype_le μ U)).trans ?_
  refine Finset.sum_le_sum fun i _ ↦ (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (κ i)).powersetCard q, p ^ q := by
      refine Finset.sum_le_sum fun S hS ↦ ?_
      rw [(hE i).meas_biInter, ← (Finset.mem_powersetCard.1 hS).2, ← Finset.prod_const]
      exact Finset.prod_le_prod fun j _ ↦ hp i j
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

variable [IsProbabilityMeasure μ]

/-- A family is independent if its coordinates are almost surely constant outside a subsingleton
set of indices. The constants and the exceptional null sets may depend on the coordinate. -/
theorem iIndepFun_of_ae_eq_const_outside_subsingleton {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : s.Subsingleton) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  classical
  let g (i : ι) : Ω → β i :=
    if hi : i ∈ s then f i else fun _ => (hf i hi).choose
  have hfg (i : ι) : f i =ᵐ[μ] g i := by
    dsimp [g]
    split_ifs with hi
    · exact Filter.EventuallyEq.rfl
    · exact (hf i hi).choose_spec
  suffices hg : iIndepFun g μ from hg.congr (fun i => (hfg i).symm)
  have hc (i : ι) (hi : i ∉ s) : ∃ c, g i = fun _ => c :=
    ⟨(hf i hi).choose, by simp [g, hi]⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases hbad : ∃ i ∈ S, ∃ c, g i = (fun _ => c) ∧ c ∉ sets i
  · obtain ⟨i, hi, c, hgi, hci⟩ := hbad
    have hempty : g i ⁻¹' sets i = ∅ := by simp [hgi, hci]
    have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω hω => by
        have := Set.mem_iInter₂.mp hω i hi
        simp only [hempty, Set.mem_empty_iff_false] at this
    rw [hInter, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hempty, measure_empty])).symm
  · have hfull (i : ι) (hi : i ∈ S) (hsi : i ∉ s) : g i ⁻¹' sets i = Set.univ := by
      obtain ⟨c, hgi⟩ := hc i hsi
      have hci : c ∈ sets i := by by_contra h; exact hbad ⟨i, hi, c, hgi, h⟩
      simp [hgi, hci]
    by_cases hactive : ∃ i ∈ S, i ∈ s
    · obtain ⟨i, hi, hsi⟩ := hactive
      have hother (j : ι) (hj : j ∈ S) (hji : j ≠ i) : g j ⁻¹' sets j = Set.univ :=
        hfull j hj (fun hsj => hji (hs hsj hsi))
      have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = g i ⁻¹' sets i := by
        ext ω
        simp only [Set.mem_iInter]
        constructor
        · exact fun hω => hω i hi
        · intro hω j hj
          by_cases hji : j = i
          · subst j
            exact hω
          · rw [hother j hj hji]
            exact Set.mem_univ ω
      rw [hInter, Finset.prod_eq_single_of_mem i hi]
      intro j hj hji
      rw [hother j hj hji, measure_univ]
    · have hfull' (i : ι) (hi : i ∈ S) : g i ⁻¹' sets i = Set.univ :=
        hfull i hi (fun hsi => hactive ⟨i, hi, hsi⟩)
      have hInter : (⋂ i ∈ S, g i ⁻¹' sets i) = Set.univ := by
        exact Set.eq_univ_iff_forall.mpr fun ω => Set.mem_iInter₂.mpr fun i hi => by
          rw [hfull' i hi]
          exact Set.mem_univ ω
      rw [hInter, measure_univ]
      exact (Finset.prod_eq_one fun i hi => by rw [hfull' i hi, measure_univ]).symm

end TauCeti.Probability

namespace ProbabilityTheory

open Set

variable {Ω β : Type*} [MeasurableSpace β]

/-- Under a zero or probability measure `P`, if restricting `P` to every event `A` of a
sub-σ-algebra `m` gives `Z` the law `P A • ν`, then `Z` is independent of `m`. Measurability of `Z`
in the ambient σ-algebra is not required beyond the almost-everywhere measurability carried by
`HasLaw`. -/
theorem indep_comap_of_forall_hasLaw_restrict {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsZeroOrProbabilityMeasure P] {ν : Measure β} {Z : Ω → β} (hm : m ≤ mΩ)
    (h : ∀ A, MeasurableSet[m] A → HasLaw Z (P A • ν) (P.restrict A)) :
    Indep (.comap Z inferInstance) m P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP
  · simp [Indep_iff]
  have hZ : HasLaw Z ν P := by simpa using h univ .univ
  rw [Indep_iff]
  rintro _ A ⟨C, hC, rfl⟩ hA
  have hZA := h A hA
  calc
    P (Z ⁻¹' C ∩ A) = P.restrict A (Z ⁻¹' C) := (Measure.restrict_apply' (hm A hA)).symm
    _ = Measure.map Z (P.restrict A) C :=
      (Measure.map_apply_of_aemeasurable hZA.aemeasurable hC).symm
    _ = (P A • ν) C := by rw [hZA.map_eq]
    _ = ν C * P A := by simp [mul_comm]
    _ = Measure.map Z P C * P A := by rw [hZ.map_eq]
    _ = P (Z ⁻¹' C) * P A := by rw [Measure.map_apply_of_aemeasurable hZ.aemeasurable hC]

/-- Under a zero or probability measure, restricted scalar-multiple laws on `A ∩ F` for every
`m`-event `A` and an almost-surely holding event `F` imply that `Z` is independent of `m`. -/
theorem indep_comap_of_forall_hasLaw_restrict_inter {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsZeroOrProbabilityMeasure P] {ν : Measure β} {Z : Ω → β} {F : Set Ω} (hm : m ≤ mΩ)
    (hF : ∀ᵐ ω ∂P, ω ∈ F)
    (h : ∀ A, MeasurableSet[m] A → HasLaw Z (P (A ∩ F) • ν) (P.restrict (A ∩ F))) :
    Indep (.comap Z inferInstance) m P :=
  indep_comap_of_forall_hasLaw_restrict hm fun A hA ↦ (h A hA).of_restrict_inter_of_ae_mem hF

/-- Every independent, identically distributed family of random variables admits a measurable
version agreeing almost everywhere at each index, preserving independence, identical distribution
within the family, and identical distribution with each original coordinate. -/
theorem iIndepFun.exists_measurable_ae_eq_of_identDistrib {Ω ι α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} {X : ι → Ω → α} {i₀ : ι}
    (hindep : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X i₀) P P) :
    ∃ X' : ι → Ω → α, (∀ i, Measurable (X' i)) ∧ (∀ i, X i =ᵐ[P] X' i) ∧
      iIndepFun X' P ∧ (∀ i, IdentDistrib (X' i) (X' i₀) P P) ∧
      ∀ i, IdentDistrib (X' i) (X i) P P := by
  let X' : ι → Ω → α := fun i ↦ (hid i).aemeasurable_fst.mk (X i)
  have hX'_ae (i : ι) : X i =ᵐ[P] X' i := (hid i).aemeasurable_fst.ae_eq_mk
  refine ⟨X', fun i ↦ (hid i).aemeasurable_fst.measurable_mk, hX'_ae, hindep.congr hX'_ae,
    fun i ↦ ((hid i).aemeasurable_fst.identDistrib_mk.symm.trans (hid i)).trans
      (hid i₀).aemeasurable_fst.identDistrib_mk,
    fun i ↦ (hid i).aemeasurable_fst.identDistrib_mk.symm⟩

end ProbabilityTheory
