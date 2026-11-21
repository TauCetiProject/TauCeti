/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
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
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (β i)] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- An independent restriction remains independent when the other coordinates are almost
surely constant. The constants and the exceptional null sets may depend on the coordinate. -/
theorem _root_.ProbabilityTheory.iIndepFun.of_subtype_of_ae_eq_const
    {f : ∀ i, Ω → β i} {s : Set ι}
    (h : iIndepFun (fun i : s ↦ f i.val) μ)
    (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ ↦ c) : iIndepFun f μ := by
  classical
  have := h.isProbabilityMeasure
  let g (i : ι) : Ω → β i :=
    if hi : i ∈ s then f i else fun _ ↦ (hf i hi).choose
  have hfg (i : ι) : f i =ᵐ[μ] g i := by
    dsimp [g]
    split_ifs with hi
    · exact Filter.EventuallyEq.rfl
    · exact (hf i hi).choose_spec
  suffices hg : iIndepFun g μ from hg.congr (fun i ↦ (hfg i).symm)
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  by_cases hbad : ∃ i ∈ S, ∃ c, g i = (fun _ ↦ c) ∧ c ∉ sets i
  · obtain ⟨i, hi, c, hgi, hci⟩ := hbad
    have hempty : g i ⁻¹' sets i = ∅ := by simp [hgi, hci]
    have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ by
        have := Set.mem_iInter₂.mp hω i hi
        simp only [hempty, Set.mem_empty_iff_false] at this
    rw [hInter, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hempty, measure_empty])).symm
  have hfull (i : ι) (hi : i ∈ S) (hsi : i ∉ s) : g i ⁻¹' sets i = Set.univ := by
    have hg : g i = fun _ ↦ (hf i hsi).choose := by simp [g, hsi]
    have hci : (hf i hsi).choose ∈ sets i := by
      by_contra hn
      exact hbad ⟨i, hi, _, hg, hn⟩
    simp [hg, hci]
  let T := S.subtype (· ∈ s)
  have h' := h.measure_inter_preimage_eq_mul T (sets := fun i ↦ sets i)
    (fun i hi ↦ hs i (Finset.mem_subtype.mp hi))
  have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = ⋂ j ∈ T, f j.val ⁻¹' sets j := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    refine ⟨fun hw i hi ↦ ?_, fun hw i hi ↦ ?_⟩
    · simpa [g, i.property] using hw i (Finset.mem_subtype.mp hi)
    · by_cases his : i ∈ s
      · simpa [g, his] using hw ⟨i, his⟩ (Finset.mem_subtype.mpr hi)
      · have hmem : ω ∈ g i ⁻¹' sets i := (hfull i hi his).symm ▸ Set.mem_univ ω
        exact hmem
  rw [hInter, h']
  calc
    _ = ∏ j ∈ S.filter (· ∈ s), μ (f j ⁻¹' sets j) := Finset.prod_subtype_eq_prod_filter _
    _ = ∏ j ∈ S.filter (· ∈ s), μ (g j ⁻¹' sets j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [g, (Finset.mem_filter.mp hj).2]
    _ = _ := Finset.prod_subset (Finset.filter_subset _ _) fun j hj hjs ↦ by
      rw [hfull j hj (fun hjs' ↦ hjs (Finset.mem_filter.mpr ⟨hj, hjs'⟩)), measure_univ]

/-- A family is independent if its coordinates are almost surely constant outside a subsingleton
set of indices. The constants and the exceptional null sets may depend on the coordinate. -/
theorem iIndepFun_of_ae_eq_const_outside_subsingleton {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : s.Subsingleton) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  let : Subsingleton s := ⟨fun i j ↦ Subtype.ext (hs i.property j.property)⟩
  exact (iIndepFun.of_subsingleton (f := fun i : s ↦ f i.val)).of_subtype_of_ae_eq_const hf

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
