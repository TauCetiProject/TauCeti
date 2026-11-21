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

A dependent family of random variables is independent if `f ∘ e` is independent and every
coordinate outside `Set.range e` is almost surely constant
(`TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_range`), specializing to
`TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_subsingleton`.

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

/-- A dependent family `f` is independent if `f ∘ e` is independent and every coordinate outside
`Set.range e` is almost surely constant. -/
theorem iIndepFun_of_ae_eq_const_outside_range {κ : Type*} {e : κ → ι} {f : ∀ i, Ω → β i}
    (hindep : iIndepFun (fun k => f (e k)) μ)
    (hf : ∀ i ∉ Set.range e, ∃ c, f i =ᵐ[μ] fun _ => c) : iIndepFun f μ := by
  classical
  let g (i : ι) : Ω → β i := if hi : i ∈ Set.range e then f i else fun _ => (hf i hi).choose
  suffices hg : iIndepFun g μ from hg.congr fun i => by
    dsimp only [g]; split_ifs with hi; exacts [.rfl, (hf i hi).choose_spec.symm]
  have hindep_g : iIndepFun (fun k => g (e k)) μ :=
    hindep.congr fun k => by simp only [g, Set.mem_range_self, ↓reduceDIte]; rfl
  rw [iIndepFun_iff]; intro S f' hf'
  by_cases hzero : ∃ i ∈ S, i ∉ Set.range e ∧ f' i = ∅
  · obtain ⟨i, hi, _, hfi⟩ := hzero
    have hempty : (⋂ j ∈ S, f' j) = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun ω hω => by
      simpa [hfi] using Set.mem_iInter₂.mp hω i hi
    rw [hempty, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hfi, measure_empty])).symm
  · have huniv (i : ι) (hi : i ∈ S) (hri : i ∉ Set.range e) : f' i = Set.univ := by
      have hm := hf' i hi
      have hgi : g i = fun _ => (hf i hri).choose := by simp only [g, hri, ↓reduceDIte]
      rw [hgi, MeasurableSpace.comap_const, MeasurableSpace.measurableSet_bot_iff] at hm
      exact hm.resolve_left fun h0 => hzero ⟨i, hi, hri, h0⟩
    let S₁ : Finset ι := S.filter (· ∈ Set.range e)
    let ψ (j : S₁) : κ := (Finset.mem_filter.mp j.2).2.choose
    have hψ (j : S₁) : e (ψ j) = j.1 := (Finset.mem_filter.mp j.2).2.choose_spec
    have hcomap {a b : ι} (hab : a = b) :
        MeasurableSpace.comap (g a) inferInstance = MeasurableSpace.comap (g b) inferInstance := by
      subst hab; rfl
    have hindep_S₁ : iIndep (fun j : S₁ => MeasurableSpace.comap (g j.1) inferInstance) μ := by
      simpa only [Function.comp_def, fun j => hcomap (hψ j)] using
        hindep_g.iIndep.precomp (g := ψ) fun a b h => Subtype.ext (by rw [← hψ a, ← hψ b, h])
    have hinter : (⋂ i ∈ S, f' i) = ⋂ j : S₁, f' j.1 := by
      ext ω; simp only [Set.mem_iInter, Subtype.forall, S₁, Finset.mem_filter]
      exact ⟨fun h i hi => h i hi.1, fun h i hi => if hri : i ∈ Set.range e then
        h i ⟨hi, hri⟩ else by rw [huniv i hi hri]; trivial⟩
    have hprod : ∏ i ∈ S, μ (f' i) = ∏ j : S₁, μ (f' j.1) := by
      rw [Finset.prod_coe_sort S₁ (fun i => μ (f' i))]
      exact (Finset.prod_subset (Finset.filter_subset _ S) fun i hi hni => by
        rw [huniv i hi fun hri => hni (Finset.mem_filter.mpr ⟨hi, hri⟩), measure_univ]).symm
    rw [hinter, hprod]
    exact hindep_S₁.meas_iInter fun j => hf' j.1 (Finset.filter_subset _ S j.2)

/-- A family is independent if its coordinates are almost surely constant outside a subsingleton
set of indices. The constants and the exceptional null sets may depend on the coordinate. -/
theorem iIndepFun_of_ae_eq_const_outside_subsingleton {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : s.Subsingleton) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) : iIndepFun f μ := by
  have : Subsingleton s := hs.coe_sort
  exact iIndepFun_of_ae_eq_const_outside_range (e := (Subtype.val : s → ι))
    iIndepFun.of_subsingleton (by simpa only [Subtype.range_coe] using hf)

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
