/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independence of families almost surely constant outside a subset

A family `f` is independent if `f ∘ e` is independent and every coordinate outside `Set.range e` is
a.s. constant (`TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_range`), specializing to
`TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_subsingleton`.
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
