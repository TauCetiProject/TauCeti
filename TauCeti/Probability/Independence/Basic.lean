/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independence of families almost surely constant outside a subset

If `f ∘ e` is an independent family on a probability space and every coordinate outside
`Set.range e` is almost surely constant, then `f` is independent. In particular, any family of
random variables that is almost surely constant outside a subsingleton set of indices is
independent. No measurability assumption or restriction on the index types is needed.

## Main statements

* `TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_range`
* `TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_subsingleton`
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (β i)] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A dependent family `f` is independent if `f ∘ e` is independent and every coordinate outside
`Set.range e` is almost surely constant. Neither measurability of unused coordinates nor
nonemptiness of `κ` is required. -/
theorem iIndepFun_of_ae_eq_const_outside_range {κ : Type*} {e : κ → ι} {f : ∀ i, Ω → β i}
    (hindep : iIndepFun (fun k => f (e k)) μ)
    (hf : ∀ i ∉ Set.range e, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  classical
  let g (i : ι) : Ω → β i :=
    if hi : i ∈ Set.range e then f i else fun _ => (hf i hi).choose
  have hfg (i : ι) : f i =ᵐ[μ] g i := by
    dsimp only [g]
    split_ifs with hi
    · exact Filter.EventuallyEq.rfl
    · exact (hf i hi).choose_spec
  suffices hg : iIndepFun g μ from hg.congr fun i => (hfg i).symm
  have hindep_g : iIndepFun (fun k => g (e k)) μ := by
    refine hindep.congr fun k => ?_
    simp only [g, Set.mem_range_self, ↓reduceDIte]
    rfl
  let m (i : ι) : MeasurableSpace Ω := (inferInstance : MeasurableSpace (β i)).comap (g i)
  have hm_bot (i : ι) (hi : i ∉ Set.range e) : m i = ⊥ := by
    have hg : g i = fun _ => (hf i hi).choose := by simp only [g, hi, ↓reduceDIte]
    simp only [m, hg, MeasurableSpace.comap_const]
  rw [iIndepFun_iff]
  intro S f' hf'
  by_cases hzero : ∃ i ∈ S, i ∉ Set.range e ∧ f' i = ∅
  · obtain ⟨i, hi, _, hfi⟩ := hzero
    have hInter : (⋂ j ∈ S, f' j) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω hω => by
        simpa [hfi] using Set.mem_iInter₂.mp hω i hi
    rw [hInter, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hfi, measure_empty])).symm
  · have huniv (i : ι) (hi : i ∈ S) (hri : i ∉ Set.range e) : f' i = Set.univ := by
      have hm := hf' i hi
      rw [show (inferInstance : MeasurableSpace (β i)).comap (g i) = ⊥ from hm_bot i hri,
        MeasurableSpace.measurableSet_bot_iff] at hm
      exact hm.resolve_left fun h0 => hzero ⟨i, hi, hri, h0⟩
    let S₁ : Finset ι := S.filter (· ∈ Set.range e)
    have hInter_eq : (⋂ i ∈ S, f' i) = ⋂ j : S₁, f' j.1 := by
      ext ω
      simp only [Set.mem_iInter, Subtype.forall, S₁, Finset.mem_filter]
      refine ⟨fun h i hi => h i hi.1, fun h i hi => ?_⟩
      by_cases hri : i ∈ Set.range e
      · exact h i ⟨hi, hri⟩
      · rw [huniv i hi hri]
        exact Set.mem_univ ω
    have hprod_eq : ∏ i ∈ S, μ (f' i) = ∏ j : S₁, μ (f' j.1) := by
      rw [Finset.prod_coe_sort S₁ (fun i => μ (f' i))]
      refine (Finset.prod_subset (Finset.filter_subset _ S) fun i hi hni => ?_).symm
      have hri : i ∉ Set.range e := fun hri => hni (Finset.mem_filter.mpr ⟨hi, hri⟩)
      rw [huniv i hi hri, measure_univ]
    let ψ (j : S₁) : κ := (Finset.mem_filter.mp j.2).2.choose
    have hψ (j : S₁) : e (ψ j) = j.1 := (Finset.mem_filter.mp j.2).2.choose_spec
    have hψ_inj : Function.Injective ψ := fun j₁ j₂ h =>
      Subtype.ext (by rw [← hψ j₁, ← hψ j₂, h])
    have hcomap {a b : ι} (hab : a = b) :
        MeasurableSpace.comap (g a) inferInstance = m b := by
      subst hab; rfl
    have hindep_S₁ : iIndep (fun j : S₁ => m j.1) μ := by
      simpa only [Function.comp_def, fun j => hcomap (hψ j)] using hindep_g.iIndep.precomp hψ_inj
    rw [hInter_eq, hprod_eq]
    exact hindep_S₁.meas_iInter fun j => hf' j.1 (Finset.filter_subset _ S j.2)

/-- A family is independent if its coordinates are almost surely constant outside a subsingleton
set of indices. The constants and the exceptional null sets may depend on the coordinate. -/
theorem iIndepFun_of_ae_eq_const_outside_subsingleton {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : s.Subsingleton) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  have : Subsingleton s := hs.coe_sort
  exact iIndepFun_of_ae_eq_const_outside_range (e := (Subtype.val : s → ι))
    iIndepFun.of_subsingleton (by simpa only [Subtype.range_coe] using hf)

end TauCeti.Probability
