/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independence of almost surely constant coordinates

A dependent family of random variables is independent if and only if its restriction to a set `s`
of coordinates is independent, whenever all coordinates outside `s` are almost surely constant. In
particular, a family on a probability space is independent if all coordinates outside a subsingleton
set are almost surely constant. No measurability assumption or restriction on the index type is
needed.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (β i)] {μ : Measure Ω}

/-- A family of random variables is independent if its restriction to a set `s` of indices is
independent and all coordinates outside `s` are almost surely constant. The constants and the
exceptional null sets may depend on the coordinate, and no measurability assumption is needed. -/
theorem iIndepFun_of_ae_eq_const_outside {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : iIndepFun (fun i : s => f i) μ) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  have : IsProbabilityMeasure μ := hs.isProbabilityMeasure
  classical
  let g (i : ι) : Ω → β i :=
    if hi : i ∈ s then f i else fun _ => (hf i hi).choose
  have hfg (i : ι) : f i =ᵐ[μ] g i := by
    dsimp [g]
    split_ifs with hi
    · exact Filter.EventuallyEq.rfl
    · exact (hf i hi).choose_spec
  suffices hg : iIndepFun g μ from hg.congr (fun i => (hfg i).symm)
  have hgs : iIndepFun (fun i : s => g i) μ :=
    hs.congr fun i => .of_forall fun _ => by simp [g, i.2]
  have hc (i : ι) (hi : i ∉ s) : ∃ c, g i = fun _ => c :=
    ⟨(hf i hi).choose, by simp [g, hi]⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hmeas
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
    let S' : Finset s := S.subtype (· ∈ s)
    have hInter : (⋂ j ∈ S, g j ⁻¹' sets j) = ⋂ j ∈ S', g j.1 ⁻¹' sets j.1 := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_subtype, S']
      refine ⟨fun hω j hj => hω j.1 hj, fun hω j hj => ?_⟩
      by_cases hjs : j ∈ s
      · exact hω ⟨j, hjs⟩ hj
      · rw [hfull j hj hjs]
        exact Set.mem_univ ω
    have hind := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hgs) S' (sets := fun j => sets j.1)
      fun j hj => hmeas j.1 (Finset.mem_subtype.mp hj)
    rw [hInter, hind]
    dsimp only [S']
    rw [Finset.prod_subtype_eq_prod_filter (fun j => μ (g j ⁻¹' sets j)), Finset.prod_filter]
    refine Finset.prod_congr rfl fun j hj => ?_
    split_ifs with hjs
    · rfl
    · rw [hfull j hj hjs, measure_univ]

/-- When all coordinates outside `s` are almost surely constant, independence of the full family is
equivalent to independence of its restriction to `s`. -/
theorem iIndepFun_iff_of_ae_eq_const_outside {f : ∀ i, Ω → β i} {s : Set ι}
    (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ ↔ iIndepFun (fun i : s => f i) μ :=
  ⟨fun h => h.precomp Subtype.val_injective, fun h => iIndepFun_of_ae_eq_const_outside h hf⟩

/-- Extending an independent `{i // p i}`-indexed family by `0` outside `p` produces an independent
family on the whole index type. -/
theorem iIndepFun_ite_zero {f : ∀ i, Ω → β i} [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p]
    (hp : iIndepFun (fun i : {i // p i} => f i) μ) :
    iIndepFun (fun i => if p i then f i else 0) μ :=
  iIndepFun_of_ae_eq_const_outside (s := {i | p i})
    (hp.congr fun i => .of_forall fun _ => by simp [show p i.1 from i.2])
    fun i hi => ⟨0, .of_forall fun _ => by simp [show ¬ p i from hi]⟩

/-- A family on a probability space is independent if its coordinates are almost surely constant
outside a subsingleton set of indices. The constants and the exceptional null sets may depend on
the coordinate. -/
theorem iIndepFun_of_ae_eq_const_outside_subsingleton [IsProbabilityMeasure μ]
    {f : ∀ i, Ω → β i} {s : Set ι}
    (hs : s.Subsingleton) (hf : ∀ i ∉ s, ∃ c, f i =ᵐ[μ] fun _ => c) :
    iIndepFun f μ := by
  have := hs.coe_sort
  exact iIndepFun_of_ae_eq_const_outside .of_subsingleton hf

end TauCeti.Probability
