/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Basic independence lemmas

* `TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_subsingleton`: a dependent family of random
  variables is independent if all but at most one coordinate are almost surely constant.
* `ProbabilityTheory.iIndepFun.indepFun_finsetProd_of_notMem₀_on` and
  `ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem₀_on`: Finset-restricted variants of
  Mathlib's `indepFun_finsetProd_of_notMem₀` / `indepFun_finsetSum_of_notMem₀` requiring a.e.
  measurability only on `s` and at the excluded index `i`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (β i)] {μ : Measure Ω} [IsProbabilityMeasure μ]

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

/-- Finset-restricted variant of `ProbabilityTheory.iIndepFun.indepFun_finsetProd_of_notMem₀`:
for an independent family `f` in a commutative monoid with jointly measurable multiplication,
`∏ j ∈ s, f j` and `f i` are independent when `i ∉ s`, assuming a.e. measurability only on `s`
and at `i`. -/
@[to_additive /-- Finset-restricted variant of
`ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem₀`: for an independent family `f` in a
commutative additive monoid with jointly measurable addition, `∑ j ∈ s, f j` and `f i` are
independent when `i ∉ s`, assuming a.e. measurability only on `s` and at `i`. -/]
theorem iIndepFun.indepFun_finsetProd_of_notMem₀_on {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [CommMonoid β] [MeasurableMul₂ β] {μ : Measure Ω}
    {f : ι → Ω → β} (hf_indep : iIndepFun f μ) {s : Finset ι} {i : ι} (hi : i ∉ s)
    (hf_meas : ∀ j ∈ s, AEMeasurable (f j) μ) (hf_i : AEMeasurable (f i) μ) :
    IndepFun (∏ j ∈ s, f j) (f i) μ := by
  classical
  let t : Finset ↥(insert i s) := s.attach.map
    ⟨fun k ↦ ⟨k.1, Finset.mem_insert_of_mem k.2⟩,
      fun _ _ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)⟩
  have hi' : (⟨i, Finset.mem_insert_self i s⟩ : ↥(insert i s)) ∉ t := by
    simp only [t, Finset.mem_map, Finset.mem_attach, true_and, Subtype.ext_iff, not_exists]
    exact fun k hk ↦ hi (hk ▸ k.2)
  have hmeas_ins : ∀ k : ↥(insert i s), AEMeasurable (f k.1) μ := fun k ↦ by
    rcases Finset.mem_insert.1 k.2 with hk | hk
    · rw [hk]; exact hf_i
    · exact hf_meas k.1 hk
  have h := (hf_indep.precomp Subtype.val_injective).indepFun_finsetProd_of_notMem₀ hmeas_ins hi'
  rwa [show (∏ k ∈ t, f k.1) = ∏ k ∈ s, f k by
    simp only [t, Finset.prod_map]
    exact Finset.prod_attach s f] at h

end ProbabilityTheory
