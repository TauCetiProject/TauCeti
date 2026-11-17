/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Basic independence lemmas

A dependent family of random variables is independent if all but at most one coordinate are
almost surely constant. No measurability assumption or restriction on the index type is needed.

Independence of a σ-algebra pulled back along a map from another σ-algebra is also invariant
under almost-everywhere equality of the map (`indep_comap_congr_left`, `indep_comap_congr_right`).
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

section Comap

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Independence of a comapped σ-algebra on the left from another σ-algebra is invariant under
almost-everywhere equality of the map. -/
theorem indep_comap_congr_left {m : MeasurableSpace Ω} {mα : MeasurableSpace α}
    {X Y : Ω → α} (hXY : X =ᵐ[μ] Y) :
    Indep (mα.comap X) m μ ↔ Indep (mα.comap Y) m μ := by
  have h {f g : Ω → α} (hfg : f =ᵐ[μ] g) (hf : Indep (mα.comap f) m μ) :
      Indep (mα.comap g) m μ := by
    have hi : @IndepFun Ω α Ω mΩ mα m f id μ := by
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hf
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hi.congr hfg .rfl
  exact ⟨h hXY, h hXY.symm⟩

/-- Independence of a σ-algebra from a comapped σ-algebra on the right is invariant under
almost-everywhere equality of the map. -/
theorem indep_comap_congr_right {m : MeasurableSpace Ω} {mα : MeasurableSpace α}
    {X Y : Ω → α} (hXY : X =ᵐ[μ] Y) :
    Indep m (mα.comap X) μ ↔ Indep m (mα.comap Y) μ :=
  ⟨fun h ↦ ((indep_comap_congr_left hXY).1 h.symm).symm,
    fun h ↦ ((indep_comap_congr_left hXY).2 h.symm).symm⟩

end Comap

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
