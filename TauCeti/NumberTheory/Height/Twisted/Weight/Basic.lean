/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Local weights of subspaces

For a finite family of linear forms `L` and real weights `c`, the local weight of a
subspace `U` is the minimum of `∑ i ∈ s, c i` over the subfamilies whose restrictions
form a basis of `U`'s dual. This is the local input to the weight optimization defining
exceptional subspaces in the quantitative Subspace Theorem.

`localWeightBases` records the eligible index sets, and `localWeight` records the
minimum. If the forms span the ambient dual, an eligible set always exists, including
for the zero subspace. The API gives attainment, the minimum characterization,
monotonicity in the weights, and the effect of adding a constant to every weight.
The forms need not be independent; redundant generating systems are allowed.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative
  Subspace Theorem*, §15, especially (15.1).
-/

public noncomputable section

open Module Submodule Set

namespace TauCeti

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι]

/-- The index sets whose restricted forms are a basis of the dual of `U`. -/
def localWeightBases (L : ι → Module.Dual K V)
    (U : Submodule K V) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun s ↦
    LinearIndependent K (fun i : s ↦ (L i).comp U.subtype) ∧
      span K (range (fun i : s ↦ (L i).comp U.subtype)) = ⊤

/-- Membership in the set of local dual bases. -/
@[simp]
theorem mem_localWeightBases {L : ι → Module.Dual K V} {U : Submodule K V}
    {s : Finset ι} : s ∈ localWeightBases L U ↔
      LinearIndependent K (fun i : s ↦ (L i).comp U.subtype) ∧
        span K (range (fun i : s ↦ (L i).comp U.subtype)) = ⊤ := by
  classical
  simp [localWeightBases]

/-- A restricted dual basis has as many indices as the dimension of the subspace. -/
theorem card_eq_finrank_of_mem_localWeightBases {L : ι → Module.Dual K V}
    {U : Submodule K V} {s : Finset ι}
    (hs : s ∈ localWeightBases L U) : s.card = finrank K U := by
  have h := finrank_span_eq_card (mem_localWeightBases.mp hs).1
  rw [(mem_localWeightBases.mp hs).2, finrank_top, Subspace.dual_finrank_eq] at h
  simpa using h.symm

/-- In finite dimension, independence and the correct cardinality characterize local dual bases. -/
theorem mem_localWeightBases_iff_linearIndependent_card {L : ι → Module.Dual K V}
    {U : Submodule K V} [Module.Finite K U] {s : Finset ι} :
    s ∈ localWeightBases L U ↔
      LinearIndependent K (fun i : s ↦ (L i).comp U.subtype) ∧ s.card = finrank K U := by
  classical
  constructor
  · intro hs
    exact ⟨(mem_localWeightBases.mp hs).1, card_eq_finrank_of_mem_localWeightBases hs⟩
  · rintro ⟨hli, hcard⟩
    refine mem_localWeightBases.mpr ⟨hli, ?_⟩
    apply hli.span_eq_top_of_card_eq_finrank'
    simpa [Subspace.dual_finrank_eq] using hcard

/-- A generating family of ambient forms contains a basis after restriction to any subspace. -/
theorem localWeightBases_nonempty {L : ι → Module.Dual K V}
    (hL : span K (range L) = ⊤) (U : Submodule K V) :
    (localWeightBases L U).Nonempty := by
  classical
  let f : ι → Module.Dual K U := fun i ↦ (L i).comp U.subtype
  have hf : span K (range f) = ⊤ := by
    have heq : range f = U.subtype.dualMap '' range L := by
      exact Set.range_comp U.subtype.dualMap L
    rw [heq, ← LinearMap.map_span, hL, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.dualMap_surjective_of_injective U.injective_subtype
  obtain ⟨b, -, -, hbspan, hbi⟩ := exists_linearIndepOn_extension
    (v := f) (linearIndepOn_empty K f) (Set.empty_subset (Set.univ : Set ι))
  have hb : span K (f '' b) = ⊤ := by
    apply top_unique
    rw [← hf]
    exact span_le.mpr (by simpa using hbspan)
  have hbi' : LinearIndepOn K f (b.toFinset : Set ι) := by
    rwa [Set.coe_toFinset]
  have hb' : span K (range (fun i : b.toFinset ↦ f i)) = ⊤ := by
    have hset : range (fun i : b.toFinset ↦ f i) = f '' (b.toFinset : Set ι) :=
      (Set.image_eq_range _ _).symm
    rwa [hset, Set.coe_toFinset]
  refine ⟨b.toFinset, mem_localWeightBases.mpr ⟨?_, hb'⟩⟩
  simpa only [Finset.coe_sort_coe] using hbi'.linearIndependent

/-- The minimum weight of a restricted dual basis; its value is `0` if there is no such basis. -/
def localWeight (L : ι → Module.Dual K V) (c : ι → ℝ) (U : Submodule K V) : ℝ :=
  sInf ((fun s : Finset ι ↦ ∑ i ∈ s, c i) '' (localWeightBases L U : Set (Finset ι)))

/-- The defining minimum as an infimum of the finite set of basis weights. -/
theorem localWeight_def (L : ι → Module.Dual K V) (c : ι → ℝ) (U : Submodule K V) :
    localWeight L c U =
      sInf ((fun s : Finset ι ↦ ∑ i ∈ s, c i) '' (localWeightBases L U : Set (Finset ι))) :=
  (rfl)

/-- The local weight is zero when there is no restricted dual basis. -/
@[simp]
theorem localWeight_of_localWeightBases_eq_empty {L : ι → Module.Dual K V}
    {c : ι → ℝ} {U : Submodule K V} (h : localWeightBases L U = ∅) :
    localWeight L c U = 0 := by
  simp [localWeight_def, h]

/-- Every eligible dual basis gives an upper bound for the local weight. -/
theorem localWeight_le_sum {L : ι → Module.Dual K V} (c : ι → ℝ) {U : Submodule K V}
    {s : Finset ι} (hs : s ∈ localWeightBases L U) : localWeight L c U ≤ ∑ i ∈ s, c i := by
  exact csInf_le ((localWeightBases L U).finite_toSet.image _).bddBelow ⟨s, hs, rfl⟩

/-- If an eligible dual basis exists, one attains the local weight. -/
theorem exists_localWeight_eq_sum {L : ι → Module.Dual K V} {U : Submodule K V}
    (h : (localWeightBases L U).Nonempty) (c : ι → ℝ) :
    ∃ s ∈ localWeightBases L U, localWeight L c U = ∑ i ∈ s, c i := by
  obtain ⟨s, hs, heq⟩ := (h.to_set.image (fun s : Finset ι ↦ ∑ i ∈ s, c i)).csInf_mem
    ((localWeightBases L U).finite_toSet.image _)
  exact ⟨s, hs, heq.symm⟩

/-- A lower bound for the local weight is exactly a lower bound for every eligible basis weight. -/
theorem le_localWeight_iff {L : ι → Module.Dual K V} {U : Submodule K V}
    (h : (localWeightBases L U).Nonempty) (c : ι → ℝ) (a : ℝ) :
    a ≤ localWeight L c U ↔ ∀ s ∈ localWeightBases L U, a ≤ ∑ i ∈ s, c i := by
  constructor
  · exact fun h s hs ↦ h.trans (localWeight_le_sum c hs)
  · intro ha
    obtain ⟨s, hs, heq⟩ := exists_localWeight_eq_sum h c
    rw [heq]
    exact ha s hs

/-- The local weight is at most `a` exactly when some eligible basis has weight at most `a`. -/
theorem localWeight_le_iff {L : ι → Module.Dual K V} {U : Submodule K V}
    (h : (localWeightBases L U).Nonempty) (c : ι → ℝ) (a : ℝ) :
    localWeight L c U ≤ a ↔ ∃ s ∈ localWeightBases L U, (∑ i ∈ s, c i) ≤ a := by
  constructor
  · intro ha
    obtain ⟨s, hs, heq⟩ := exists_localWeight_eq_sum h c
    exact ⟨s, hs, heq ▸ ha⟩
  · rintro ⟨s, hs, h⟩
    exact (localWeight_le_sum c hs).trans h

/-- Increasing all the weights cannot decrease the local weight. -/
theorem localWeight_mono {L : ι → Module.Dual K V} {U : Submodule K V}
    {c d : ι → ℝ} (hcd : c ≤ d) :
    localWeight L c U ≤ localWeight L d U := by
  classical
  by_cases h : (localWeightBases L U).Nonempty
  · obtain ⟨s, hs, heq⟩ := exists_localWeight_eq_sum h d
    rw [heq]
    exact (localWeight_le_sum c hs).trans (Finset.sum_le_sum fun i _ ↦ hcd i)
  · simp [localWeight_of_localWeightBases_eq_empty (Finset.not_nonempty_iff_eq_empty.mp h)]

/-- Adding a constant to every form weight adds that constant times the subspace dimension. -/
theorem localWeight_add_const {L : ι → Module.Dual K V} {U : Submodule K V}
    (h : (localWeightBases L U).Nonempty) (c : ι → ℝ) (a : ℝ) :
    localWeight L (fun i ↦ c i + a) U = localWeight L c U + finrank K U * a := by
  have hsum (s : Finset ι) (hs : s ∈ localWeightBases L U) :
      (∑ i ∈ s, (c i + a)) = (∑ i ∈ s, c i) + finrank K U * a := by
    simp [Finset.sum_add_distrib, card_eq_finrank_of_mem_localWeightBases hs]
  obtain ⟨s, hs, heq⟩ := exists_localWeight_eq_sum h c
  obtain ⟨t, ht, heq'⟩ := exists_localWeight_eq_sum h (fun i ↦ c i + a)
  apply le_antisymm
  · calc
      _ ≤ ∑ i ∈ s, (c i + a) := localWeight_le_sum _ hs
      _ = _ := by rw [hsum s hs, heq]
  · rw [heq', hsum t ht]
    exact add_le_add (localWeight_le_sum c ht) le_rfl

/-- All local weights belong to a finite set of subset sums, independently of the subspace. -/
theorem finite_range_localWeight (L : ι → Module.Dual K V) (c : ι → ℝ) :
    (range (localWeight L c)).Finite := by
  classical
  refine ((Set.finite_range (fun s : Finset ι ↦ ∑ i ∈ s, c i)).insert 0).subset ?_
  rintro _ ⟨U, rfl⟩
  by_cases h : (localWeightBases L U).Nonempty
  · obtain ⟨s, -, heq⟩ := exists_localWeight_eq_sum h c
    exact Or.inr ⟨s, heq.symm⟩
  · simp [localWeight_of_localWeightBases_eq_empty (Finset.not_nonempty_iff_eq_empty.mp h)]

/-- The empty family is the only local dual basis of the zero subspace. -/
@[simp]
theorem localWeightBases_bot (L : ι → Module.Dual K V) :
    localWeightBases L (⊥ : Submodule K V) = {∅} := by
  classical
  ext s
  simp only [mem_localWeightBases_iff_linearIndependent_card, finrank_bot,
    Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · exact And.right
  · rintro rfl
    exact ⟨linearIndependent_empty_type, rfl⟩

/-- The zero subspace has local weight zero. -/
@[simp]
theorem localWeight_bot (L : ι → Module.Dual K V) (c : ι → ℝ) :
    localWeight L c (⊥ : Submodule K V) = 0 := by
  simp [localWeight, localWeightBases_bot]

/-- Zero form weights give zero local weight, even when the forms do not span. -/
@[simp]
theorem localWeight_zero (L : ι → Module.Dual K V) (U : Submodule K V) :
    localWeight L 0 U = 0 := by
  classical
  by_cases h : (localWeightBases L U).Nonempty
  · have himage : (fun s : Finset ι ↦ ∑ i ∈ s, (0 : ι → ℝ) i) ''
        (localWeightBases L U : Set (Finset ι)) = {0} := by
      simp [h.to_set]
    rw [localWeight_def, himage, csInf_singleton]
  · exact localWeight_of_localWeightBases_eq_empty (Finset.not_nonempty_iff_eq_empty.mp h)

/-- A constant weight gives the dimension times that constant. -/
@[simp]
theorem localWeight_const {L : ι → Module.Dual K V} {U : Submodule K V}
    (h : (localWeightBases L U).Nonempty) (a : ℝ) :
    localWeight L (fun _ ↦ a) U = finrank K U * a := by
  simpa using localWeight_add_const h 0 a

/-- Nonnegative form weights give nonnegative local weights. -/
theorem localWeight_nonneg {L : ι → Module.Dual K V} {U : Submodule K V}
    {c : ι → ℝ} (hc : 0 ≤ c) :
    0 ≤ localWeight L c U := by
  simpa using localWeight_mono (L := L) (U := U) hc

/-- For a basis of the ambient dual, the whole space has just the full local dual basis. -/
@[simp]
theorem localWeightBases_top {L : ι → Module.Dual K V}
    (hLi : LinearIndependent K L) (hL : span K (range L) = ⊤) :
    localWeightBases L (⊤ : Submodule K V) = {Finset.univ} := by
  classical
  have : Module.Finite K (Module.Dual K V) := Module.Finite.of_basis (Basis.mk hLi hL.ge)
  have : Module.Finite K V := (Module.finite_dual_iff K).mp inferInstance
  have hcard : Fintype.card ι = finrank K V := by
    have h := finrank_span_eq_card hLi
    rw [hL, finrank_top, Subspace.dual_finrank_eq] at h
    exact h.symm
  have hsurj : Function.Surjective (⊤ : Submodule K V).subtype := by
    intro x
    exact ⟨⟨x, mem_top⟩, rfl⟩
  have hli := hLi.map' (⊤ : Submodule K V).subtype.dualMap
    (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective hsurj))
  ext s
  simp only [mem_localWeightBases_iff_linearIndependent_card, finrank_top, Finset.mem_singleton]
  constructor
  · intro hs
    exact Finset.eq_univ_of_card s (hs.2.trans hcard.symm)
  · rintro rfl
    refine ⟨?_, by simpa using hcard⟩
    exact hli.comp _ Subtype.val_injective

/-- The local weight of the whole space is the sum of all weights for independent spanning forms. -/
@[simp]
theorem localWeight_top {L : ι → Module.Dual K V}
    (hLi : LinearIndependent K L) (hL : span K (range L) = ⊤) (c : ι → ℝ) :
    localWeight L c (⊤ : Submodule K V) = ∑ i, c i := by
  simp [localWeight, localWeightBases_top hLi hL]

/-- On a nonzero line, a singleton is a local dual basis exactly when its form does not vanish. -/
theorem singleton_mem_localWeightBases_span_singleton (L : ι → Module.Dual K V)
    {x : V} (hx : x ≠ 0) (i : ι) :
    {i} ∈ localWeightBases L (K ∙ x) ↔ L i x ≠ 0 := by
  classical
  rw [mem_localWeightBases_iff_linearIndependent_card]
  simp only [Finset.card_singleton, finrank_span_singleton hx, and_true]
  trans LinearIndepOn K (fun j ↦ (L j).comp (K ∙ x).subtype) (({i} : Finset ι) : Set ι)
  · simpa only [Finset.coe_sort_coe] using
      (linearIndependent_set_coe_iff (R := K)
        (v := fun j ↦ (L j).comp (K ∙ x).subtype) (s := (({i} : Finset ι) : Set ι)))
  · rw [Finset.coe_singleton, linearIndepOn_singleton_iff]
    apply not_congr
    rw [← LinearMap.range_le_ker_iff, Submodule.range_subtype,
      Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]

/-- The weight of a nonzero line is the infimum of the weights of its nonvanishing forms:
the least such weight when one exists, and zero otherwise. -/
theorem localWeight_span_singleton (L : ι → Module.Dual K V) (c : ι → ℝ)
    {x : V} (hx : x ≠ 0) :
    localWeight L c (K ∙ x) = sInf (c '' {i | L i x ≠ 0}) := by
  classical
  rw [localWeight_def]
  congr 1
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp
      ((card_eq_finrank_of_mem_localWeightBases hs).trans (finrank_span_singleton hx))
    exact ⟨i, (singleton_mem_localWeightBases_span_singleton L hx i).mp hs, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨{i}, (singleton_mem_localWeightBases_span_singleton L hx i).mpr hi, by simp⟩

end TauCeti
