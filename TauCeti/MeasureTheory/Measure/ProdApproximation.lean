/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Approximation by measurable rectangles

Every measurable subset of a product measurable space equipped with a finite measure can be
approximated in measure by a finite disjoint union of measurable rectangles.  The statement is
valid for arbitrary measurable spaces: no countable-generation or standard-Borel hypothesis is
needed.

This is the set-level approximation used in the finite-step reduction for the coupling triangle
inequality of graphon cut distance.  A bounded measurable kernel is first approximated by a simple
function; the result here is then applied to its finitely many level sets to construct an
approximating simple function depending on only finitely many measurable events in each coordinate.

The proof applies Mathlib's general density theorem
`exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` to the semiring of measurable
rectangles.  We verify the semiring law explicitly: the difference of two rectangles splits into
two disjoint rectangles.  `generateFrom_prod` supplies the generation of the product sigma algebra.

## Main results

* `TauCeti.MeasureTheory.exists_finset_prod_measure_symmDiff_lt` approximates a product-measurable
  set by a pairwise-disjoint finite family of measurable rectangles.
* `TauCeti.MeasureTheory.exists_finset_prod_symmetric_measure_symmDiff_lt` does so while preserving
  invariance under swapping the two coordinates.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 6.5.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, the Layer-1 design-validation milestone
  requiring stability of finite coupling gluing under step approximation.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal symmDiff

namespace TauCeti

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Measurable rectangles form a semiring of sets in a product space. -/
private theorem isSetSemiring_measurable_prod :
    IsSetSemiring
      (Set.image2 (· ×ˢ ·) {s : Set X | MeasurableSet s} {t : Set Y | MeasurableSet t}) where
  empty_mem := by
    refine ⟨∅, MeasurableSet.empty, Set.univ, MeasurableSet.univ, ?_⟩
    simp
  inter_mem := by
    rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    have hs : MeasurableSet s := by simpa only [Set.mem_ofPred_eq] using hs
    have ht : MeasurableSet t := by simpa only [Set.mem_ofPred_eq] using ht
    have hu : MeasurableSet u := by simpa only [Set.mem_ofPred_eq] using hu
    have hv : MeasurableSet v := by simpa only [Set.mem_ofPred_eq] using hv
    refine ⟨s ∩ u, hs.inter hu, t ∩ v, ht.inter hv, ?_⟩
    ext
    simp only [Set.mem_prod, Set.mem_inter_iff]
    grind
  sdiff_eq_sUnion' := by
    rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    have hs : MeasurableSet s := by simpa only [Set.mem_ofPred_eq] using hs
    have ht : MeasurableSet t := by simpa only [Set.mem_ofPred_eq] using ht
    have hu : MeasurableSet u := by simpa only [Set.mem_ofPred_eq] using hu
    have hv : MeasurableSet v := by simpa only [Set.mem_ofPred_eq] using hv
    let a : Set (X × Y) := (s \ u) ×ˢ t
    let b : Set (X × Y) := (s ∩ u) ×ˢ (t \ v)
    refine ⟨{a, b}, ?_, ?_, ?_⟩
    · rw [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨⟨s \ u, hs.diff hu, t, ht, rfl⟩,
        ⟨s ∩ u, hs.inter hu, t \ v, ht.diff hv, rfl⟩⟩
    · rw [Finset.coe_insert, Finset.coe_singleton]
      apply Set.pairwiseDisjoint_insert.2
      refine ⟨Set.pairwiseDisjoint_singleton b id, ?_⟩
      intro _ hy _
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply Set.disjoint_left.2
      intro p ha hb
      simp only [a, b] at ha hb
      exact ha.1.2 hb.1.2
    · rw [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton]
      ext p
      simp only [a, b, Set.mem_sdiff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
      grind

/-- A measurable subset of a product measurable space with a finite measure can be approximated in
measure by a pairwise-disjoint finite union of measurable rectangles.

The output family contains no empty set, because it is the family of parts of a `Finpartition`.
The conclusion uses `⋃₀ (I : Set (Set (X × Y)))` rather than an indexed union so callers may retain
the finite family itself and refine all of its coordinate sides at once. -/
theorem exists_finset_prod_measure_symmDiff_lt (ρ : Measure (X × Y)) [IsFiniteMeasure ρ]
    {s : Set (X × Y)} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ I : Finset (Set (X × Y)),
      (∀ r ∈ I, ∃ a : Set X, MeasurableSet a ∧ ∃ b : Set Y, MeasurableSet b ∧ r = a ×ˢ b) ∧
      (I : Set (Set (X × Y))).PairwiseDisjoint id ∧ ∅ ∉ I ∧
      ρ (⋃₀ (I : Set (Set (X × Y))) ∆ s) < ε := by
  let C : Set (Set (X × Y)) :=
    Set.image2 (· ×ˢ ·) {a : Set X | MeasurableSet a} {b : Set Y | MeasurableSet b}
  have hC : IsSetSemiring C := isSetSemiring_measurable_prod
  have hcover : ∃ D : Set (Set (X × Y)),
      D.Countable ∧ D ⊆ C ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ ×ˢ Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · rintro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      exact ⟨Set.univ, MeasurableSet.univ, Set.univ, MeasurableSet.univ, rfl⟩
    · simp
  have hgenerate : Prod.instMeasurableSpace = MeasurableSpace.generateFrom C := by
    exact generateFrom_prod.symm
  obtain ⟨t, htC, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    hC hcover hgenerate hs hε
  obtain ⟨P, hPC⟩ := hC.mem_supClosure_iff.1 htC
  refine ⟨P.parts, ?_, P.disjoint, P.bot_notMem, ?_⟩
  · intro r hr
    have hrect : r ∈ Set.image2 (· ×ˢ ·) {a : Set X | MeasurableSet a}
        {b : Set Y | MeasurableSet b} := by
      simpa only [C] using hPC hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hrect
    exact ⟨a, ha, b, hb, rfl⟩
  · have hUnion : ⋃₀ (P.parts : Set (Set (X × Y))) = t :=
      (Finset.sup_id_set_eq_sUnion P.parts).symm.trans P.sup_parts
    simpa only [hUnion] using ht

/-- A finite union of sets from a semiring of sets lies in the ring `supClosure C` it generates. -/
theorem sUnion_finset_mem_supClosure {α : Type*} {C : Set (Set α)}
    (hC : IsSetSemiring C) {I : Finset (Set α)} (hI : ∀ r ∈ I, r ∈ C) :
    ⋃₀ (I : Set (Set α)) ∈ supClosure C := by
  rw [← Finset.sup_id_set_eq_sUnion]
  exact hC.isSetRing_supClosure.finsetSup_mem fun r hr => subset_supClosure (hI r hr)

/-- An element of the ring generated by measurable rectangles is a finite disjoint union of
measurable rectangles, none of them empty. -/
private theorem exists_finset_rect_of_mem_supClosure {v : Set (X × Y)}
    (hv : v ∈ supClosure
      (Set.image2 (· ×ˢ ·) {a : Set X | MeasurableSet a} {b : Set Y | MeasurableSet b})) :
    ∃ I : Finset (Set (X × Y)),
      (∀ r ∈ I, ∃ a : Set X, MeasurableSet a ∧ ∃ b : Set Y, MeasurableSet b ∧ r = a ×ˢ b) ∧
      (I : Set (Set (X × Y))).PairwiseDisjoint id ∧ ∅ ∉ I ∧ ⋃₀ (I : Set (Set (X × Y))) = v := by
  obtain ⟨P, hPC⟩ := isSetSemiring_measurable_prod.mem_supClosure_iff.1 hv
  refine ⟨P.parts, fun r hr => ?_, P.disjoint, P.bot_notMem, ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hPC hr
    exact ⟨a, ha, b, hb, rfl⟩
  · exact (Finset.sup_id_set_eq_sUnion P.parts).symm.trans P.sup_parts

/-- Swapping the coordinates of an approximant of a swap-invariant set does not change the
measure of the symmetric difference. -/
theorem measure_symmDiff_preimage_swap_of_preimage_swap_eq (μ : Measure X) [SFinite μ]
    {u s : Set (X × X)} (hu : MeasurableSet u) (hs : MeasurableSet s)
    (hsymm : Prod.swap ⁻¹' s = s) :
    (μ.prod μ) ((Prod.swap ⁻¹' u) ∆ s) = (μ.prod μ) (u ∆ s) := by
  calc
    (μ.prod μ) ((Prod.swap ⁻¹' u) ∆ s) = (μ.prod μ) (Prod.swap ⁻¹' (u ∆ s)) := by
      rw [Set.preimage_symmDiff, hsymm]
    _ = (μ.prod μ) (u ∆ s) :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage
        (hu.symmDiff hs).nullMeasurableSet

/-- The union of a finite family of measurable rectangles of `X × X` with its swap lies in the
ring generated by measurable rectangles. -/
private theorem union_preimage_swap_mem_supClosure {I : Finset (Set (X × X))}
    (hI : ∀ r ∈ I, ∃ a : Set X, MeasurableSet a ∧ ∃ b : Set X, MeasurableSet b ∧ r = a ×ˢ b) :
    ⋃₀ (I : Set (Set (X × X))) ∪ Prod.swap ⁻¹' ⋃₀ (I : Set (Set (X × X))) ∈ supClosure
      (Set.image2 (· ×ˢ ·) {a : Set X | MeasurableSet a} {b : Set X | MeasurableSet b}) := by
  have hC := isSetSemiring_measurable_prod (X := X) (Y := X)
  have hIC : ∀ r ∈ I, r ∈ Set.image2 (· ×ˢ ·) {a : Set X | MeasurableSet a}
      {b : Set X | MeasurableSet b} := fun r hr => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hI r hr
    exact ⟨a, ha, b, hb, rfl⟩
  have hJC : ∀ r ∈ I.image fun r => Prod.swap ⁻¹' r, r ∈ Set.image2 (· ×ˢ ·)
      {a : Set X | MeasurableSet a} {b : Set X | MeasurableSet b} := fun r hr => by
    obtain ⟨q, hqI, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hI q hqI
    rw [Set.preimage_swap_prod]
    exact ⟨b, hb, a, ha, rfl⟩
  have hswapUnion : ⋃₀ ((I.image fun r => Prod.swap ⁻¹' r : Finset (Set (X × X))) :
      Set (Set (X × X))) = Prod.swap ⁻¹' ⋃₀ (I : Set (Set (X × X))) := by
    ext p
    simp only [Finset.coe_image, Set.mem_sUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨r, ⟨q, hqI, rfl⟩, hp⟩
      exact ⟨q, hqI, hp⟩
    · rintro ⟨q, hqI, hp⟩
      exact ⟨Prod.swap ⁻¹' q, ⟨q, hqI, rfl⟩, hp⟩
  exact hC.isSetRing_supClosure.union_mem (sUnion_finset_mem_supClosure hC hIC)
    (hswapUnion ▸ sUnion_finset_mem_supClosure hC hJC)

/-- A swap-invariant measurable subset of the square of a finite measure space can be approximated
by a swap-invariant, pairwise-disjoint finite union of measurable rectangles.

Starting from `exists_finset_prod_measure_symmDiff_lt`, take the union of the approximant and its
coordinate swap.  This at most doubles the error.  The resulting finite union is repartitioned into
disjoint rectangles using the same rectangle semiring, so symmetry does not cost the useful
pairwise-disjoint output contract. -/
theorem exists_finset_prod_symmetric_measure_symmDiff_lt (μ : Measure X) [IsFiniteMeasure μ]
    {s : Set (X × X)} (hs : MeasurableSet s) (hsymm : Prod.swap ⁻¹' s = s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ I : Finset (Set (X × X)),
      (∀ r ∈ I, ∃ a : Set X, MeasurableSet a ∧ ∃ b : Set X, MeasurableSet b ∧ r = a ×ˢ b) ∧
      (I : Set (Set (X × X))).PairwiseDisjoint id ∧ ∅ ∉ I ∧
      Prod.swap ⁻¹' ⋃₀ (I : Set (Set (X × X))) = ⋃₀ (I : Set (Set (X × X))) ∧
      (μ.prod μ) (⋃₀ (I : Set (Set (X × X))) ∆ s) < ε := by
  obtain ⟨I, hIrect, _, _, hIapprox⟩ :=
    exists_finset_prod_measure_symmDiff_lt (μ.prod μ) hs (ENNReal.half_pos hε.ne')
  have huMeas : MeasurableSet (⋃₀ (I : Set (Set (X × X)))) := by
    refine MeasurableSet.sUnion I.finite_toSet.to_countable fun r hr => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hIrect r hr
    exact ha.prod hb
  have hswapError := measure_symmDiff_preimage_swap_of_preimage_swap_eq μ huMeas hs hsymm
  obtain ⟨K, hKrect, hKdisj, hKbot, hKunion⟩ :=
    exists_finset_rect_of_mem_supClosure (union_preimage_swap_mem_supClosure hIrect)
  refine ⟨K, hKrect, hKdisj, hKbot, ?_, ?_⟩
  · rw [hKunion, Set.preimage_union, Set.preimage_preimage]
    exact Set.union_comm _ _
  · rw [hKunion]
    calc
      (μ.prod μ) ((⋃₀ (I : Set (Set (X × X))) ∪ Prod.swap ⁻¹' ⋃₀ (I : Set (Set (X × X)))) ∆ s)
          ≤ (μ.prod μ) ((⋃₀ (I : Set (Set (X × X))) ∆ s) ∪
              ((Prod.swap ⁻¹' ⋃₀ (I : Set (Set (X × X)))) ∆ s)) :=
            measure_mono Set.union_symmDiff_subset
      _ ≤ (μ.prod μ) (⋃₀ (I : Set (Set (X × X))) ∆ s) +
            (μ.prod μ) ((Prod.swap ⁻¹' ⋃₀ (I : Set (Set (X × X)))) ∆ s) :=
        measure_union_le _ _
      _ < ε / 2 + ε / 2 := by
        rw [hswapError]
        exact ENNReal.add_lt_add hIapprox hIapprox
      _ = ε := ENNReal.add_halves ε

end MeasureTheory

end TauCeti
