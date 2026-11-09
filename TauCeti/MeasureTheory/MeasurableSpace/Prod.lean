/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.SetSemiring

/-!
# Products of σ-algebras

Measurable rectangles form a semiring of sets: the difference of two rectangles splits into two
disjoint rectangles. This is the input to Mathlib's density theorems for set semirings
generating a σ-algebra, such as `exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring`.

The product of the discrete σ-algebras on two types is again discrete as soon as the first type is
countable. Countability is what makes this work: every subset `s` of the product is the countable
union of the measurable rectangles `{a} ×ˢ (Prod.mk a ⁻¹' s)` over the points `a` of the first
factor. No hypothesis on the second factor is needed.

## Main results

* `TauCeti.MeasureTheory.isSetSemiring_measurable_prod`: measurable rectangles form a semiring
  of sets.
* `TauCeti.MeasureTheory.prod_top_eq_top_of_countable`: the product of the discrete σ-algebras on
  a countable type and an arbitrary type is discrete.
-/

public section

open Set MeasureTheory

namespace TauCeti.MeasureTheory

section Rectangle

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Measurable rectangles form a semiring of sets in a product space: the difference of two
rectangles splits into two disjoint rectangles. -/
theorem isSetSemiring_measurable_prod :
    IsSetSemiring
      (Set.image2 (· ×ˢ ·) {s : Set X | MeasurableSet s} {t : Set Y | MeasurableSet t}) where
  empty_mem := ⟨∅, .empty, univ, .univ, empty_prod⟩
  inter_mem := by
    rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    exact ⟨s ∩ u, hs.inter hu, t ∩ v, ht.inter hv, prod_inter_prod.symm⟩
  sdiff_eq_sUnion' := by
    rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    refine ⟨{(s \ u) ×ˢ t, (s ∩ u) ×ˢ (t \ v)}, ?_, ?_, ?_⟩ <;> rw [Finset.coe_pair]
    · exact pair_subset_iff.2
        ⟨⟨s \ u, hs.diff hu, t, ht, rfl⟩, ⟨s ∩ u, hs.inter hu, t \ v, ht.diff hv, rfl⟩⟩
    · refine pairwiseDisjoint_insert.2 ⟨pairwiseDisjoint_singleton _ _, fun _ hy _ => ?_⟩
      rw [mem_singleton_iff.1 hy]
      exact disjoint_left.2 fun _ ha hb => ha.1.2 hb.1.2
    · ext
      simp only [sUnion_pair, mem_sdiff, mem_prod, mem_union, mem_inter_iff]
      grind

end Rectangle

/-- The product of the discrete σ-algebras on a countable type `α` and an arbitrary type `β` is
discrete. -/
theorem prod_top_eq_top_of_countable (α β : Type*) [Countable α] :
    (⊤ : MeasurableSpace α).prod (⊤ : MeasurableSpace β) = ⊤ := by
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  refine top_unique fun s _ => measurableSet_setOfPred.2 ?_
  exact measurable_from_prod_countable_right fun _ => measurable_from_top

end TauCeti.MeasureTheory
