/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.Frontier
public import Mathlib.Order.Preorder.Finite

/-!
# Nesting and innermost selection for regions with disjoint frontiers

If `B`, its complement, and the frontier of `C` are preconnected, disjoint frontiers
force `B` and `C` to be disjoint, nested, or to cover the space. Noncovering rules out the
last case. A finite nonempty family of sets whose complements and frontiers are preconnected,
with pairwise disjoint frontiers and pairwise unions different from the whole space, has a
member disjoint from all other frontiers.

A preconnected set that is not open is disjoint from any set when each set
avoids the other's frontier. These separation statements support the innermost and mutual
frontier avoidance steps of finite sphere-cutting decompositions.

## References

* Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Proposition 15.3.
* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {B C : Set X}

/-- If the complement of `B` and the frontier of `C` are preconnected and the frontiers
are disjoint, then `B` avoids the frontier of `C`, `C` is contained in `B`, or `B ∪ C`
is the whole space. -/
theorem _root_.IsPreconnected.disjoint_frontier_or_subset_or_union_eq_univ_of_disjoint_frontier
    (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C)) :
    Disjoint B (frontier C) ∨ C ⊆ B ∨ B ∪ C = Set.univ := by
  rcases hboundary.subset_interior_or_subset_compl_closure hdisjoint.symm with hinside | houtside
  · have havoid : Disjoint Bᶜ (frontier C) :=
      disjoint_compl_left_iff_subset.mpr (hinside.trans interior_subset)
    rcases hBout.subset_interior_or_subset_compl_closure havoid with hcover | hsubset
    · exact Or.inr (Or.inr (compl_subset_iff_union.mp (hcover.trans interior_subset)))
    · exact Or.inr (Or.inl (compl_subset_compl.mp
        (hsubset.trans (compl_subset_compl.mpr subset_closure))))
  · exact Or.inl (subset_compl_iff_disjoint_left.mp
      (houtside.trans (compl_subset_compl.mpr subset_closure)))

/-- If `B`, its complement and the frontier of `C` are preconnected and the frontiers
are disjoint, the sets are disjoint, one contains the other, or `B ∪ C` is the whole space. -/
theorem _root_.IsPreconnected.disjoint_or_subset_or_subset_or_union_eq_univ_of_disjoint_frontier
    (hBin : IsPreconnected B) (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C)) :
    Disjoint B C ∨ B ⊆ C ∨ C ⊆ B ∨ B ∪ C = Set.univ := by
  rcases hBout.disjoint_frontier_or_subset_or_union_eq_univ_of_disjoint_frontier
    hboundary hdisjoint with havoid | hsub | hcover
  · rcases hBin.subset_interior_or_subset_compl_closure havoid with hsubset | hsep
    · exact Or.inr (Or.inl (hsubset.trans interior_subset))
    · exact Or.inl (subset_compl_iff_disjoint_right.mp
        (hsep.trans (compl_subset_compl.mpr subset_closure)))
  · exact Or.inr (Or.inr (Or.inl hsub))
  · exact Or.inr (Or.inr (Or.inr hcover))

/-- If `B`, its complement and the frontier of `C` are preconnected, the frontiers of
`B` and `C` are disjoint and `B ∪ C` is not the whole space, then the sets are disjoint
or one contains the other. -/
theorem _root_.IsPreconnected.disjoint_or_subset_or_subset_of_disjoint_frontier
    (hBin : IsPreconnected B) (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C))
    (hcover : B ∪ C ≠ Set.univ) :
    Disjoint B C ∨ B ⊆ C ∨ C ⊆ B := by
  rcases hBin.disjoint_or_subset_or_subset_or_union_eq_univ_of_disjoint_frontier
    hBout hboundary hdisjoint with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (hcover h).elim

/-- A preconnected set that is not open is disjoint from any set when
both sets avoid the other's frontier. -/
theorem disjoint_of_not_isOpen_of_disjoint_frontier
    (hB : ¬ IsOpen B) (hconnected : IsPreconnected B)
    (hBC : Disjoint B (frontier C)) (hCB : Disjoint C (frontier B)) :
    Disjoint B C := by
  rcases hconnected.subset_interior_or_subset_compl_closure hBC with hinner | houter
  · exact (hB (disjoint_frontier_iff_isOpen.mp
      (hCB.symm.mono_right (hinner.trans interior_subset)))).elim
  · exact subset_compl_iff_disjoint_right.mp
      (houter.trans (compl_subset_compl.mpr subset_closure))

/-- On a finite nonempty index set, pairwise noncovering sets with disjoint frontiers have
a member disjoint from every other frontier if their complements and frontiers are
preconnected. No set is required to be closed or preconnected. -/
theorem exists_forall_ne_disjoint_frontier_of_pairwiseDisjoint_frontier
    {ι : Type*} (B : ι → Set X) {s : Set ι} (hs : s.Finite) (hne : s.Nonempty)
    (hout : ∀ i ∈ s, IsPreconnected (B i)ᶜ)
    (hfront : ∀ i ∈ s, IsPreconnected (frontier (B i)))
    (hdisjoint : s.PairwiseDisjoint (frontier ∘ B))
    (hcover : s.Pairwise fun i j ↦ B i ∪ B j ≠ Set.univ) :
    ∃ i ∈ s, ∀ j ∈ s, j ≠ i → Disjoint (B i) (frontier (B j)) := by
  obtain ⟨i, hmin⟩ := Set.Finite.exists_minimalFor
    B s hs hne
  refine ⟨i, hmin.prop, ?_⟩
  intro j hj hji
  have hfr : Disjoint (frontier (B i)) (frontier (B j)) := hdisjoint hmin.prop hj hji.symm
  rcases (hout i hmin.prop).disjoint_frontier_or_subset_or_union_eq_univ_of_disjoint_frontier
    (hfront j hj) hfr with hsep | hsub | hcover'
  · exact hsep
  · have heq : B i = B j := (hmin.le_of_le hj hsub).antisymm hsub
    rw [heq] at hfr
    simp only [disjoint_self] at hfr
    simp [hfr]
  · exact (hcover hmin.prop hj hji.symm hcover').elim

end TauCeti
