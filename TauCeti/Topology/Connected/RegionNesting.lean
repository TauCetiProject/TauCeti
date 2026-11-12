/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# Nesting and innermost selection for regions with disjoint frontiers

Closed regions with connected inside, outside and boundary are nested, disjoint, or cover
the space when their frontiers are disjoint. A common exterior point rules out the covering
case. In a finite nonempty family, minimality then selects a region missing every other
frontier. These are topological separation statements; no ball filling is assumed to exist.

## References

* Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Proposition 15.3.
* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {B C S : Set X}

/-- A preconnected set avoiding a closed region's frontier lies entirely
in its interior or entirely outside the region. -/
theorem subset_interior_or_subset_compl_of_disjoint_frontier
    (hB : IsClosed B) (hS : IsPreconnected S)
    (hdisjoint : Disjoint S (frontier B)) :
    S ⊆ interior B ∨ S ⊆ Bᶜ := by
  apply IsPreconnected.subset_or_subset isOpen_interior hB.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) ?_ hS
  intro x hx
  by_cases hxB : x ∈ B
  · left
    by_contra hxI
    exact Set.disjoint_left.mp hdisjoint hx (hB.frontier_eq ▸ ⟨hxB, hxI⟩)
  · exact Or.inr hxB

/-- Closed regions with a connected boundary and connected inside and
outside have the four usual nesting alternatives when their frontiers
are disjoint. Only the first region needs both connectedness assumptions. -/
theorem disjoint_or_subset_or_subset_or_union_eq_univ_of_disjoint_frontiers
    (hB : IsClosed B) (hC : IsClosed C)
    (hBin : IsPreconnected B) (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C)) :
    Disjoint B C ∨ B ⊆ C ∨ C ⊆ B ∨ B ∪ C = Set.univ := by
  rcases subset_interior_or_subset_compl_of_disjoint_frontier hB hboundary hdisjoint.symm with
    hinside | houtside
  · have havoid : Disjoint Bᶜ (frontier C) := by
      apply Set.disjoint_left.mpr
      intro x hx hfrontier
      exact hx (interior_subset (hinside hfrontier))
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hC hBout havoid with
      hcover | hsubset
    · right; right; right
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ B
      · exact Or.inl hx
      · exact Or.inr (interior_subset (hcover hx))
    · right; right; left
      intro x hx
      by_contra hxB
      exact hsubset hxB hx
  · have havoid : Disjoint B (frontier C) := by
      apply Set.disjoint_left.mpr
      intro x hx hfrontier
      exact houtside hfrontier hx
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hC hBin havoid with hsubset | hsep
    · exact Or.inr (Or.inl (hsubset.trans interior_subset))
    · exact Or.inl (Set.disjoint_left.mpr (fun _ hx hy ↦ hsep hx hy))

/-- A common point outside both regions excludes the whole-space
alternative, leaving exactly nesting or disjointness. -/
theorem disjoint_or_subset_or_subset_of_disjoint_frontiers
    (hB : IsClosed B) (hC : IsClosed C)
    (hBin : IsPreconnected B) (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C))
    (p : X) (hpB : p ∉ B) (hpC : p ∉ C) :
    Disjoint B C ∨ B ⊆ C ∨ C ⊆ B := by
  rcases disjoint_or_subset_or_subset_or_union_eq_univ_of_disjoint_frontiers
    hB hC hBin hBout
    hboundary hdisjoint with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have hp : p ∈ B ∪ C := h.symm ▸ Set.mem_univ p
    exact (hp.elim hpB hpC).elim

/-- Containment of regions with disjoint frontiers is strict at
the outer boundary: the smaller region lies in the larger interior. -/
theorem subset_interior_of_subset_of_disjoint_frontiers
    (hsubset : B ⊆ C)
    (hdisjoint : Disjoint (frontier B) (frontier C)) :
    B ⊆ interior C := by
  intro x hx
  by_cases hxI : x ∈ interior B
  · exact interior_mono hsubset hxI
  · by_contra hxC
    have hxfrontB : x ∈ frontier B := ⟨subset_closure hx, hxI⟩
    have hxfrontC : x ∈ frontier C := ⟨subset_closure (hsubset hx), hxC⟩
    exact Set.disjoint_left.mp hdisjoint hxfrontB hxfrontC

/-- A closed preconnected region with nonempty frontier cannot meet
another closed region when each avoids the other's frontier. -/
theorem closed_regions_disjoint_of_mutual_frontier_avoidance
    {X : Type*} [TopologicalSpace X] {B C : Set X}
    (hB : IsClosed B) (hC : IsClosed C) (hconnected : IsPreconnected B)
    (hboundary : (frontier B).Nonempty)
    (hBC : Disjoint B (frontier C)) (hCB : Disjoint C (frontier B)) :
    Disjoint B C := by
  rcases subset_interior_or_subset_compl_of_disjoint_frontier hC hconnected hBC with hinner | houter
  · obtain ⟨x, hx⟩ := hboundary
    exact (Set.disjoint_left.mp hCB
      (interior_subset (hinner (hB.frontier_subset hx))) hx).elim
  · exact Set.disjoint_left.mpr (fun _ hx hy ↦ houter hx hy)


/-- A finite nonempty family of closed regions with pairwise disjoint frontiers and a
common exterior point has a member disjoint from every other frontier, provided the
regions, their complements and their frontiers are preconnected. -/
theorem exists_disjoint_frontier_of_finite_regions
    {ι : Type*} [Finite ι] [Nonempty ι] (B : ι → Set X)
    (hclosed : ∀ i, IsClosed (B i)) (hin : ∀ i, IsPreconnected (B i))
    (hout : ∀ i, IsPreconnected (B i)ᶜ) (hfront : ∀ i, IsPreconnected (frontier (B i)))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (frontier (B i)) (frontier (B j)))
    (p : X) (hp : ∀ i, p ∉ B i) :
    ∃ i, ∀ j, j ≠ i → Disjoint (B i) (frontier (B j)) := by
  obtain ⟨i, hmin⟩ := Set.Finite.exists_minimalFor
    B Set.univ (Set.toFinite Set.univ) Set.univ_nonempty
  refine ⟨i, ?_⟩
  intro j hji
  have hfr : Disjoint (frontier (B i)) (frontier (B j)) := hdisjoint hji.symm
  rcases disjoint_or_subset_or_subset_of_disjoint_frontiers (hclosed i) (hclosed j) (hin i) (hout i)
    (hfront j) hfr p (hp i) (hp j) with hsep | hsub | hsub
  · exact hsep.mono_right (hclosed j).frontier_subset
  · exact disjoint_left.mpr fun x hx hboundary ↦ hboundary.2
      (subset_interior_of_subset_of_disjoint_frontiers hsub hfr hx)
  · have heq : B i = B j := (hmin.le_of_le (Set.mem_univ j) hsub).antisymm hsub
    rw [heq] at hfr
    simp only [disjoint_self] at hfr
    simp [hfr]

end TauCeti
