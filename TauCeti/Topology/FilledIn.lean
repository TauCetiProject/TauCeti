/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Topology.FilledHull
import Mathlib.Topology.MetricSpace.Bounded
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.ConnectedComponents

/-!
# Sets filled in an open set

A set `K` is *filled in* a set `Ω` (`TauCeti.IsFilledIn K Ω`) if no connected component of
`Ω \ K` is relatively compact in `Ω`, that is, has compact closure contained in `Ω`. This is the
topological hypothesis of Runge-type approximation theorems, under which functions holomorphic, or
harmonic, near a compact set `K ⊆ Ω` are uniform limits on `K` of functions holomorphic, or
harmonic, on all of `Ω`.

Adjoining to any set `K` the connected components of `Ω \ K` whose closures are compact and
contained in `Ω` always produces a set filled in `Ω`
(`TauCeti.isFilledIn_union_setOf_isCompact_closure_connectedComponentIn`), since removing those
components leaves the remaining components of `Ω \ K` unchanged.

In a proper, locally connected metric space,
`TauCeti.isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset` recasts the
condition through the bounded components of `Kᶜ`, which make up the filled hull
`TauCeti.filledHull K \ K`: for closed `K ⊆ Ω`, the set `K` is filled in `Ω` exactly when every
bounded connected component of `Kᶜ` meets `Ωᶜ`. The relatively compact components of `Ω \ K` in
`Ω` are precisely the bounded components of `Kᶜ` contained in `Ω`
(`TauCeti.setOf_isCompact_closure_connectedComponentIn_eq_filledHull`), so adjoining them to a
closed `K ⊆ Ω` gives a closed subset of `Ω`
(`IsClosed.isClosed_union_setOf_isCompact_closure_connectedComponentIn`), which is compact when `K`
is compact and the ambient space has no compact connected component
(`IsCompact.isCompact_union_setOf_isCompact_closure_connectedComponentIn`).
For `Ω` the whole space, being filled in it means being equal to the filled hull
(`TauCeti.isFilledIn_univ_iff`).

Filled compact exhaustions of open sets in proper real normed spaces are constructed in
`TauCeti/Analysis/Normed/Module/Exhaustion.lean`, and preservation of filledness under discrete
unions on manifolds of dimension greater than one is proved in
`TauCeti/Geometry/Manifold/FilledIn.lean`.

## Main declarations

* `TauCeti.IsFilledIn`: no connected component of `Ω \ K` is relatively compact in `Ω`.
* `IsOpen.isFilledIn_empty`: the empty set is filled in every open subset of a locally connected
  space with no compact connected component.
* `TauCeti.isFilledIn_union_setOf_isCompact_closure_connectedComponentIn`: adjoining the relatively
  compact components of `Ω \ K` in `Ω` produces a set filled in `Ω`.
* `TauCeti.isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset`: the same
  condition through the bounded components of `Kᶜ`.
* `IsCompact.isCompact_union_setOf_isCompact_closure_connectedComponentIn`: for compact `K ⊆ Ω` in
  a proper locally connected metric space without compact components, adjoining the relatively
  compact components of `Ω \ K` in `Ω` gives a compact subset of `Ω`.
* `TauCeti.isFilledIn_univ_iff`: a closed set is filled in the whole space exactly when it equals
  its filled hull.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Bornology Metric Set

namespace TauCeti

section Topology

variable {X : Type*} [TopologicalSpace X] {K Ω : Set X}

/-- A set `K` is **filled in** a set `Ω` if no connected component of `Ω \ K` is relatively compact
in `Ω`: the closure of each such component is noncompact or leaves `Ω`. -/
def IsFilledIn (K Ω : Set X) : Prop :=
  ∀ x ∈ Ω \ K,
    ¬ (IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
      closure (connectedComponentIn (Ω \ K) x) ⊆ Ω)

/-- Unfolding `TauCeti.IsFilledIn`. -/
theorem isFilledIn_iff :
    IsFilledIn K Ω ↔ ∀ x ∈ Ω \ K,
      ¬ (IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
        closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :=
  Iff.rfl

/-- In a locally connected space with no compact connected component, the empty set is filled in
every open set. -/
theorem _root_.IsOpen.isFilledIn_empty [LocallyConnectedSpace X] (hΩ : IsOpen Ω)
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) : IsFilledIn ∅ Ω := by
  -- A component of `Ω` with compact closure in `Ω` is clopen in `X`, hence a compact component.
  rintro x ⟨hxΩ, -⟩ ⟨hcpt, hsub⟩
  rw [sdiff_empty] at hcpt hsub
  have hcl : closure (connectedComponentIn Ω x) = connectedComponentIn Ω x :=
    Subset.antisymm
      (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hxΩ)) hsub)
      subset_closure
  have hclopen : IsClopen (connectedComponentIn Ω x) :=
    ⟨hcl ▸ isClosed_closure, hΩ.connectedComponentIn⟩
  exact hX x (hcpt.of_isClosed_subset isClosed_connectedComponent
    ((hclopen.connectedComponent_subset (mem_connectedComponentIn hxΩ)).trans subset_closure))

/-- **Adjoining the relatively compact complementary components fills a set in `Ω`.** Adding to `K`
all points of `Ω \ K` whose connected component in `Ω \ K` has compact closure contained in `Ω`
produces a set filled in `Ω`. -/
theorem isFilledIn_union_setOf_isCompact_closure_connectedComponentIn (K Ω : Set X) :
    IsFilledIn (K ∪ {x ∈ Ω \ K |
      IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
        closure (connectedComponentIn (Ω \ K) x) ⊆ Ω}) Ω := by
  set S := K ∪ {x ∈ Ω \ K |
    IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
      closure (connectedComponentIn (Ω \ K) x) ⊆ Ω}
  rintro x ⟨hxΩ, hxS⟩
  have hxK : x ∈ Ω \ K := ⟨hxΩ, fun hxK => hxS (Or.inl hxK)⟩
  have hcomp : connectedComponentIn (Ω \ S) x = connectedComponentIn (Ω \ K) x := by
    refine Subset.antisymm
      (connectedComponentIn_mono x (sdiff_subset_sdiff Subset.rfl subset_union_left))
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxK) fun y hy => ⟨(connectedComponentIn_subset _ _ hy).1,
          fun hyS => ?_⟩)
    rcases hyS with hyK | ⟨-, hycpt⟩
    · exact (connectedComponentIn_subset _ _ hy).2 hyK
    · exact hxS (Or.inr ⟨hxK, by rwa [connectedComponentIn_eq hy]⟩)
  rw [hcomp]
  exact fun h => hxS (Or.inr ⟨hxK, h⟩)

end Topology

section MetricSpace

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X] [LocallyConnectedSpace X] {K Ω : Set X}

/-- **Relatively compact components of `Ω \ K` versus bounded components of `Kᶜ`.** For a closed
subset `K` of an open set `Ω` in a proper, locally connected metric space, the points of `Ω \ K`
whose component in `Ω \ K` has compact closure contained in `Ω` are the points of
`filledHull K \ K` whose component in `Kᶜ` lies in `Ω`. -/
theorem setOf_isCompact_closure_connectedComponentIn_eq_filledHull
    (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    {x ∈ Ω \ K | IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
      closure (connectedComponentIn (Ω \ K) x) ⊆ Ω} =
      {x ∈ filledHull K \ K | connectedComponentIn Kᶜ x ⊆ Ω} := by
  ext x
  constructor
  · rintro ⟨⟨hxΩ, hxK⟩, hcpt, hsub⟩
    have hD : connectedComponentIn Kᶜ x ⊆ connectedComponentIn (Ω \ K) x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn_of_inter_closure_subset
        (hΩ.sdiff hK) (mem_connectedComponentIn hxK) ⟨hxΩ, hxK⟩
        fun y hy => ⟨hsub hy.2, connectedComponentIn_subset _ _ hy.1⟩
    exact ⟨⟨mem_filledHull_iff.mpr (hcpt.isBounded.subset (hD.trans subset_closure)), hxK⟩,
      hD.trans (subset_closure.trans hsub)⟩
  · rintro ⟨⟨hxH, hxK⟩, hDΩ⟩
    have hCD : connectedComponentIn (Ω \ K) x ⊆ connectedComponentIn Kᶜ x :=
      connectedComponentIn_mono x (sdiff_subset_compl _ _)
    have hclD : closure (connectedComponentIn Kᶜ x) ⊆ Ω := by
      rw [closure_eq_self_union_frontier]
      exact union_subset hDΩ <| (frontier_connectedComponentIn_subset_compl hK.isOpen_compl x).trans
        (by rwa [compl_compl])
    exact ⟨⟨hDΩ (mem_connectedComponentIn hxK), hxK⟩,
      (mem_filledHull_iff.mp hxH).isCompact_closure.of_isClosed_subset isClosed_closure
        (closure_mono hCD), (closure_mono hCD).trans hclD⟩

/-- **Filledness through the filled hull.** For a closed set `K` inside an open set `Ω` of a proper,
locally connected metric space, `K` is filled in `Ω` exactly when no bounded connected component
of `Kᶜ` lies in `Ω`, i.e. every bounded component of `Kᶜ` meets `Ωᶜ`. -/
theorem isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ x ∈ filledHull K \ K, ¬ connectedComponentIn Kᶜ x ⊆ Ω := by
  have heq := Set.ext_iff.mp (setOf_isCompact_closure_connectedComponentIn_eq_filledHull hK hΩ hKΩ)
  exact ⟨fun h x hx hD => h x ⟨hD (mem_connectedComponentIn hx.2), hx.2⟩
      ((heq x).mpr ⟨hx, hD⟩).2,
    fun h x hx hcpt => h x ((heq x).mp ⟨hx, hcpt⟩).1 ((heq x).mp ⟨hx, hcpt⟩).2⟩

/-- Adjoining to a closed set `K ⊆ Ω` the relatively compact components of `Ω \ K` in `Ω` yields a
closed set. -/
theorem _root_.IsClosed.isClosed_union_setOf_isCompact_closure_connectedComponentIn
    (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    IsClosed (K ∪ {x ∈ Ω \ K |
      IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
        closure (connectedComponentIn (Ω \ K) x) ⊆ Ω}) := by
  rw [setOf_isCompact_closure_connectedComponentIn_eq_filledHull hK hΩ hKΩ, ← isOpen_compl_iff,
    isOpen_iff_mem_nhds]
  intro x hx
  have hxK : x ∈ Kᶜ := fun h => hx (Or.inl h)
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hxK)) ?_
  rintro y hy (hyK | ⟨⟨hyH, -⟩, hyΩ⟩)
  · exact connectedComponentIn_subset Kᶜ x hy hyK
  · exact hx (Or.inr ⟨⟨(mem_filledHull_iff_of_mem_connectedComponentIn hy).mp hyH, hxK⟩,
      by rwa [connectedComponentIn_eq hy]⟩)

/-- **Compactness of the relative fill.** In a proper, locally connected metric space with no
compact connected component, adjoining to a compact set `K ⊆ Ω` the relatively compact components
of `Ω \ K` in `Ω` produces a compact subset of `Ω`. -/
theorem _root_.IsCompact.isCompact_union_setOf_isCompact_closure_connectedComponentIn [T2Space X]
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) :
    IsCompact (K ∪ {x ∈ Ω \ K |
      IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
        closure (connectedComponentIn (Ω \ K) x) ⊆ Ω}) := by
  refine (hK.isCompact_setOf_isCompact_closure_connectedComponentIn_compl hX).of_isClosed_subset
    (hK.isClosed.isClosed_union_setOf_isCompact_closure_connectedComponentIn hΩ hKΩ) ?_
  rw [setOf_isCompact_closure_connectedComponentIn_eq_filledHull hK.isClosed hΩ hKΩ]
  rintro x (hxK | ⟨⟨hxH, -⟩, -⟩)
  · exact isCompact_closure_connectedComponentIn_compl_of_mem hxK
  · exact (mem_filledHull_iff.mp hxH).isCompact_closure

/-- A closed set is filled in the whole space exactly when it equals its filled hull, i.e. its
complement has no bounded connected component. -/
theorem isFilledIn_univ_iff (hK : IsClosed K) : IsFilledIn K univ ↔ filledHull K = K := by
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset hK isOpen_univ
    (subset_univ K)]
  exact ⟨fun h => Subset.antisymm
      (fun x hx => by_contra fun hxK => h x ⟨hx, hxK⟩ (subset_univ _)) subset_filledHull,
    fun h x hx _ => hx.2 (h ▸ hx.1)⟩

end MetricSpace

end TauCeti
