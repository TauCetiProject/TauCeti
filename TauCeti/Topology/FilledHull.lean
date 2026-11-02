/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Frontier

/-!
# Filling in the bounded complementary components of a set

The **filled hull** `TauCeti.filledHull K` of a subset `K` of a topological space with a bornology
is `K` together with the bounded connected components of its complement: the points whose component
in `Kᶜ` is bounded. Points of `K` qualify vacuously, their component in `Kᶜ` being empty. Filling a
circle gives the closed disc it bounds; filling a segment, or any set whose complement is connected
and unbounded, changes nothing.

This file develops the definition and structural properties using only a topology and a bornology.
In a real seminormed space, filling preserves boundedness and diameter; these bounds are proved in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

The trapping property `IsPreconnected.subset_filledHull` says that a preconnected set disjoint from
`K` lies inside the filled hull as soon as it meets it, since it then lies in a single bounded
component. Together with the diameter bound, it gives `IsPreconnected.diam_le_diam_of_disjoint`:
a preconnected set disjoint from a bounded `K` that meets its filled hull has diameter at most
`diam K`, without regularity assumptions on `K`.

A point lies outside the filled hull exactly when its component in the complement of `K` is
unbounded. This is the hypothesis of
`TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Winding/UnboundedComponent.lean` and of its cycle form
`TauCeti.Contour.Cycle.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Cycle/Winding.lean`: for a closed curve with the required regularity,
or a contour cycle, the winding number vanishes outside the filled hull of its trace.

Without additional hypotheses on `K`, the hull need not be closed or connected.

## Compactness

For the bornology of relatively compact sets in a locally compact Hausdorff, locally connected
space with no compact connected component, the filled hull of a compact set `K` is compact
(`IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl`): every relatively
compact component of `Kᶜ` either meets the frontier of a compact neighbourhood `L` of `K`, in which
case it is one of the finitely many components covering that frontier, or it lies inside `L`; a
component lying outside `L` would be clopen in the whole space, hence contain a compact component.
This feeds the construction of locally finite proper rays in
`TauCeti/Topology/Connected/ProperRay.lean`.

## Planar enclosure

For a planar set `J`, `filledHull J \ J` consists of its bounded complementary components.
The enclosure theorem
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton`
combines winding-number two-sidedness with preconnectedness of `K \ {f z₀}` to place the near-side
image of a circular crosscut inside `filledHull K` when the far-side image has larger diameter
than `K`. For a Jordan curve, `TauCeti.IsJordanCurve.isPathConnected_sdiff_singleton` supplies
the required preconnectedness. These enclosure and diameter estimates are used in the
Carathéodory boundary correspondence in `TauCeti/Analysis/Complex/Conformal/Caratheodory.lean`.

## Main results

* `TauCeti.filledHull` — the filled hull, and `TauCeti.subset_filledHull`,
  `TauCeti.filledHull_mono` its two structural properties.
* `TauCeti.filledHull_eq_self` — filling a set whose complement is preconnected and unbounded
  changes nothing.
* `IsClosed.isOpen_filledHull_sdiff`, `IsClosed.isClosed_filledHull`, and
  `IsClosed.frontier_filledHull_sdiff_subset` — for a closed set in a locally connected space,
  the bounded complementary components form an open set whose frontier lies in that set.
* `TauCeti.filledHull_eq_self_of_isPreconnected_frontier` — an open set with preconnected frontier
  and unbounded complement has no holes: filling it changes nothing.
* `IsPreconnected.subset_filledHull` — a preconnected set disjoint from `K` that meets the
  filled hull lies in it.
* `TauCeti.subset_filledHull_of_frontier_subset` — a bounded set whose frontier `K` swallows
  lies in the filled hull, with no connectivity asked of it.
* `IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl` — a compact set together
  with the relatively compact components of its complement is compact.
* `TauCeti.exists_mem_not_isCompact_closure_connectedComponentIn_compl` — a set with noncompact
  closure meets a component of the complement of a compact set which again has noncompact closure.
-/

public section

namespace TauCeti

open Bornology Set

variable {E : Type*} [TopologicalSpace E] [Bornology E] {K L S : Set E} {x : E}

/-- The **filled hull** of a set `K`: the points whose connected component in the complement of `K`
is bounded. Equivalently, `K` together with the bounded connected components of `Kᶜ`; a point of
`K` belongs because its component in `Kᶜ` is empty. -/
def filledHull (K : Set E) : Set E := {x | IsBounded (connectedComponentIn Kᶜ x)}

@[simp]
theorem mem_filledHull_iff
    : x ∈ filledHull K ↔ IsBounded (connectedComponentIn Kᶜ x) := Iff.rfl

/-- Membership in the filled hull is the same at every point of a component of `Kᶜ`. -/
theorem mem_filledHull_iff_of_mem_connectedComponentIn {y : E}
    (hy : y ∈ connectedComponentIn Kᶜ x) : y ∈ filledHull K ↔ x ∈ filledHull K := by
  rw [mem_filledHull_iff, mem_filledHull_iff, connectedComponentIn_eq hy]

/-- **A set lies in its filled hull.** For `x ∈ K` the component of `x` in `Kᶜ` is empty, and the
empty set is bounded. -/
theorem subset_filledHull : K ⊆ filledHull K := by
  intro x hx
  have hxc : x ∉ Kᶜ := by simpa using hx
  simp [mem_filledHull_iff, connectedComponentIn_eq_empty hxc]

/-- **Filling is monotone.** Enlarging `K` shrinks the complement, hence shrinks each component of
it, hence can only turn unbounded components into bounded ones. -/
@[gcongr]
theorem filledHull_mono (h : K ⊆ L) : filledHull K ⊆ filledHull L := fun _ hx =>
  mem_filledHull_iff.mpr <|
    (mem_filledHull_iff.mp hx).subset (connectedComponentIn_mono _ (compl_subset_compl.mpr h))

/-- The bounded complementary components of a closed set form an open set in a locally
connected space. No Jordan-curve or finiteness assumption is needed. -/
theorem _root_.IsClosed.isOpen_filledHull_sdiff
    [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsOpen (filledHull K \ K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hx.2)) ?_
  intro y hy
  exact ⟨(mem_filledHull_iff_of_mem_connectedComponentIn hy).mpr hx.1,
    connectedComponentIn_subset Kᶜ x hy⟩

/-- Filling a closed set preserves closedness in a locally connected space. -/
theorem _root_.IsClosed.isClosed_filledHull [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsClosed (filledHull K) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hxK : x ∈ Kᶜ := fun h => hx (subset_filledHull h)
  refine Filter.mem_of_superset
    ((hK.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hxK)) ?_
  exact fun y hy hyH => hx ((mem_filledHull_iff_of_mem_connectedComponentIn hy).mp hyH)

/-- The frontier of the bounded complementary components of a closed set lies in the set
itself. In particular, filling introduces no new boundary points. -/
theorem _root_.IsClosed.frontier_filledHull_sdiff_subset
    [LocallyConnectedSpace E] (hK : IsClosed K) :
    frontier (filledHull K \ K) ⊆ K := by
  intro x hx
  have hxH : x ∈ filledHull K :=
    (closure_minimal sdiff_subset (IsClosed.isClosed_filledHull hK)) hx.1
  by_contra hxK
  exact hx.2 ((IsClosed.isOpen_filledHull_sdiff hK).interior_eq.symm ▸ ⟨hxH, hxK⟩)

/-- **Filling changes nothing when the complement is connected and unbounded.** The complement is
then a single component and that component is unbounded, so no point outside `K` is filled in. This
is the case of a segment in the plane, and of any set that does not separate the space. -/
theorem filledHull_eq_self
    (h : IsPreconnected Kᶜ) (hu : ¬ IsBounded Kᶜ) : filledHull K = K := by
  refine Subset.antisymm (fun x hx => ?_) subset_filledHull
  by_contra hxK
  exact hu ((mem_filledHull_iff.mp hx).subset
    (h.subset_connectedComponentIn (mem_compl hxK) subset_rfl))

/-- **An open set with preconnected frontier has no holes**, in a preconnected, locally connected
space: if the complement of `K` is unbounded, filling `K` changes nothing. The complement is then
preconnected (`TauCeti.isPreconnected_compl_of_isPreconnected_frontier`), so this is
`TauCeti.filledHull_eq_self`. A bounded open set of the plane whose frontier is a Jordan curve is
the basic example. -/
theorem filledHull_eq_self_of_isPreconnected_frontier [LocallyConnectedSpace E]
    [PreconnectedSpace E] (hK : IsOpen K) (hf : IsPreconnected (frontier K))
    (hu : ¬ IsBounded Kᶜ) : filledHull K = K :=
  filledHull_eq_self (isPreconnected_compl_of_isPreconnected_frontier hK hf) hu

/-- **A preconnected set that a set cuts off from infinity lies in its filled hull.** If `S` is
preconnected and disjoint from `K`, then `S` lies in a single connected component of `Kᶜ`; meeting
the filled hull says that component is bounded, so all of `S` is in the hull. -/
theorem _root_.IsPreconnected.subset_filledHull (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) : S ⊆ filledHull K := by
  obtain ⟨x, hxS, hxH⟩ := hne
  have hScompl : S ⊆ Kᶜ := fun y hy => Set.disjoint_left.mp hSK hy
  have hScomp : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hScompl
  exact fun y hy => (mem_filledHull_iff_of_mem_connectedComponentIn (hScomp hy)).mpr hxH

/-- **A bounded set whose frontier lies in `K` is cut off from infinity by `K`.** A point of
`S \ K` lies in `interior S`, since every non-interior point of `S` lies on `frontier S ⊆ K`. Its
connected component in `Kᶜ` cannot leave `interior S`: were it to, it would meet
`frontier (interior S) ⊆ frontier S ⊆ K` by `IsPreconnected.inter_frontier_nonempty`,
while lying in `Kᶜ`. So that component is bounded because `S` is. Points of `S ∩ K` lie in the
filled hull directly.

Unlike `IsPreconnected.subset_filledHull` this asks nothing of the connectivity of `S` and
nothing about the hull being met, at the price of asking `K` to swallow the whole frontier — the
same trade as between `TauCeti.diam_le_diam_of_frontier_subset` and
`IsPreconnected.diam_le_diam_of_disjoint`. -/
theorem subset_filledHull_of_frontier_subset (hSb : IsBounded S) (hfr : frontier S ⊆ K) :
    S ⊆ filledHull K := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact subset_filledHull hxK
  have hxKc : x ∈ Kᶜ := hxK
  have hxi : x ∈ interior S := (mem_interior_iff_notMem_frontier hx).2 fun h => hxK (hfr h)
  have hcomp : connectedComponentIn Kᶜ x ⊆ interior S := by
    by_contra h
    obtain ⟨y, hy, hyi⟩ := not_subset.mp h
    obtain ⟨z, hz, hzf⟩ := isPreconnected_connectedComponentIn.inter_frontier_nonempty
      ⟨x, mem_connectedComponentIn hxKc, hxi⟩ ⟨y, hy, hyi⟩
    exact connectedComponentIn_subset _ _ hz (hfr (frontier_interior_subset hzf))
  exact mem_filledHull_iff.mpr (hSb.subset (hcomp.trans interior_subset))

end TauCeti

section Compact

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]

/-- **The filled hull of a compact set is compact.** In a locally compact Hausdorff, locally
connected space with no compact connected component, a compact set `K` together with the
connected components of `Kᶜ` having compact closure is compact. This set is the filled hull of `K`
for the bornology of relatively compact sets; points of `K` belong to it because their component in
`Kᶜ` is empty. -/
theorem IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl
    [LocallyConnectedSpace X] {K : Set X} (hK : IsCompact K)
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) :
    IsCompact {x | IsCompact (closure (connectedComponentIn Kᶜ x))} := by
  set B := {x | IsCompact (closure (connectedComponentIn Kᶜ x))}
  have hB : IsClosed B := by
    let : Bornology X := .relativelyCompact X
    have hBK : B = TauCeti.filledHull K := by
      ext x
      simp [B, Bornology.relativelyCompact.isBounded_iff]
    exact hBK ▸ hK.isClosed.isClosed_filledHull
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  -- Finitely many components of `Kᶜ` cover the frontier of the compact neighbourhood `L`.
  have hfrK : frontier L ⊆ Kᶜ := fun y hy hyK ↦ hy.2 (hKL hyK)
  obtain ⟨F, hFL, hcover⟩ := (hL.of_isClosed_subset isClosed_frontier
    hL.isClosed.frontier_subset).elim_nhds_subcover (connectedComponentIn Kᶜ)
      fun y hy ↦ hK.isClosed.isOpen_compl.connectedComponentIn.mem_nhds
        (mem_connectedComponentIn (hfrK hy))
  classical
  refine (hL.union ((F.filter (· ∈ B)).isCompact_biUnion fun z hz ↦
    (Finset.mem_filter.1 hz).2)).of_isClosed_subset hB fun y hy ↦ ?_
  by_cases hyL : y ∈ L
  · exact Or.inl hyL
  right
  set C := connectedComponentIn Kᶜ y
  have hyC : y ∈ C := mem_connectedComponentIn fun hyK ↦ hyL (interior_subset (hKL hyK))
  by_cases hCfr : (C ∩ frontier L).Nonempty
  · -- A component meeting the frontier of `L` is one of the covering components.
    obtain ⟨w, hwC, hwL⟩ := hCfr
    obtain ⟨z, hzF, hwz⟩ := mem_iUnion₂.1 (hcover hwL)
    have hCz : connectedComponentIn Kᶜ z = C :=
      (connectedComponentIn_eq hwz).trans (connectedComponentIn_eq hwC).symm
    refine mem_iUnion₂.2 ⟨z, Finset.mem_filter.2 ⟨hzF, ?_⟩, ?_⟩
    · simpa [B, hCz] using hy
    · exact subset_closure (hCz ▸ hyC)
  · -- Otherwise the component lies outside `L`, so it is clopen and contains a component of `X`.
    exfalso
    have hCL : C ⊆ Lᶜ := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hL.isClosed.isOpen_compl ⟨y, hyC, hyL⟩ fun w ⟨hw, hwC⟩ hwL ↦
        hCfr ⟨w, hwC, subset_closure hwL, by rwa [← mem_compl_iff, ← closure_compl]⟩
    have hfrC : frontier C = ∅ := by
      refine eq_empty_of_forall_notMem fun w hw ↦ ?_
      have hwK : w ∈ K := by
        simpa using TauCeti.frontier_connectedComponentIn_subset_compl hK.isClosed.isOpen_compl
          y hw
      have hw' : w ∈ closure Lᶜ := closure_mono hCL (frontier_subset_closure hw)
      rw [closure_compl] at hw'
      exact hw' (hKL hwK)
    have hcomp : connectedComponent y ⊆ closure C :=
      ((isClopen_iff_frontier_eq_empty.2 hfrC).connectedComponent_subset hyC).trans subset_closure
    exact hX y (hy.of_isClosed_subset isClosed_connectedComponent hcomp)

namespace TauCeti

/-- In a locally compact Hausdorff, locally connected space with no compact connected component,
a set with noncompact closure contains a point whose component in the complement of a given
compact set `L` again has noncompact closure. -/
theorem exists_mem_not_isCompact_closure_connectedComponentIn_compl [LocallyConnectedSpace X]
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) {S L : Set X}
    (hS : ¬IsCompact (closure S)) (hL : IsCompact L) :
    ∃ y ∈ S, ¬IsCompact (closure (connectedComponentIn Lᶜ y)) := by
  by_contra! h
  have hB := hL.isCompact_setOf_isCompact_closure_connectedComponentIn_compl hX
  exact hS (hB.of_isClosed_subset isClosed_closure (closure_minimal h hB.isClosed))

end TauCeti

end Compact
