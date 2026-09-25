/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Separation.Basic

/-!
# Coordinate zero-pattern strata

For a subset `A` of an index type, the corresponding zero-pattern stratum consists of families
that vanish exactly on `A`, paired with an unrestricted second component. This file records the
product description of these strata, their local closedness for a finite index type, and their
closure when zero is not isolated.

## Main declarations

* `TauCeti.zeroPatternSet`: the coordinate stratum with zero set exactly `A`.
* `TauCeti.isLocallyClosed_zeroPatternSet`: a zero-pattern stratum with finitely many coordinates
  is locally closed.
* `TauCeti.closure_zeroPatternSet`: its closure allows additional coordinates to vanish.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- The coordinate stratum attached to a subset `A` of an index type: precisely those pairs whose
first coordinates vanish on `A` and nowhere else. The second component is unrestricted. -/
def zeroPatternSet (α β K : Type*) [Zero K] (A : Set α) : Set ((α → K) × β) :=
  {z | ∀ a, z.1 a = 0 ↔ a ∈ A}

/-- A coordinate pair belongs to the stratum attached to `A` exactly when its first coordinate
vanishes precisely on `A`. -/
@[simp]
theorem mem_zeroPatternSet (α β K : Type*) [Zero K] (A : Set α) (z : (α → K) × β) :
    z ∈ zeroPatternSet α β K A ↔ ∀ a, z.1 a = 0 ↔ a ∈ A :=
  Iff.rfl

/-- The coordinate stratum is a product of single-coordinate conditions with an unrestricted
second factor. -/
theorem zeroPatternSet_eq_pi_prod (α β K : Type*) [Zero K] (A : Set α) :
    zeroPatternSet α β K A =
      (Set.pi Set.univ fun a ↦ {z : K | z = 0 ↔ a ∈ A}) ×ˢ Set.univ := by
  ext z
  rw [mem_zeroPatternSet]
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, and_true]
  rfl

/-- A coordinate stratum with finitely many first coordinates is locally closed. -/
theorem isLocallyClosed_zeroPatternSet (α β K : Type*) [Finite α] [Zero K]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace β] (A : Set α) :
    IsLocallyClosed (zeroPatternSet α β K A) := by
  classical
  let U := (Set.pi Aᶜ fun _ ↦ ({0}ᶜ : Set K)) ×ˢ (Set.univ : Set β)
  let Z := (Set.pi A fun _ ↦ ({0} : Set K)) ×ˢ (Set.univ : Set β)
  have hU : IsOpen U :=
    (isOpen_set_pi (Set.toFinite _) fun _ _ ↦ isOpen_compl_singleton).prod isOpen_univ
  have hZ : IsClosed Z :=
    (isClosed_set_pi fun _ _ ↦ isClosed_singleton).prod isClosed_univ
  refine ⟨U, Z, hU, hZ, ?_⟩
  ext z
  simp only [mem_zeroPatternSet, Set.mem_inter_iff, U, Z, Set.mem_prod, Set.mem_pi,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, and_true]
  constructor
  · intro hz
    exact ⟨fun a ha ↦ (hz a).not.mpr ha, fun a ha ↦ (hz a).mpr ha⟩
  · rintro ⟨hU', hZ'⟩ a
    exact ⟨fun h ↦ Classical.byContradiction fun hn ↦ hU' a hn h,
      fun h ↦ hZ' a h⟩

/-- The closure of a coordinate stratum permits additional first coordinates to vanish, while
retaining the coordinates already forced to be zero. -/
theorem closure_zeroPatternSet (α β K : Type*) [Zero K] [TopologicalSpace K] [T1Space K]
    [NeBot (𝓝[≠] (0 : K))] [TopologicalSpace β] (A : Set α) :
    closure (zeroPatternSet α β K A) = {z | ∀ a ∈ A, z.1 a = 0} := by
  classical
  rw [zeroPatternSet_eq_pi_prod, closure_prod_eq, closure_pi_set]
  ext z
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, closure_univ, and_true]
  constructor
  · intro hz a ha
    simpa [ha] using hz a
  · intro hz a
    by_cases ha : a ∈ A
    · simpa [ha] using hz a ha
    · have hne : {w : K | w = 0 ↔ a ∈ A} = ({0}ᶜ : Set K) := by
        ext w
        simp [ha]
      rw [hne, closure_compl_singleton]
      exact Set.mem_univ _

end TauCeti
