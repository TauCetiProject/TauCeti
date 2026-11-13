/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Face
import Mathlib.Data.Finset.Sum

/-!
# Faces of intersections of polyhedra

Every nonempty convex extreme subset of the intersection of two convex
polyhedra is the intersection of actual nonempty exposed faces of the two
polyhedra. This decomposition supports closure under taking faces when
constructing common refinements of polyhedral complexes. No finite-dimensionality,
boundedness, or salience is assumed.

Adapted from `Mei/Geometry/Convex/Polyhedron/Face/Intersection.lean` at
Mei commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

namespace IsExtreme

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] {P Q F : Set V}

/-- A nonempty convex extreme subset of an intersection of polyhedra is the
intersection of nonempty exposed faces of the original polyhedra. -/
theorem exists_inter_isExposed_of_isConvexPolyhedron (hF : IsExtreme ℝ (P ∩ Q) F)
    (hP : TauCeti.IsConvexPolyhedron P) (hQ : TauCeti.IsConvexPolyhedron Q)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ F₁ F₂ : Set V, IsExposed ℝ P F₁ ∧ IsExposed ℝ Q F₂ ∧
      F₁.Nonempty ∧ F₂.Nonempty ∧ F = F₁ ∩ F₂ := by
  classical
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  obtain ⟨n, h, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hQ
  have hbase : {x : V | ∀ i, g i x ≤ 0} ∩ {x : V | ∀ j, h j x ≤ 0} =
      {x : V | ∀ k : Fin m ⊕ Fin n, Sum.elim g h k x ≤ 0} := by
    ext x
    simp [Sum.forall]
  rw [hbase] at hF
  obtain ⟨I, hI⟩ := hF.eq_setOf_active (fun k => (Sum.elim g h k).toAffineMap) hconv hne
  let L := I.toLeft
  let R := I.toRight
  let F₁ : Set V := {x | (∀ i, g i x ≤ 0) ∧ ∀ i ∈ L, g i x = 0}
  let F₂ : Set V := {x | (∀ j, h j x ≤ 0) ∧ ∀ j ∈ R, h j x = 0}
  have hsplit : F = F₁ ∩ F₂ := by
    ext x
    rw [hI]
    constructor
    · rintro ⟨hx, hxI⟩
      exact ⟨⟨fun i => hx (Sum.inl i), fun i hi => hxI (Sum.inl i) (Finset.mem_toLeft.mp hi)⟩,
        ⟨fun j => hx (Sum.inr j), fun j hj => hxI (Sum.inr j) (Finset.mem_toRight.mp hj)⟩⟩
    · rintro ⟨⟨hx, hxL⟩, ⟨hy, hyR⟩⟩
      constructor
      · intro k
        cases k with
        | inl i => exact hx i
        | inr j => exact hy j
      · intro k hk
        cases k with
        | inl i => exact hxL i (Finset.mem_toLeft.mpr hk)
        | inr j => exact hyR j (Finset.mem_toRight.mpr hk)
  obtain ⟨p, hp⟩ := hne
  have hp₁ : p ∈ F₁ := (hsplit ▸ hp).1
  have hp₂ : p ∈ F₂ := (hsplit ▸ hp).2
  exact ⟨F₁, F₂, TauCeti.isExposed_setOf_active g L,
    TauCeti.isExposed_setOf_active h R, ⟨p, hp₁⟩, ⟨p, hp₂⟩, hsplit⟩

end IsExtreme

namespace IsExposed

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] {P Q F : Set V}

/-- Every nonempty exposed face of an intersection of polyhedra splits into
nonempty exposed faces of the two original polyhedra. -/
theorem exists_inter_of_isConvexPolyhedron (hF : IsExposed ℝ (P ∩ Q) F)
    (hP : TauCeti.IsConvexPolyhedron P) (hQ : TauCeti.IsConvexPolyhedron Q)
    (hne : F.Nonempty) :
    ∃ F₁ F₂ : Set V, IsExposed ℝ P F₁ ∧ IsExposed ℝ Q F₂ ∧
      F₁.Nonempty ∧ F₂.Nonempty ∧ F = F₁ ∩ F₂ :=
  hF.isExtreme.exists_inter_isExposed_of_isConvexPolyhedron hP hQ
    (hF.convex (hP.convex.inter hQ.convex)) hne

end IsExposed
