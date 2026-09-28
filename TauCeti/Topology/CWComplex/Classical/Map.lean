/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Cellular maps of relative CW complexes

A cellular map preserves the skeletal filtration of a relative CW complex. This condition
ensures that the map restricts to each skeleton and to each consecutive skeletal pair, the
restrictions used to act on cellular chains.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

open CategoryTheory Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X Y Z : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  {D : Set X} {E : Set Y} {F : Set Z}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

/-- A map of relative CW complexes is cellular if it preserves every stage of the skeletal
filtration. In particular, it sends the base (stage zero) into the target base. -/
abbrev IsCellular (f : TopCat.of X ⟶ TopCat.of Y) : Prop :=
  ∀ n : ℕ, Set.MapsTo f (skeletonLT C (n : ℕ∞)) (skeletonLT C' (n : ℕ∞))

/-- A cellular map sends the carrier of the source complex into the carrier of the target.
Every point of a relative CW complex belongs to some finite skeleton. -/
lemma IsCellular.mapsTo {f : TopCat.of X ⟶ TopCat.of Y}
    (hf : IsCellular C C' f) : Set.MapsTo f C C' := by
  intro x hx
  rw [← (iUnion_skeletonLT_eq_complex (C := C))] at hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact (skeletonLT C' (n : ℕ∞)).subset_complex (hf n hn)

/-- The identity map preserves every skeleton. -/
lemma isCellular_id : IsCellular C C (𝟙 (TopCat.of X)) := fun _ _ h ↦ h

/-- The composite of cellular maps is cellular. -/
lemma IsCellular.comp {C'' : Set Z} [RelCWComplex C'' F]
    {f : TopCat.of X ⟶ TopCat.of Y} {g : TopCat.of Y ⟶ TopCat.of Z}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g) :
    IsCellular C C'' (f ≫ g) := fun n _ hx ↦ hg n (hf n hx)

end TauCeti
