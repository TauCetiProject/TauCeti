/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Orientation

/-!
# Orientation comparisons preserve path length

The existing isomorphism between preprojective algebras of two orientations is built from a
doubled-quiver identification and arrow rescalings. These operations preserve path length, so the
orientation comparison sends each homogeneous quotient class to one of the same degree. This is
the algebra-level input for comparing graded constructions, including Koszul resolutions, across
orientations.

## Main results

* `TauCeti.reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade`: the orientation comparison
  sends every homogeneous quotient class into the same degree piece.

## References

The local preprojective relations and orientation comparison follow Crawley-Boevey,
*Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]
  (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- **The orientation comparison preserves the path-length grading.** If an element of the
preprojective algebra of a reoriented quiver has degree `n`, its image in the original
preprojective algebra also has degree `n`. -/
theorem reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade {n : ℕ}
    {x : preprojectiveAlgebra k (Reorient Q σ)}
    (hx : x ∈ preprojectiveGrade k (Reorient Q σ) n) :
    reorientPreprojectiveAlgebraEquiv k σ x ∈ preprojectiveGrade k Q n := by
  rw [mem_preprojectiveGrade_iff] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨rescale (doubledLabelling k fun _ _ a => reorientSign k σ a)
    (reorientDoubledEquiv k σ y), ?_, ?_⟩
  · exact PathAlgebra.rescale_mem_grade _ (reorientDoubledEquiv_mem_grade k σ hy)
  · rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk]

end TauCeti
