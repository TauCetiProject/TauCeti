/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold

/-!
# Combinatorially triangulable spaces

This predicate records the stronger witness needed when a triangulation is required to carry
the link condition of a combinatorial manifold.  It is kept separate from `IsTriangulable`:
an arbitrary simplicial complex can realize a triangulable space without presenting a PL
manifold.

The predicate `IsCombinatoriallyTriangulable` is indexed by the manifold dimension `n`, using the
same convention as `PreAbstractSimplicialComplex.IsCombinatorialManifold`.

## Main definitions

* `IsCombinatoriallyTriangulable`: a space has a triangulation by a combinatorial manifold.

## Main results

* `IsCombinatoriallyTriangulable.isTriangulable`: combinatorial triangulability implies
  triangulability.
* `isCombinatoriallyTriangulable_iff`: the defining witness characterization.
* `AbstractSimplicialComplex.isCombinatoriallyTriangulable_realization`: realizations of
  combinatorial manifolds are combinatorially triangulable.
* `Homeomorph.isCombinatoriallyTriangulable_iff`: invariance under homeomorphism.
-/

public section

namespace TauCeti

noncomputable section
attribute [local instance] Classical.decEq

/-- `X` has a triangulation by a combinatorial `n`-manifold. -/
def IsCombinatoriallyTriangulable.{v, u} (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∃ (ι : Type v) (K : AbstractSimplicialComplex ι),
    K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n ∧
      Nonempty (AbstractSimplicialComplex.Realization K ≃ₜ X)

universe u v w

variable {X : Type u} [TopologicalSpace X]

/-- A combinatorial triangulation is, in particular, a triangulation. -/
theorem IsCombinatoriallyTriangulable.isTriangulable
    (h : IsCombinatoriallyTriangulable.{v} X n) : IsTriangulable.{v} X := by
  rcases h with ⟨ι, K, _, ⟨e⟩⟩
  exact (Homeomorph.isTriangulable_iff e).mp
    (AbstractSimplicialComplex.isTriangulable_realization K)


/-- Characterization of combinatorial triangulability by its defining witness. -/
theorem isCombinatoriallyTriangulable_iff :
    IsCombinatoriallyTriangulable.{v} X n ↔
      ∃ (ι : Type v) (K : AbstractSimplicialComplex ι),
        K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n ∧
          Nonempty (AbstractSimplicialComplex.Realization K ≃ₜ X) := Iff.rfl

/-- The realization of a combinatorial manifold is combinatorially triangulable. -/
theorem _root_.AbstractSimplicialComplex.isCombinatoriallyTriangulable_realization
    {ι : Type v} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι)
    (hK : @PreAbstractSimplicialComplex.IsCombinatorialManifold ι (Classical.decEq ι)
      K.toPreAbstractSimplicialComplex n) :
    IsCombinatoriallyTriangulable.{v} (_root_.AbstractSimplicialComplex.Realization K) n := by
  letI := Classical.decEq ι
  exact ⟨ι, K, (by
    exact hK),
    ⟨Homeomorph.refl _⟩⟩

end

end TauCeti

open TauCeti

variable {X : Type u} [TopologicalSpace X]

/-- Combinatorial triangulability is invariant under homeomorphism of the ambient space. -/
theorem Homeomorph.isCombinatoriallyTriangulable_iff
    {Y : Type w} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    IsCombinatoriallyTriangulable.{v} X n ↔
      IsCombinatoriallyTriangulable.{v} Y n := by
  constructor
  · rintro ⟨ι, K, hK, ⟨h⟩⟩
    exact ⟨ι, K, hK, ⟨h.trans e⟩⟩
  · rintro ⟨ι, K, hK, ⟨h⟩⟩
    exact ⟨ι, K, hK, ⟨h.trans e.symm⟩⟩
