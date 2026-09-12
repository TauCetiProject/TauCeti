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
-/

public section

namespace TauCeti

noncomputable section
attribute [local instance] Classical.decEq

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- `X` has a triangulation by a combinatorial `n`-manifold. -/
def IsCombinatoriallyTriangulable (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∃ (ι : Type v) (K : AbstractSimplicialComplex ι),
    K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n ∧
      Nonempty (AbstractSimplicialComplex.Realization K ≃ₜ X)

/-- A combinatorial triangulation is, in particular, a triangulation. -/
theorem IsCombinatoriallyTriangulable.isTriangulable
    (h : IsCombinatoriallyTriangulable.{u, v} X n) : IsTriangulable.{v} X := by
  rcases h with ⟨ι, K, _, ⟨e⟩⟩
  exact (Homeomorph.isTriangulable_iff e).mp
    (AbstractSimplicialComplex.isTriangulable_realization K)

/-- Combinatorial triangulability is invariant under homeomorphism of the ambient space. -/
theorem Homeomorph.isCombinatoriallyTriangulable_iff
    {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    IsCombinatoriallyTriangulable.{u, v} X n ↔
      IsCombinatoriallyTriangulable.{u, v} Y n := by
  constructor
  · rintro ⟨ι, K, hK, ⟨h⟩⟩
    exact ⟨ι, K, hK, ⟨h.trans e⟩⟩
  · rintro ⟨ι, K, hK, ⟨h⟩⟩
    exact ⟨ι, K, hK, ⟨h.trans e.symm⟩⟩

end

end TauCeti
