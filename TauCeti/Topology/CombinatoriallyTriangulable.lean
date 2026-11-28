/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Basic
public import TauCeti.Topology.Triangulable.FiniteCWType
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.VertexPlacement

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
* `IsCombinatoriallyTriangulable.exists_vertex_image_of_compactSpace`: every finite subset of a
  compact combinatorially triangulable space is a vertex image in a finite combinatorial
  triangulation of the same dimension.
* `IsCombinatoriallyTriangulable.finiteCWType_compl`: removing any finite subset from a compact
  combinatorially triangulable space preserves `FiniteCWType`.
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
    {ι : Type v}
    (K : AbstractSimplicialComplex ι)
    (hK : @PreAbstractSimplicialComplex.IsCombinatorialManifold ι (Classical.decEq ι)
      K.toPreAbstractSimplicialComplex n) :
    IsCombinatoriallyTriangulable.{v} (_root_.AbstractSimplicialComplex.Realization K) n := by
  let _ := Classical.decEq ι
  exact ⟨ι, K, (by
    exact hK),
    ⟨Homeomorph.refl _⟩⟩

/-- Every finite subset of a compact combinatorially triangulable space is a vertex image in a
finite combinatorial triangulation of the same dimension. -/
theorem IsCombinatoriallyTriangulable.exists_vertex_image_of_compactSpace
    [CompactSpace X] {n : ℕ}
    (htri : IsCombinatoriallyTriangulable.{w} X n) {S : Set X} (hS : S.Finite) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι)
      (e : AbstractSimplicialComplex.Realization K ≃ₜ X) (V : Set ι),
      Finite ι ∧ K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n ∧
      e '' (K.vertex '' V) = S := by
  obtain ⟨ι, K, hK, ⟨e⟩⟩ := isCombinatoriallyTriangulable_iff.mp htri
  have := e.symm.compactSpace
  have hfin : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  obtain ⟨ι', inst', K', e', V, hfin', hman', hV⟩ :=
    K.exists_homeomorph_vertex_image_of_homeomorph e hS
  exact ⟨ι', K', e', V, hfin' hfin,
    (K'.toPreAbstractSimplicialComplex.isCombinatorialManifold_congr_decidableEq
      inst' (Classical.decEq ι')).mp (hman' n hK),
    hV⟩

/-- Removing any finite subset from a compact combinatorially triangulable space leaves a space
of finite CW type. -/
theorem IsCombinatoriallyTriangulable.finiteCWType_compl
    [CompactSpace X] {n : ℕ}
    (htri : IsCombinatoriallyTriangulable.{w} X n) {S : Set X} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ :=
  htri.isTriangulable.finiteCWType_compl hS

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
