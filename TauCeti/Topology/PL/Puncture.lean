/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Structure
public import TauCeti.Topology.Triangulable.Vertices
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.VertexPlacement
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Complement

/-!
# Finite punctures of PL manifolds and compact triangulated spaces

By placing vertices at arbitrary finite subsets via stellar subdivision
(`AbstractSimplicialComplex.exists_subdivision_vertex_image`) and passing to the complement model
in the barycentric subdivision (`AbstractSimplicialComplex.instFiniteCWTypeComplVertexImage`),
removing any finite subset `S` from a compact triangulable space (in particular a space with a
`PLStructure`, with or without boundary, connected or not, in any dimension `n`) yields a space
`↥Sᶜ` of finite CW type.

For spaces carrying a `PLStructure`, the subdivided triangulation remains a `PLStructure` of the
same dimension, so even boundary punctures and punctures in dimensions `0` and `1` are covered.

## Main results

* `TauCeti.PLStructure.exists_vertex_image`: any finite subset of a space with a `PLStructure`
  becomes a vertex image after stellar subdivision, preserving the `PLStructure` dimension.
* `TauCeti.PLStructure.finiteCWType_compl`: removing any finite subset from a space with a
  `PLStructure` preserves `FiniteCWType`.
* `TauCeti.IsCombinatoriallyTriangulable.exists_vertex_image_of_compactSpace` and
  `TauCeti.IsCombinatoriallyTriangulable.finiteCWType_compl`: the same for compact spaces with
  a combinatorial triangulation.
* `TauCeti.IsTriangulable.exists_vertex_image_of_compactSpace` and
  `TauCeti.IsTriangulable.finiteCWType_compl`: removing any finite subset from any compact
  triangulable space preserves `FiniteCWType`.
-/

public section

noncomputable section

open AbstractSimplicialComplex Set

namespace TauCeti

universe u w

attribute [local instance] Classical.decEq

namespace PLStructure

variable {M : Type u} [TopologicalSpace M] {n : ℕ}

/-- Any finite subset `S : Set M` becomes the image of a vertex set in a subdivided `PLStructure`
of the same dimension `n` on `M`. No boundarylessness, connectedness, or dimension lower bound
is required. -/
theorem exists_vertex_image (s : PLStructure M n) {S : Set M} (hS : S.Finite) :
    ∃ (s' : PLStructure M n) (V : Set s'.ι), s'.e '' (s'.K.vertex '' V) = S := by
  obtain ⟨ι', _, K', e', V, hfin, hman, hV⟩ :=
    s.K.exists_subdivision_vertex_image (hS.preimage s.e.injective.injOn)
  have : Finite ι' := hfin s.finite_ι
  let s' : PLStructure M n :=
    { ι := ι'
      K := K'
      isCombinatorialManifold := by
        convert hman n s.isCombinatorialManifold
      e := e'.trans s.e }
  refine ⟨s', V, ?_⟩
  dsimp only [s']
  change (s.e ∘ e') '' (K'.vertex '' V) = S
  rw [Set.image_comp, hV, Set.image_preimage_eq _ s.e.surjective]

/-- Removing any finite subset `S : Set M` from a space carrying a `PLStructure` leaves a space
of finite CW type. -/
theorem finiteCWType_compl (s : PLStructure M n) {S : Set M} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ := by
  obtain ⟨s', V, hV⟩ := s.exists_vertex_image hS
  have heq : s'.e ⁻¹' Sᶜ = (s'.K.vertex '' V)ᶜ := by
    rw [← hV, preimage_compl, s'.e.injective.preimage_image]
  have := s'.K.instFiniteCWTypeComplVertexImage V
  exact (s'.e.sets heq.symm).symm.finiteCWType

end PLStructure

/-- Every finite subset of a compact combinatorially triangulable space is a vertex image in a
finite combinatorial triangulation of the same dimension. -/
theorem IsCombinatoriallyTriangulable.exists_vertex_image_of_compactSpace
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (htri : IsCombinatoriallyTriangulable.{w} X n) {S : Set X} (hS : S.Finite) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι) (e : Realization K ≃ₜ X) (V : Set ι),
      Finite ι ∧ K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n ∧
      e '' (K.vertex '' V) = S := by
  obtain ⟨ι, K, hK, ⟨e⟩⟩ := isCombinatoriallyTriangulable_iff.mp htri
  have := e.symm.compactSpace
  have hfin : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  obtain ⟨ι', _, K', e', V, hfin', hman', hV⟩ :=
    K.exists_subdivision_vertex_image (hS.preimage e.injective.injOn)
  refine ⟨ι', K', e'.trans e, V, hfin' hfin, by convert hman' n hK, ?_⟩
  change (e ∘ e') '' (K'.vertex '' V) = S
  rw [Set.image_comp, hV, Set.image_preimage_eq _ e.surjective]

/-- Every finite subset of a compact triangulable space is a vertex image in a finite topological
triangulation. -/
theorem IsTriangulable.exists_vertex_image_of_compactSpace
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (htri : IsTriangulable.{w} X) {S : Set X} (hS : S.Finite) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι) (e : Realization K ≃ₜ X) (V : Set ι),
      Finite ι ∧ e '' (K.vertex '' V) = S := by
  obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff X).mp htri
  have := e.symm.compactSpace
  have hfin : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  obtain ⟨ι', _, K', e', V, hfin', -, hV⟩ :=
    K.exists_subdivision_vertex_image (hS.preimage e.injective.injOn)
  refine ⟨ι', K', e'.trans e, V, hfin' hfin, ?_⟩
  change (e ∘ e') '' (K'.vertex '' V) = S
  rw [Set.image_comp, hV, Set.image_preimage_eq _ e.surjective]

/-- Removing any finite subset from a compact triangulable space leaves a space of finite CW type.
No manifold, smoothness, connectedness, or dimension lower bound is needed. -/
theorem IsTriangulable.finiteCWType_compl
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (htri : IsTriangulable.{w} X) {S : Set X} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ := by
  have htri' : IsTriangulable.{u} X := htri.lift_of_compactSpace
  obtain ⟨ι, K, e, V, hfin, hV⟩ := htri'.exists_vertex_image_of_compactSpace hS
  have heq : e ⁻¹' Sᶜ = (K.vertex '' V)ᶜ := by
    rw [← hV, preimage_compl, e.injective.preimage_image]
  have := K.instFiniteCWTypeComplVertexImage V
  exact (e.sets heq.symm).symm.finiteCWType

/-- Removing any finite subset from a compact combinatorially triangulable space leaves a space
of finite CW type. -/
theorem IsCombinatoriallyTriangulable.finiteCWType_compl
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (htri : IsCombinatoriallyTriangulable.{w} X n) {S : Set X} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ :=
  htri.isTriangulable.finiteCWType_compl hS

end TauCeti
