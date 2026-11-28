/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Vertices
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.EulerCharacteristic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.VertexPlacement
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Complement

/-!
# Finite CW type of compact triangulable spaces

A compact space triangulated by a weak simplicial realization has finite CW type. Compactness
forces the triangulating complex to have finitely many vertices, hence finitely many faces;
the existing simplicial CW structure then supplies a Hausdorff finite CW model. In particular,
no local finiteness hypothesis on the supplied triangulation is needed.

Moreover, any finite subset `S` of a compact triangulable space can be realized as a vertex image
in some finite triangulation (`TauCeti.IsTriangulable.exists_vertex_image_of_compactSpace`), so
passing to the complement model in the barycentric subdivision shows that deleting any finite
subset preserves `TauCeti.FiniteCWType` (`TauCeti.IsTriangulable.finiteCWType_compl`).

## Main results

* `TauCeti.IsTriangulable.finiteCWType`: a compact triangulable space has finite CW type.
* `TauCeti.IsTriangulable.exists_vertex_image_of_compactSpace`: every finite subset of a compact
  triangulable space is a vertex image in a finite triangulation.
* `TauCeti.IsTriangulable.finiteCWType_compl`: removing any finite subset from a compact
  triangulable space leaves a space of finite CW type.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Appendix A, Proposition A.1
  (simplicial CW structures and compact subsets of weak complexes).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2–3 (stellar subdivision and complements of subpolyhedra).
-/

public section

noncomputable section

open AbstractSimplicialComplex Set

namespace TauCeti

universe u v w

attribute [local instance] Classical.decEq

/-- A compact triangulable space has finite CW type. The triangulation may be any weak
simplicial realization, in any universe; its finiteness follows from compactness. -/
theorem IsTriangulable.finiteCWType {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : IsTriangulable.{v} X) : FiniteCWType X := by
  obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff X).mp (h.lift_of_compactSpace : IsTriangulable.{u} X)
  have := e.symm.compactSpace
  have : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  exact e.symm.finiteCWType

/-- Every finite subset of a compact triangulable space is the image of a vertex set in some
finite complex `K'` and homeomorphism `e : Realization K' ≃ₜ X`. -/
theorem IsTriangulable.exists_vertex_image_of_compactSpace
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (htri : IsTriangulable.{w} X) {S : Set X} (hS : S.Finite) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι) (e : Realization K ≃ₜ X) (V : Set ι),
      Finite ι ∧ e '' (K.vertex '' V) = S := by
  obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff X).mp htri
  have := e.symm.compactSpace
  have hfin : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  obtain ⟨ι', _, K', e', V, hfin', -, hV⟩ :=
    K.exists_homeomorph_vertex_image_of_homeomorph e hS
  exact ⟨ι', K', e', V, hfin' hfin, hV⟩

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

end TauCeti
