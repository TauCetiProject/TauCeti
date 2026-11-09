/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Vertices
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.EulerCharacteristic

/-!
# Finite CW type of compact triangulable spaces

A compact space triangulated by a weak simplicial realization has finite CW type. Compactness
forces the triangulating complex to have finitely many vertices, hence finitely many faces;
the existing simplicial CW structure then supplies a Hausdorff finite CW model. In particular,
no local finiteness hypothesis on the supplied triangulation is needed.

This is the topological passage from a triangulation of a compact manifold to a finite CW
model, allowing homotopy invariants such as Euler characteristic to be applied to that manifold.
It does not construct a triangulation or assert that deleting points preserves finite CW type.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Appendix A, Proposition A.1
  (simplicial CW structures and compact subsets of weak complexes).
-/

public section

noncomputable section

namespace TauCeti

universe u v

/-- A compact triangulable space has finite CW type. The triangulation may be any weak
simplicial realization, in any universe; its finiteness follows from compactness. -/
theorem IsTriangulable.finiteCWType {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : IsTriangulable.{v} X) : FiniteCWType X := by
  obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff X).mp (h.lift_of_compactSpace : IsTriangulable.{u} X)
  have := e.symm.compactSpace
  have : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  exact e.symm.finiteCWType

end TauCeti
