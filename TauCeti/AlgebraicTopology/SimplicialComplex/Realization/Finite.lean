/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex

/-!
# The topology of finite polyhedra

For a complex on finitely many vertices, the weak topology of its realization agrees with
its barycentric-coordinate topology. In particular, the realization is compact and its
coordinate map into `ι → ℝ` is a closed embedding. This permits finite polyhedra, including
finite local models of triangulated manifolds, to be treated as ordinary coordinate subspaces.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (polyhedra and their topology).
-/

public section

noncomputable section

open Set TauCeti.SetLike
open scoped Set.Notation

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

section Finite

variable (K : AbstractSimplicialComplex ι)

/-- The part of the full realization supported on a face of `K`. -/
private def coordinatePolyhedron : Set (Realization (⊤ : AbstractSimplicialComplex ι)) :=
  {x | x.1.support ∈ K}

private theorem isClosed_coordinatePolyhedron : IsClosed (coordinatePolyhedron K) :=
  isClosed_setOf_support_mem (P := K.toPreAbstractSimplicialComplex) le_top

/-- Recover a weak realization point from its coordinates in the full simplex. -/
private def fromCoordinates (x : coordinatePolyhedron K) : Realization K :=
  ⟨x.1.1, mem_realization_iff.mpr
    ⟨x.1.1.support, x.2, by simpa only [carrier_val] using mem_convexHull_carrier ⊤ x.1⟩⟩

private theorem fromCoordinates_surjective : Function.Surjective (fromCoordinates K) := by
  intro x
  refine ⟨⟨realizationMap le_top x, ?_⟩, Subtype.ext (realizationMap_val le_top x)⟩
  simpa only [coordinatePolyhedron, mem_ofPred_eq, realizationMap_val] using support_mem K x

private theorem continuous_fromCoordinates : Continuous (fromCoordinates K) := by
  apply (continuous_subtype_iff_faceInclusion
    (P := K.toPreAbstractSimplicialComplex) le_top).mpr
  intro σ hσ
  convert continuous_faceInclusion K ⟨σ, hσ⟩ using 1
  funext x
  apply Subtype.ext
  rw [faceInclusion_val]
  exact faceInclusion_val ⊤ ⟨σ, (le_top : K ≤ ⊤) hσ⟩ x

private theorem compactSpace_realization_of_nonempty [Finite ι] [Nonempty ι] :
    CompactSpace (Realization K) := by
  let := Fintype.ofFinite ι
  let : CompactSpace (Realization (⊤ : AbstractSimplicialComplex ι)) :=
    (realizationTopHomeomorphStdSimplex (ι := ι)).symm.compactSpace
  let : CompactSpace (coordinatePolyhedron K) :=
    isCompact_iff_compactSpace.mp (isClosed_coordinatePolyhedron K).isCompact
  exact Function.Surjective.compactSpace (continuous_fromCoordinates K)
    (fromCoordinates_surjective K)

end Finite

/-- The weak realization of a complex on a finite vertex type is compact. -/
instance instCompactSpaceRealization [Finite ι] (K : AbstractSimplicialComplex ι) :
    CompactSpace (Realization K) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have : IsEmpty (Realization K) := ⟨fun x => by
      obtain ⟨v, -⟩ := K.isRelLowerSet_faces.prop_of_mem (support_mem K x)
      exact isEmptyElim v⟩
    infer_instance
  | inr h => exact compactSpace_realization_of_nonempty K

/-- For a finite complex the barycentric-coordinate map is a closed embedding. Thus the weak
topology is exactly the topology inherited from the finite-dimensional coordinate space. -/
theorem isClosedEmbedding_realization_coe [Finite ι] (K : AbstractSimplicialComplex ι) :
    Topology.IsClosedEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) :=
  (continuous_realization_coe K).isClosedEmbedding fun _ _ h =>
    Subtype.ext (Finsupp.ext fun v => congrFun h v)

end AbstractSimplicialComplex
