/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
import Mathlib.Data.Fintype.Powerset

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

/-- The coordinate face spanned by `σ`, inside the full realization. -/
private def coordinateFace (σ : Finset ι) : Set (Realization (⊤ : AbstractSimplicialComplex ι)) :=
  {x | x.1.support ⊆ σ}

private theorem isClosed_coordinateFace (σ : Finset ι) : IsClosed (coordinateFace σ) := by
  have heq : coordinateFace σ =
      ⋂ v ∈ (σ : Set ι)ᶜ, {x : Realization (⊤ : AbstractSimplicialComplex ι) | x.1 v = 0} := by
    ext x
    simp only [coordinateFace, mem_ofPred, mem_iInter, mem_compl_iff, Finset.mem_coe]
    constructor
    · intro h v hv
      exact Finsupp.notMem_support_iff.mp (fun hx => hv (h hx))
    · intro h v hv
      by_contra hvσ
      exact Finsupp.mem_support_iff.mp hv (h v hvσ)
  rw [heq]
  exact isClosed_biInter fun v _ => isClosed_eq
    ((continuous_apply v).comp (continuous_realization_coe ⊤)) continuous_const

/-- The part of the full realization supported on a face of `K`. -/
private def coordinatePolyhedron : Set (Realization (⊤ : AbstractSimplicialComplex ι)) :=
  {x | x.1.support ∈ K}

private theorem coordinatePolyhedron_eq_iUnion :
    coordinatePolyhedron K = ⋃ σ : Face K, coordinateFace σ.1 := by
  ext x
  simp only [coordinatePolyhedron, mem_ofPred_eq, mem_iUnion, coordinateFace]
  constructor
  · intro hx
    exact ⟨⟨x.1.support, hx⟩, Finset.Subset.rfl⟩
  · rintro ⟨σ, hσ⟩
    exact K.isRelLowerSet_faces.mem_of_le σ.2 hσ
      ((⊤ : AbstractSimplicialComplex ι).isRelLowerSet_faces.prop_of_mem (support_mem ⊤ x))

private theorem isClosed_coordinatePolyhedron [Finite ι] : IsClosed (coordinatePolyhedron K) := by
  let := Fintype.ofFinite ι
  rw [coordinatePolyhedron_eq_iUnion]
  exact isClosed_iUnion_of_finite fun σ => isClosed_coordinateFace σ.1

/-- Recover a weak realization point from its coordinates in the full simplex. -/
private def fromCoordinates (x : coordinatePolyhedron K) : Realization K :=
  ⟨x.1.1, mem_realization_iff.mpr
    ⟨x.1.1.support, x.2, by simpa only [carrier_val] using mem_convexHull_carrier ⊤ x.1⟩⟩

private theorem fromCoordinates_surjective : Function.Surjective (fromCoordinates K) := by
  intro x
  refine ⟨⟨realizationMap le_top x, ?_⟩, Subtype.ext (realizationMap_val le_top x)⟩
  simpa only [coordinatePolyhedron, mem_ofPred_eq, realizationMap_val] using support_mem K x

private def faceFromCoordinates (σ : Face K)
    (x : (coordinatePolyhedron K) ↓∩ coordinateFace σ.1) : StandardSimplex σ.1 :=
  ⟨x.1.1.1, by
    rw [Finset.coe_image, mem_standardSimplex_iff]
    refine ⟨Realization.nonneg ⊤ x.1.1, ?_, x.2⟩
    exact StandardSimplex.sum_eq_one (σ := (carrier ⊤ x.1.1).1)
      ⟨x.1.1.1, mem_convexHull_carrier ⊤ x.1.1⟩⟩

private theorem continuous_fromCoordinates [Finite ι] : Continuous (fromCoordinates K) := by
  let := Fintype.ofFinite ι
  let C : Face K → Set (coordinatePolyhedron K) :=
    fun σ => (coordinatePolyhedron K) ↓∩ coordinateFace σ.1
  have hC : ∀ σ, IsClosed (C σ) := fun σ =>
    (isClosed_coordinateFace σ.1).preimage continuous_subtype_val
  have hcover : ⋃ σ, C σ = univ := by
    ext x
    simp only [C, mem_iUnion, mem_preimage, mem_univ, iff_true]
    exact ⟨⟨x.1.1.support, x.2⟩, Finset.Subset.rfl⟩
  apply (locallyFinite_of_finite C).continuous hcover hC
  intro σ
  rw [continuousOn_iff_continuous_domRestrict]
  have hface : Continuous (faceFromCoordinates K σ) := by
    apply continuous_induced_rng.mpr
    exact (continuous_realization_coe ⊤).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  exact ((continuous_faceInclusion K σ).comp hface).congr fun x => by
    apply Subtype.ext
    rw [Function.comp_apply, faceInclusion_val]
    rfl

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
