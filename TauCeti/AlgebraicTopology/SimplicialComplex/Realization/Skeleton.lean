/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Skeleton
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex

/-!
# The skeletal filtration of a weak realization

The realization of the `n`-skeleton is precisely the closed subspace of points with at most
`n + 1` nonzero barycentric coordinates. These subspaces exhaust the realization, and continuity
out of the realization is detected on them. The skeleta carry their own weak realization topology,
which agrees with the subspace topology even for infinite complexes.

Simplicial maps preserve this filtration. If a map is injective on each face, it also reflects
skeletal membership: the dimension of the face carrying a point is preserved. These statements
give the skeletal part of cellularity and of compatibility with simplex characteristic maps.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (skeleta and cellular maps).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (the weak topology on a polyhedron).
-/

public section

noncomputable section

open Set Topology

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι)

/-- The realized skeleton consists exactly of the points carried by a face of dimension at most
`n`. -/
theorem range_realizationMap_skeleton (n : ℕ) :
    range (realizationMap (K.skeleton_le n)) = {x : Realization K | x.1.support.card ≤ n + 1} := by
  ext x
  simp only [mem_range_realizationMap, mem_skeleton, mem_ofPred_eq, and_iff_right (support_mem K x)]

/-- The points with at most `n + 1` nonzero coordinates form a closed subspace. -/
theorem isClosed_setOf_card_support_le (n : ℕ) :
    IsClosed {x : Realization K | x.1.support.card ≤ n + 1} := by
  rw [← range_realizationMap_skeleton]
  exact (isClosedEmbedding_realizationMap (K.skeleton_le n)).isClosed_range

/-- The skeletal filtration exhausts the realization, even in unbounded dimension. -/
theorem iUnion_range_realizationMap_skeleton :
    ⋃ n, range (realizationMap (K.skeleton_le n)) = univ := by
  simp only [range_realizationMap_skeleton]
  exact eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x.1.support.card, Nat.le_succ _⟩

/-- Continuity out of a weak realization can be tested on all its skeleta. -/
theorem continuous_iff_realizationMap_skeleton {X : Type*} [TopologicalSpace X]
    {f : Realization K → X} :
    Continuous f ↔ ∀ n, Continuous (f ∘ realizationMap (K.skeleton_le n)) := by
  refine ⟨fun hf n => hf.comp (continuous_realizationMap _), fun hf => ?_⟩
  apply continuous_iff_faceInclusion.mpr
  intro σ
  let τ : TauCeti.SetLike.Face (K.skeleton σ.1.card) :=
    ⟨σ.1, mem_skeleton.mpr ⟨σ.2, Nat.le_succ _⟩⟩
  have he := realizationMap_comp_faceInclusion (K.skeleton_le σ.1.card) τ
  rw [← he, ← Function.comp_assoc]
  exact (hf σ.1.card).comp (continuous_faceInclusion _ τ)

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.SimplicialMap

open AbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}

/-- Realizing the restriction to a skeleton commutes with the skeletal inclusions. -/
theorem realizationMap_skeleton
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (n : ℕ) :
    AbstractSimplicialComplex.realizationMap (L.skeleton_le n) ∘
        (f.skeleton n).realizationMap (K := K.skeleton n) (L := L.skeleton n) =
      f.realizationMap ∘ AbstractSimplicialComplex.realizationMap (K.skeleton_le n) := by
  funext x
  apply Subtype.ext
  simp only [Function.comp_apply, AbstractSimplicialComplex.realizationMap_val,
    realizationMap_val]
  congr 1
  funext v
  exact skeleton_apply f n v

/-- A simplicial realization cannot increase the number of nonzero barycentric coordinates. -/
theorem card_support_realizationMap_le
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (x : Realization K) : (f.realizationMap x).1.support.card ≤ x.1.support.card := by
  rw [realizationMap_val]
  exact (Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le

/-- A realized simplicial map sends each skeleton into the corresponding skeleton. -/
theorem mapsTo_realizationMap_skeleton
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (n : ℕ) : MapsTo f.realizationMap
      (range (AbstractSimplicialComplex.realizationMap (K.skeleton_le n)))
      (range (AbstractSimplicialComplex.realizationMap (L.skeleton_le n))) := by
  simp only [range_realizationMap_skeleton]
  exact fun x hx => (f.card_support_realizationMap_le x).trans hx

/-- Injectivity on the support of a point preserves its number of nonzero barycentric
coordinates. -/
theorem card_support_realizationMap_of_injOn
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (x : Realization K) (hf : InjOn f (x.1.support : Set ι)) :
    (f.realizationMap x).1.support.card = x.1.support.card := by
  rw [realizationMap_val, Finsupp.mapDomain_support_of_injOn x.1 hf]
  exact Finset.card_image_of_injOn hf

/-- A simplicial map injective on each face reflects skeletal membership as well as preserving
it. -/
theorem preimage_realizationMap_skeleton_of_injOn
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : ∀ σ ∈ K, InjOn f (σ : Set ι)) (n : ℕ) :
    f.realizationMap ⁻¹' range (AbstractSimplicialComplex.realizationMap (L.skeleton_le n)) =
      range (AbstractSimplicialComplex.realizationMap (K.skeleton_le n)) := by
  ext x
  simp only [range_realizationMap_skeleton, mem_preimage, mem_ofPred_eq,
    f.card_support_realizationMap_of_injOn x (hf _ (support_mem K x))]

end PreAbstractSimplicialComplex.SimplicialMap
