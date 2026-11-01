/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing

/-!
# Subfamilies of open gluing data

Reindexing `TopCat.GlueData` selects pieces together with all their overlaps. The induced map
`reindexMap` from the selected gluing to the original gluing is an open embedding, with image
the union of the selected pieces. No injectivity of the index map is needed: repeated pieces
are identified by their full overlaps. In particular, an empty subfamily gives an empty open
subspace, and a subfamily covering the original gluing gives a homeomorphism.

The construction uses Mathlib's gluing carrier and multicoequalizer universal property.
The key injectivity argument uses the cocycle theorem `TopCat.GlueData.ι_eq_iff_rel`, so
identifications through omitted pieces introduce no additional identifications.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1
  (restriction of a gluing to a subfamily of charts).
-/

public section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace TopCat.GlueData

universe u

variable (D : TopCat.GlueData.{u}) {K L : Type u}

/-- Select pieces and all their overlaps along an index map. The body is exposed so that the
selected pieces and overlaps retain their original types and structures. -/
@[expose, instance_reducible]
def reindex (r : K → D.J) : TopCat.GlueData.{u} where
  J := K
  U i := D.U (r i)
  V ij := D.V (r ij.1, r ij.2)
  f i j := D.f (r i) (r j)
  t i j := D.t (r i) (r j)
  t_id i := D.t_id (r i)
  t' i j k := D.t' (r i) (r j) (r k)
  t_fac i j k := D.t_fac (r i) (r j) (r k)
  cocycle i j k := D.cocycle (r i) (r j) (r k)
  f_open i j := D.f_open (r i) (r j)

/-- Reindexing retains exactly the original relation between the selected pieces. -/
@[simp]
theorem reindex_rel (r : K → D.J) (i j : K) (x : D.U (r i)) (y : D.U (r j)) :
    (D.reindex r).Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D.Rel ⟨r i, x⟩ ⟨r j, y⟩ :=
  Iff.rfl

/-- The canonical continuous map from a selected gluing to the full gluing. -/
noncomputable def reindexMap (r : K → D.J) :
    (D.reindex r).toGlueData.glued ⟶ D.toGlueData.glued :=
  Multicoequalizer.desc _ _ (fun i ↦ D.toGlueData.ι (r i))
    (fun ⟨i, j⟩ ↦ (D.toGlueData.glue_condition (r i) (r j)).symm)

/-- The canonical map of a selected gluing agrees with the original inclusion on each piece. -/
@[simp]
theorem reindexMap_ι (r : K → D.J) (i : K) (x : D.U (r i)) :
    D.reindexMap r ((D.reindex r).toGlueData.ι i x) = D.toGlueData.ι (r i) x :=
  ConcreteCategory.congr_hom
    (Multicoequalizer.π_desc (D.reindex r).toGlueData.diagram _
      (fun i ↦ D.toGlueData.ι (r i)) _ i) x

/-- The image of the selected gluing is precisely the union of the selected pieces. -/
theorem range_reindexMap (r : K → D.J) :
    range (D.reindexMap r) = ⋃ i, range (D.toGlueData.ι (r i)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, z, rfl⟩ := (D.reindex r).ι_jointly_surjective y
    exact mem_iUnion.2 ⟨i, z, (D.reindexMap_ι r i z).symm⟩
  · intro hx
    obtain ⟨i, z, rfl⟩ := mem_iUnion.1 hx
    exact ⟨(D.reindex r).toGlueData.ι i z, D.reindexMap_ι r i z⟩

/-- Selecting a subfamily, even with repeated indices, embeds its gluing as an open subspace. -/
theorem isOpenEmbedding_reindexMap (r : K → D.J) : IsOpenEmbedding (D.reindexMap r) := by
  refine .of_continuous_injective_isOpenMap (D.reindexMap r).hom.continuous ?_ ?_
  · intro x y hxy
    obtain ⟨i, x, rfl⟩ := (D.reindex r).ι_jointly_surjective x
    obtain ⟨j, y, rfl⟩ := (D.reindex r).ι_jointly_surjective y
    rw [D.reindexMap_ι r i x, D.reindexMap_ι r j y] at hxy
    exact ((D.reindex r).ι_eq_iff_rel i j x y).2
      ((D.reindex_rel r i j x y).2 ((D.ι_eq_iff_rel _ _ _ _).1 hxy))
  · -- Test openness after the continuous surjection from the disjoint union of pieces.
    refine IsOpenMap.of_comp
      (f := fun x : Σ i, (D.reindex r).U i ↦ (D.reindex r).toGlueData.ι x.1 x.2)
      (continuous_sigma fun i ↦ ((D.reindex r).toGlueData.ι i).hom.continuous) ?_ ?_
    · intro x
      obtain ⟨i, y, rfl⟩ := (D.reindex r).ι_jointly_surjective x
      exact ⟨⟨i, y⟩, rfl⟩
    · apply isOpenMap_sigma.2
      intro i
      simpa only [Function.comp_def, D.reindexMap_ι] using
        (D.ι_isOpenEmbedding (r i)).isOpenMap

/-- The selected gluing covers the full gluing exactly when the selected pieces cover it. -/
theorem surjective_reindexMap_iff (r : K → D.J) :
    Function.Surjective (D.reindexMap r) ↔ ⋃ i, range (D.toGlueData.ι (r i)) = univ := by
  rw [← D.range_reindexMap, range_eq_univ]

/-- Reindexing by the identity induces the identity map on the glued space. -/
@[simp]
theorem reindexMap_id (x : (D.reindex id).toGlueData.glued) :
    D.reindexMap id x = x := by
  obtain ⟨i, y, rfl⟩ := (D.reindex id).ι_jointly_surjective x
  exact D.reindexMap_ι id i y

/-- Successive selections induce the composite of their canonical maps. -/
@[simp]
theorem reindexMap_comp (r : K → D.J) (s : L → K)
    (x : ((D.reindex r).reindex s).toGlueData.glued) :
    D.reindexMap r ((D.reindex r).reindexMap s x) = D.reindexMap (r ∘ s) x := by
  obtain ⟨i, y, rfl⟩ := ((D.reindex r).reindex s).ι_jointly_surjective x
  rw [(D.reindex r).reindexMap_ι s i y, D.reindexMap_ι r (s i) y]
  exact (D.reindexMap_ι (r ∘ s) i y).symm

end TopCat.GlueData
