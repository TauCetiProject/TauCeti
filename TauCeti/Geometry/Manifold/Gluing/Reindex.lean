/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.GlueData.Reindex
public import TauCeti.Geometry.Manifold.Gluing.GlueData

/-!
# Restricting compatible manifold gluings to subfamilies

A subfamily of compatible open gluing data, with all its inherited overlaps, is compatible.
The canonical map `TopCat.GlueData.reindexMap` is a local diffeomorphism for the named glued
atlases. Together with `TopCat.GlueData.isOpenEmbedding_reindexMap`, this identifies the
selected gluing as an open submanifold of the original gluing, with image the union of the
selected pieces. If those pieces still cover, `reindexDiffeomorph` is the comparison
diffeomorphism. These statements allow repeated indices and empty pieces or index types.
For the complex field they apply to holomorphic gluings without changing the carrier.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1
  (restriction and refinement of smooth atlases).
-/

public section

open Set Topology
open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u

variable {D : TopCat.GlueData.{u}} {K : Type u}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [∀ i, ChartedSpace H (D.U i)] [∀ ij, ChartedSpace H (D.V ij)]

/-- Selecting pieces with their inherited overlaps preserves compatibility of manifold atlases. -/
theorem IsCompatible.reindex (h : D.IsCompatible I n) (r : K → D.J) :
    (D.reindex r).IsCompatible I n where
  isLocalDiffeomorph_f i j := h.isLocalDiffeomorph_f (r i) (r j)
  isLocalDiffeomorph_f_comp_t i j := h.isLocalDiffeomorph_f_comp_t (r i) (r j)

variable [∀ i, IsManifold I n (D.U i)]

/-- The inclusion of a selected gluing in the full gluing is a local diffeomorphism for their
named atlases. In particular, it identifies the selected gluing with an open submanifold. -/
theorem IsCompatible.isLocalDiffeomorph_reindexMap (h : D.IsCompatible I n) (r : K → D.J) :
    letI := D.chartedSpace H
    letI := (D.reindex r).chartedSpace H
    IsLocalDiffeomorph I I n (D.reindexMap r) := by
  let := D.chartedSpace H
  let := (D.reindex r).chartedSpace H
  apply ((h.reindex r).isLocalDiffeomorph_iff).2
  intro i
  have heq : D.reindexMap r ∘ (D.reindex r).toGlueData.ι i = D.toGlueData.ι (r i) :=
    funext (D.reindexMap_ι r i)
  rw [heq]
  exact h.isLocalDiffeomorph_ι (r i)

/-- A selected family that still covers gives the same manifold, through the canonical map
on the existing glued carriers. -/
noncomputable def IsCompatible.reindexDiffeomorph (h : D.IsCompatible I n) (r : K → D.J)
    (hcover : ⋃ i, range (D.toGlueData.ι (r i)) = univ) :
    letI := D.chartedSpace H
    letI := (D.reindex r).chartedSpace H
    (D.reindex r).toGlueData.glued ≃ₘ^n⟮I, I⟯ D.toGlueData.glued := by
  letI := D.chartedSpace H
  letI := (D.reindex r).chartedSpace H
  exact (h.isLocalDiffeomorph_reindexMap r).diffeomorphOfBijective
    ⟨(D.isOpenEmbedding_reindexMap r).injective, (D.surjective_reindexMap_iff r).2 hcover⟩

/-- The covering-subfamily comparison is the canonical map, not an independently chosen
identification of glued spaces. -/
@[simp]
theorem IsCompatible.coe_reindexDiffeomorph (h : D.IsCompatible I n) (r : K → D.J)
    (hcover : ⋃ i, range (D.toGlueData.ι (r i)) = univ) :
    ⇑(h.reindexDiffeomorph r hcover) = D.reindexMap r := by
  let := D.chartedSpace H
  let := (D.reindex r).chartedSpace H
  exact IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

end TopCat.GlueData
