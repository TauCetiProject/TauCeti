/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod

/-!
# Products of glued manifold atlases

For two open gluings, pairs of canonical inclusions form an open cover of the product of their
existing glued carriers. `TopCat.GlueData.prodChartedSpace` glues the product charts of the
pieces along this cover. If both gluings are compatible, the result is a manifold and the
identity map identifies it diffeomorphically with the ordinary product of the two glued
manifolds (`TopCat.GlueData.IsCompatible.prodDiffeomorph`). Thus forming the glued atlas
commutes with products, without changing the topological carrier or assuming that the
chosen charts in the two constructions coincide.

The maximal atlases agree, and smoothness on the ordinary product can be tested on all pairs
of pieces. These statements also apply to holomorphic gluings. Neither nonempty pieces nor
separation or countability assumptions are needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1
  (the smooth manifold chart lemma and products of manifolds).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u v

variable (D : TopCat.GlueData.{u}) (D' : TopCat.GlueData.{v})

private theorem prod_ι_cover (x : D.toGlueData.glued × D'.toGlueData.glued) :
    ∃ (ij : D.J × D'.J) (y : D.U ij.1 × D'.U ij.2),
      Prod.map (D.toGlueData.ι ij.1) (D'.toGlueData.ι ij.2) y = x := by
  obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x.1
  obtain ⟨j, z, hz⟩ := D'.ι_jointly_surjective x.2
  exact ⟨(i, j), (y, z), Prod.ext hy hz⟩

variable {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  [∀ i, ChartedSpace H (D.U i)] [∀ j, ChartedSpace H' (D'.U j)]

/-- Glue the product charts of pairs of pieces, on the product of the existing glued carriers.
This is a named atlas, not a global instance competing with the ordinary product atlas. -/
@[instance_reducible]
noncomputable def prodChartedSpace :
    ChartedSpace (ModelProd H H') (D.toGlueData.glued × D'.toGlueData.glued) :=
  TauCeti.chartedSpaceOfIsOpenEmbedding
    (fun ij : D.J × D'.J ↦ (D.ι_isOpenEmbedding ij.1).prodMap (D'.ι_isOpenEmbedding ij.2))
    (D.prod_ι_cover D')

/-- The chosen chart in the product gluing comes from a pair of pieces containing the point,
using the inverse of their product inclusion followed by their product chart. -/
theorem exists_chartAt_prodChartedSpace_eq
    (x : D.toGlueData.glued × D'.toGlueData.glued) :
    ∃ (ij : D.J × D'.J) (y : D.U ij.1 × D'.U ij.2),
      Prod.map (D.toGlueData.ι ij.1) (D'.toGlueData.ι ij.2) y = x ∧
        haveI : Nonempty (D.U ij.1 × D'.U ij.2) := ⟨y⟩
        @chartAt (ModelProd H H') _ _ _ (D.prodChartedSpace D') x =
          (((D.ι_isOpenEmbedding ij.1).prodMap (D'.ι_isOpenEmbedding ij.2)
            ).toOpenPartialHomeomorph _).symm.trans (chartAt (ModelProd H H') y) :=
  TauCeti.exists_chartAt_chartedSpaceOfIsOpenEmbedding_eq
    (fun ij : D.J × D'.J ↦ (D.ι_isOpenEmbedding ij.1).prodMap (D'.ι_isOpenEmbedding ij.2))
    (D.prod_ι_cover D') x

variable {D D'} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  [∀ ij, ChartedSpace H (D.V ij)] [∀ ij, ChartedSpace H' (D'.V ij)]

namespace IsCompatible

variable (h : D.IsCompatible I n) (h' : D'.IsCompatible I' n)

include h h'

private theorem prod_transition (ij kl : D.J × D'.J)
    (x : D.U ij.1 × D'.U ij.2) (y : D.U kl.1 × D'.U kl.2)
    (hxy : Prod.map (D.toGlueData.ι ij.1) (D'.toGlueData.ι ij.2) x =
      Prod.map (D.toGlueData.ι kl.1) (D'.toGlueData.ι kl.2) y) :
    ∃ T : D.U ij.1 × D'.U ij.2 → D.U kl.1 × D'.U kl.2,
      ContMDiffAt (I.prod I') (I.prod I') n T x ∧
        Prod.map (D.toGlueData.ι kl.1) (D'.toGlueData.ι kl.2) ∘ T =ᶠ[𝓝 x]
          Prod.map (D.toGlueData.ι ij.1) (D'.toGlueData.ι ij.2) := by
  obtain ⟨T, hT, heq⟩ := h.exists_contMDiffAt_transition (congrArg Prod.fst hxy)
  obtain ⟨T', hT', heq'⟩ := h'.exists_contMDiffAt_transition (congrArg Prod.snd hxy)
  refine ⟨Prod.map T T', hT.prodMap hT', ?_⟩
  exact heq.prodMap_nhds heq'

variable [∀ i, IsManifold I n (D.U i)] [∀ j, IsManifold I' n (D'.U j)]

/-- Compatible gluings give a manifold when the product charts of their pieces are glued
on the product carrier. -/
theorem isManifold_prodChartedSpace :
    letI := D.prodChartedSpace D' (H := H) (H' := H')
    IsManifold (I.prod I') n (D.toGlueData.glued × D'.toGlueData.glued) :=
  TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding
    (fun ij : D.J × D'.J ↦ (D.ι_isOpenEmbedding ij.1).prodMap (D'.ι_isOpenEmbedding ij.2))
    (D.prod_ι_cover D') (h.prod_transition h')

/-- Pairs of canonical inclusions are local diffeomorphisms for the atlas glued from product
pieces, including when one of the pieces is empty. -/
theorem isLocalDiffeomorph_prod_ι (ij : D.J × D'.J) :
    letI := D.prodChartedSpace D' (H := H) (H' := H')
    IsLocalDiffeomorph (I.prod I') (I.prod I') n
      (Prod.map (D.toGlueData.ι ij.1) (D'.toGlueData.ι ij.2)) :=
  TauCeti.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
    (fun ij : D.J × D'.J ↦ (D.ι_isOpenEmbedding ij.1).prodMap (D'.ι_isOpenEmbedding ij.2))
    (D.prod_ι_cover D') (h.prod_transition h') ij

/-- Gluing product charts and taking the product of the glued manifolds give the same maximal
atlas, although the chosen chart at a point can differ. -/
theorem maximalAtlas_prodChartedSpace_eq :
    (letI := D.prodChartedSpace D' (H := H) (H' := H')
     maximalAtlas (I.prod I') n (D.toGlueData.glued × D'.toGlueData.glued)) =
    (letI := D.chartedSpace H
     letI := D'.chartedSpace H'
     maximalAtlas (I.prod I') n (D.toGlueData.glued × D'.toGlueData.glued)) := by
  let := D.chartedSpace H
  let := D'.chartedSpace H'
  let := h.isManifold
  let := h'.isManifold
  exact TauCeti.maximalAtlas_eq_of_forall_isLocalDiffeomorph (D.prod_ι_cover D')
    (h.isManifold_prodChartedSpace h') inferInstance
    (h.isLocalDiffeomorph_prod_ι h')
    (fun ij ↦ (h.isLocalDiffeomorph_ι ij.1).prodMap (h'.isLocalDiffeomorph_ι ij.2))

/-- The identity diffeomorphism from the atlas glued from pairs of pieces to the ordinary
product of the glued manifolds. Both structures live on the same topological carrier. -/
noncomputable def prodDiffeomorph (h : D.IsCompatible I n) (h' : D'.IsCompatible I' n) :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _
      (I.prod I') (I.prod I') (D.toGlueData.glued × D'.toGlueData.glued) _
      (D.prodChartedSpace D') (D.toGlueData.glued × D'.toGlueData.glued) _
      inferInstance n := by
  letI := D.chartedSpace H
  letI := D'.chartedSpace H'
  have hid : @IsLocalDiffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _
      (I.prod I') (I.prod I') (D.toGlueData.glued × D'.toGlueData.glued) _
      (D.prodChartedSpace D') (D.toGlueData.glued × D'.toGlueData.glued) _
      inferInstance n id := by
    -- Specify the source atlas explicitly: the target uses the ordinary product atlas.
    exact (@TauCeti.isLocalDiffeomorph_iff_forall_comp 𝕜 _ _ _ _ _ _ (I.prod I') n
      _ _ _ _ _ _ _ (D.prod_ι_cover D') (D.prodChartedSpace D')
      (h.isLocalDiffeomorph_prod_ι h') _ _ _ _ _ (I.prod I') _ _ inferInstance id).2
        (fun ij ↦ (h.isLocalDiffeomorph_ι ij.1).prodMap (h'.isLocalDiffeomorph_ι ij.2))
  exact @IsLocalDiffeomorph.diffeomorphOfBijective 𝕜 _ _ _ _ _ _ _ _ _ _ _
    (I.prod I') (I.prod I') _ _ (D.prodChartedSpace D') _ _ inferInstance n id
    hid Function.bijective_id

/-- The product comparison fixes every point. -/
@[simp]
theorem prodDiffeomorph_apply (x : D.toGlueData.glued × D'.toGlueData.glued) :
    h.prodDiffeomorph h' x = x := by
  simp [prodDiffeomorph]

/-- Forgetting smoothness gives the identity equivalence, in both directions. -/
@[simp]
theorem prodDiffeomorph_toEquiv :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    @Diffeomorph.toEquiv 𝕜 _ _ _ _ _ _ _ _ _ _ _ (I.prod I') (I.prod I')
      _ _ (D.prodChartedSpace D') _ _ inferInstance n (h.prodDiffeomorph h') = Equiv.refl _ :=
  Equiv.ext (h.prodDiffeomorph_apply h')

/-- A map on the ordinary product of glued manifolds is smooth exactly when it is smooth on
all pairs of pieces. This tests joint smoothness, not merely separate smoothness. -/
theorem contMDiff_prod_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners 𝕜 F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] {m : ℕ∞ω} (hm : m ≤ n)
    {f : D.toGlueData.glued × D'.toGlueData.glued → N} :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    ContMDiff (I.prod I') J m f ↔ ∀ i j,
      ContMDiff (I.prod I') J m (f ∘ Prod.map (D.toGlueData.ι i) (D'.toGlueData.ι j)) := by
  let := D.chartedSpace H
  let := D'.chartedSpace H'
  constructor
  · intro hf i j
    exact hf.comp (((h.isLocalDiffeomorph_ι i).prodMap
      (h'.isLocalDiffeomorph_ι j)).contMDiff.of_le hm)
  · intro hf x
    obtain ⟨⟨i, j⟩, y, rfl⟩ := D.prod_ι_cover D' x
    exact (((h.isLocalDiffeomorph_ι i y.1).prodMap
      (h'.isLocalDiffeomorph_ι j y.2)).contMDiffAt_comp_iff hm).1 (hf i j y)

end IsCompatible

end TopCat.GlueData
