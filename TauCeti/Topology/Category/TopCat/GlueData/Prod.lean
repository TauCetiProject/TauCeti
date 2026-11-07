/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.GlueData

/-!
# Products of open gluing data

`TopCat.GlueData.MkCore.prod` forms the product of two systems of open transition maps.
Its pieces are the products of pieces, its overlaps are the products of overlaps, and its
transitions act componentwise. `TopCat.GlueData.MkCore.prodGlueHomeomorph` identifies the
resulting glued space with the product of the two original glued spaces. No local compactness,
separation, countability, or nonemptiness assumption is needed: openness of the canonical
inclusions suffices.

The comparison is characterized on every product piece, so it can also be used to compare
structures defined locally on those pieces, such as smooth or complex atlases.

## References

* N. Bourbaki, *General Topology*, Chapter I, §4 (quotient spaces).
* The glued carriers and their universal property are Mathlib's `TopCat.GlueData.mk'` and
  `CategoryTheory.Limits.Multicoequalizer.desc`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Set

namespace TopCat.GlueData.MkCore

universe u

variable (D E : TopCat.GlueData.MkCore.{u})

/-- Product transition data: a piece is a product of pieces, and both the overlap condition
and the transition map are componentwise. -/
-- The index and piece types must compute when this transition data is used by mk'.
@[expose]
def prod : TopCat.GlueData.MkCore.{u} where
  J := D.J × E.J
  U i := TopCat.of (D.U i.1 × E.U i.2)
  V i j := ⟨(D.V i.1 j.1 : Set (D.U i.1)) ×ˢ E.V i.2 j.2,
    (D.V i.1 j.1).isOpen.prod (E.V i.2 j.2).isOpen⟩
  t i j := TopCat.ofHom ⟨fun x ↦
    ⟨((D.t i.1 j.1 ⟨x.1.1, x.2.1⟩).1, (E.t i.2 j.2 ⟨x.1.2, x.2.2⟩).1),
      (D.t i.1 j.1 ⟨x.1.1, x.2.1⟩).2, (E.t i.2 j.2 ⟨x.1.2, x.2.2⟩).2⟩,
    by
      apply Continuous.subtype_mk
      exact ((D.t i.1 j.1).hom.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).subtype_mk
          (fun x ↦ x.2.1))).subtype_val.prodMk
          (((E.t i.2 j.2).hom.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun x ↦ x.2.2))).subtype_val)⟩
  V_id i := by ext x; simp [D.V_id, E.V_id]
  t_id i := by
    funext x
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (congrFun (D.t_id i.1) ⟨x.1.1, x.2.1⟩))
      (congrArg Subtype.val (congrFun (E.t_id i.2) ⟨x.1.2, x.2.2⟩))
  t_inter {i j} k x hx := ⟨D.t_inter k.1 ⟨x.1.1, x.2.1⟩ hx.1,
    E.t_inter k.2 ⟨x.1.2, x.2.2⟩ hx.2⟩
  cocycle i j k x hx := Prod.ext
    (D.cocycle i.1 j.1 k.1 ⟨x.1.1, x.2.1⟩ hx.1)
    (E.cocycle i.2 j.2 k.2 ⟨x.1.2, x.2.2⟩ hx.2)

/-- The pieces of the product data are the products of the original pieces. -/
@[simp]
theorem prod_U (i : D.J × E.J) :
    (D.prod E).U i = TopCat.of (D.U i.1 × E.U i.2) := (rfl)

/-- A point belongs to a product overlap exactly when both coordinates belong to the
corresponding original overlaps. -/
@[simp]
theorem mem_prod_V (i j : D.J × E.J) (x : D.U i.1 × E.U i.2) :
    x ∈ (D.prod E).V i j ↔ x.1 ∈ D.V i.1 j.1 ∧ x.2 ∈ E.V i.2 j.2 := Iff.rfl

/-- A product transition applies the original transitions to the two coordinates. -/
@[simp]
theorem prod_t_apply (i j : D.J × E.J) (x : (D.prod E).V i j) :
    ((D.prod E).t i j x).1 =
      ((D.t i.1 j.1 ⟨x.1.1, x.2.1⟩).1, (E.t i.2 j.2 ⟨x.1.2, x.2.2⟩).1) := (rfl)

/-- Two points in product pieces are identified precisely when their two coordinates are
identified by the original gluing data. -/
@[simp]
theorem prod_rel_iff (i j : D.J × E.J) (x : D.U i.1 × E.U i.2)
    (y : D.U j.1 × E.U j.2) :
    (TopCat.GlueData.mk' (D.prod E)).Rel ⟨i, x⟩ ⟨j, y⟩ ↔
      (TopCat.GlueData.mk' D).Rel ⟨i.1, x.1⟩ ⟨j.1, y.1⟩ ∧
      (TopCat.GlueData.mk' E).Rel ⟨i.2, x.2⟩ ⟨j.2, y.2⟩ := by
  constructor
  · rintro ⟨z, hz, ht⟩
    exact ⟨⟨⟨z.1.1, z.2.1⟩, congrArg Prod.fst hz, congrArg Prod.fst ht⟩,
      ⟨⟨z.1.2, z.2.2⟩, congrArg Prod.snd hz, congrArg Prod.snd ht⟩⟩
  · rintro ⟨⟨z, hz, ht⟩, ⟨w, hw, hu⟩⟩
    exact ⟨⟨(z.1, w.1), z.2, w.2⟩, Prod.ext hz hw, Prod.ext ht hu⟩

private def prodPieceMap (i : D.J × E.J) :
    (TopCat.GlueData.mk' (D.prod E)).U i ⟶
      TopCat.of ((TopCat.GlueData.mk' D).toGlueData.glued ×
        (TopCat.GlueData.mk' E).toGlueData.glued) :=
  TopCat.ofHom ⟨fun x ↦ ((TopCat.GlueData.mk' D).toGlueData.ι i.1 x.1,
    (TopCat.GlueData.mk' E).toGlueData.ι i.2 x.2),
    (((TopCat.GlueData.mk' D).toGlueData.ι i.1).hom.continuous.comp continuous_fst).prodMk
      (((TopCat.GlueData.mk' E).toGlueData.ι i.2).hom.continuous.comp continuous_snd)⟩

private theorem prodPieceMap_condition (i j : D.J × E.J) :
    (TopCat.GlueData.mk' (D.prod E)).f i j ≫ prodPieceMap D E i =
      (TopCat.GlueData.mk' (D.prod E)).t i j ≫
        (TopCat.GlueData.mk' (D.prod E)).f j i ≫ prodPieceMap D E j := by
  ext x
  · exact ((TopCat.GlueData.mk' D).glue_condition_apply i.1 j.1 ⟨x.1.1, x.2.1⟩).symm
  · exact ((TopCat.GlueData.mk' E).glue_condition_apply i.2 j.2 ⟨x.1.2, x.2.2⟩).symm

/-- The canonical continuous map from the glued product data to the product of the glued
spaces. It sends each point of a product piece to the pair of its canonical images. -/
def prodGlueMap :
    C((TopCat.GlueData.mk' (D.prod E)).toGlueData.glued,
      (TopCat.GlueData.mk' D).toGlueData.glued × (TopCat.GlueData.mk' E).toGlueData.glued) :=
  (Multicoequalizer.desc (TopCat.GlueData.mk' (D.prod E)).toGlueData.diagram
    (TopCat.of ((TopCat.GlueData.mk' D).toGlueData.glued ×
      (TopCat.GlueData.mk' E).toGlueData.glued)) (prodPieceMap D E)
    (fun ⟨i, j⟩ ↦ prodPieceMap_condition D E i j)).hom

/-- The product comparison has its prescribed value on each piece. -/
@[simp]
theorem prodGlueMap_ι (i : D.J × E.J) (x : D.U i.1 × E.U i.2) :
    D.prodGlueMap E ((TopCat.GlueData.mk' (D.prod E)).toGlueData.ι i x) =
      ((TopCat.GlueData.mk' D).toGlueData.ι i.1 x.1,
        (TopCat.GlueData.mk' E).toGlueData.ι i.2 x.2) := by
  exact ConcreteCategory.congr_hom (Multicoequalizer.π_desc
    (TopCat.GlueData.mk' (D.prod E)).toGlueData.diagram
    (TopCat.of ((TopCat.GlueData.mk' D).toGlueData.glued ×
      (TopCat.GlueData.mk' E).toGlueData.glued)) (prodPieceMap D E)
      (fun ⟨i, j⟩ ↦ prodPieceMap_condition D E i j) i) x

/-- The comparison of glued products is injective: equality in each factor supplies the two
components of a single product-overlap witness. -/
theorem prodGlueMap_injective : Function.Injective (D.prodGlueMap E) := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := (TopCat.GlueData.mk' (D.prod E)).ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := (TopCat.GlueData.mk' (D.prod E)).ι_jointly_surjective y
  rw [prodGlueMap_ι D E i x, prodGlueMap_ι D E j y, Prod.mk.injEq] at h
  rw [(TopCat.GlueData.mk' (D.prod E)).ι_eq_iff_rel]
  apply (prod_rel_iff D E i j x y).2
  exact ⟨((TopCat.GlueData.mk' D).ι_eq_iff_rel _ _ _ _).1 h.1,
    ((TopCat.GlueData.mk' E).ι_eq_iff_rel _ _ _ _).1 h.2⟩

/-- Every pair of glued points has a representative in a product piece, even when some of
the original pieces are empty. -/
theorem prodGlueMap_surjective : Function.Surjective (D.prodGlueMap E) := by
  rintro ⟨x, y⟩
  obtain ⟨i, x, rfl⟩ := (TopCat.GlueData.mk' D).ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := (TopCat.GlueData.mk' E).ι_jointly_surjective y
  exact ⟨(TopCat.GlueData.mk' (D.prod E)).toGlueData.ι (i, j) (x, y),
    prodGlueMap_ι D E _ _⟩

/-- The product comparison is open because its composite with each piece inclusion is the
product of two open embeddings. -/
theorem isOpenMap_prodGlueMap : IsOpenMap (D.prodGlueMap E) := by
  apply (TopCat.GlueData.mk' (D.prod E)).isOpenQuotientMap_sigma_ι.isOpenMap_iff.2
  apply isOpenMap_sigma.2
  intro i
  have heq : (fun x ↦ D.prodGlueMap E
      ((TopCat.GlueData.mk' (D.prod E)).toGlueData.ι i x)) =
      Prod.map ((TopCat.GlueData.mk' D).toGlueData.ι i.1)
        ((TopCat.GlueData.mk' E).toGlueData.ι i.2) := funext (prodGlueMap_ι D E i)
  dsimp only [Function.comp_def]
  rw [heq]
  exact ((TopCat.GlueData.mk' D).ι_isOpenEmbedding i.1).isOpenMap.prodMap
    ((TopCat.GlueData.mk' E).ι_isOpenEmbedding i.2).isOpenMap

/-- Gluing product transition data gives the product of the original glued spaces. This
homeomorphism is canonical on every product piece and requires no separation or compactness. -/
def prodGlueHomeomorph :
    (TopCat.GlueData.mk' (D.prod E)).toGlueData.glued ≃ₜ
      (TopCat.GlueData.mk' D).toGlueData.glued × (TopCat.GlueData.mk' E).toGlueData.glued :=
  (Equiv.ofBijective (D.prodGlueMap E)
    ⟨prodGlueMap_injective D E, prodGlueMap_surjective D E⟩).toHomeomorphOfContinuousOpen
      (D.prodGlueMap E).continuous (isOpenMap_prodGlueMap D E)

/-- The homeomorphism retains the canonical product comparison as its continuous map. -/
@[simp]
theorem coe_prodGlueHomeomorph :
    ⇑(D.prodGlueHomeomorph E) = D.prodGlueMap E := (rfl)

/-- The inverse comparison glues any pair of piece representatives into the product piece. -/
@[simp]
theorem prodGlueHomeomorph_symm_ι (i : D.J × E.J) (x : D.U i.1 × E.U i.2) :
    (D.prodGlueHomeomorph E).symm
        ((TopCat.GlueData.mk' D).toGlueData.ι i.1 x.1,
          (TopCat.GlueData.mk' E).toGlueData.ι i.2 x.2) =
      (TopCat.GlueData.mk' (D.prod E)).toGlueData.ι i x := by
  apply (D.prodGlueHomeomorph E).injective
  rw [Homeomorph.apply_symm_apply, coe_prodGlueHomeomorph, prodGlueMap_ι]

end TopCat.GlueData.MkCore
