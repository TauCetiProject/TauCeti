/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import TauCeti.CategoryTheory.Products.Preadditive
public import TauCeti.CategoryTheory.Shift.Prod

/-!
# Products of pretriangulated categories

The product `C × D` of two pretriangulated categories is pretriangulated for the componentwise
shift of `TauCeti/CategoryTheory/Shift/Prod.lean`: a triangle is distinguished exactly when its
images under the two projections are distinguished. Each axiom is checked coordinatewise, the
rotation axiom through `CategoryTheory.Functor.mapTriangleRotateIso`.

The projections, the two zero sections, and products of triangulated functors are triangulated
functors. These are the functors through which triangulated Grothendieck groups of products are
compared with those of the factors.

## Main definitions

* The `CategoryTheory.Pretriangulated` instance on `C × D`.

## Main results

* `TauCeti.mem_distTriang_prod_iff`: a triangle in `C × D` is distinguished if and only if both
  of its projections are.
* `CategoryTheory.Functor.IsTriangulated` instances for `CategoryTheory.Prod.fst C D`,
  `CategoryTheory.Prod.snd C D`, `CategoryTheory.Prod.sectL C 0`,
  `CategoryTheory.Prod.sectR 0 D`, and `F.prod G` for triangulated functors `F` and `G`.

## Implementation notes

As in `TauCeti/CategoryTheory/Shift/Prod.lean`, the third morphism of a triangle mapped along one
of these functors involves a commutation isomorphism whose relevant coordinate is an identity
only up to unfolding the shift on `C × D`. The corresponding square of each triangle
isomorphism is therefore closed by an explicit identity in the factor.
-/

public section

namespace TauCeti

open CategoryTheory Limits Pretriangulated ZeroObject

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  (D : Type u₂) [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- The componentwise shift functors on a product of preadditive categories are additive. -/
instance instAdditiveShiftFunctorProd (n : ℤ) : (shiftFunctor (C × D) n).Additive :=
  inferInstanceAs ((shiftFunctor C n).prod (shiftFunctor D n)).Additive

variable [Pretriangulated C] [Pretriangulated D]

/-- The product of two pretriangulated categories is pretriangulated: a triangle is
distinguished exactly when both of its projections are distinguished. -/
noncomputable instance instPretriangulatedProd : Pretriangulated (C × D) where
  distinguishedTriangles :=
    {T | (CategoryTheory.Prod.fst C D).mapTriangle.obj T ∈ distTriang C ∧
      (CategoryTheory.Prod.snd C D).mapTriangle.obj T ∈ distTriang D}
  isomorphic_distinguished T₁ hT₁ T₂ e :=
    ⟨isomorphic_distinguished _ hT₁.1 _ ((CategoryTheory.Prod.fst C D).mapTriangle.mapIso e),
      isomorphic_distinguished _ hT₁.2 _ ((CategoryTheory.Prod.snd C D).mapTriangle.mapIso e)⟩
  contractible_distinguished X := by
    constructor
    · refine (Triangle.distinguished_iff_of_isZero₃ _
        ((CategoryTheory.Prod.fst C D).map_isZero (isZero_zero _))).2 ?_
      exact inferInstanceAs (IsIso (𝟙 _))
    · refine (Triangle.distinguished_iff_of_isZero₃ _
        ((CategoryTheory.Prod.snd C D).map_isZero (isZero_zero _))).2 ?_
      exact inferInstanceAs (IsIso (𝟙 _))
  distinguished_cocone_triangle f := by
    obtain ⟨Z₁, g₁, h₁, hT₁⟩ := distinguished_cocone_triangle f.1
    obtain ⟨Z₂, g₂, h₂, hT₂⟩ := distinguished_cocone_triangle f.2
    refine ⟨(Z₁, Z₂), (g₁, g₂), (h₁, h₂), ?_, ?_⟩
    · exact isomorphic_distinguished _ hT₁ _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))
    · exact isomorphic_distinguished _ hT₂ _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))
  rotate_distinguished_triangle T :=
    and_congr
      ((rotate_distinguished_triangle _).trans
        (distinguished_iff_of_iso ((CategoryTheory.Prod.fst C D).mapTriangleRotateIso.app T)))
      ((rotate_distinguished_triangle _).trans
        (distinguished_iff_of_iso ((CategoryTheory.Prod.snd C D).mapTriangleRotateIso.app T)))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c₁, hc₁, hc₁'⟩ := complete_distinguished_triangle_morphism _ _ hT₁.1 hT₂.1 a.1 b.1
      (congrArg Prod.fst comm)
    obtain ⟨c₂, hc₂, hc₂'⟩ := complete_distinguished_triangle_morphism _ _ hT₁.2 hT₂.2 a.2 b.2
      (congrArg Prod.snd comm)
    refine ⟨(c₁, c₂), Prod.hom_ext hc₁ hc₂, Prod.hom_ext ?_ ?_⟩
    · simpa using hc₁'
    · simpa using hc₂'

variable {C D}

/-- A triangle in a product of pretriangulated categories is distinguished exactly when both of
its projections are distinguished. -/
lemma mem_distTriang_prod_iff (T : Triangle (C × D)) :
    T ∈ distTriang (C × D) ↔ (CategoryTheory.Prod.fst C D).mapTriangle.obj T ∈ distTriang C ∧
      (CategoryTheory.Prod.snd C D).mapTriangle.obj T ∈ distTriang D :=
  Iff.rfl

variable (C D)

/-- The first projection of a product of pretriangulated categories is triangulated. -/
instance instIsTriangulatedProdFst : (CategoryTheory.Prod.fst C D).IsTriangulated where
  map_distinguished _ hT := hT.1

/-- The second projection of a product of pretriangulated categories is triangulated. -/
instance instIsTriangulatedProdSnd : (CategoryTheory.Prod.snd C D).IsTriangulated where
  map_distinguished _ hT := hT.2

/-- Inserting a zero object in the second coordinate is a triangulated functor. -/
instance instIsTriangulatedProdSectL : (CategoryTheory.Prod.sectL C (0 : D)).IsTriangulated where
  map_distinguished T hT := by
    constructor
    · refine isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ?_)
      exact (by simp : ((T.mor₃ ≫ 𝟙 _) ≫ 𝟙 _) ≫ (𝟙 T.obj₁)⟦(1 : ℤ)⟧' = 𝟙 T.obj₃ ≫ T.mor₃)
    · refine (Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero D)).2 ?_
      exact inferInstanceAs (IsIso (𝟙 _))

/-- Inserting a zero object in the first coordinate is a triangulated functor. -/
instance instIsTriangulatedProdSectR : (CategoryTheory.Prod.sectR (0 : C) D).IsTriangulated where
  map_distinguished T hT := by
    constructor
    · refine (Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero C)).2 ?_
      exact inferInstanceAs (IsIso (𝟙 _))
    · refine isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ?_)
      exact (by simp : ((T.mor₃ ≫ 𝟙 _) ≫ 𝟙 _) ≫ (𝟙 T.obj₁)⟦(1 : ℤ)⟧' = 𝟙 T.obj₃ ≫ T.mor₃)

section Functor

variable {C D} {C' : Type*} [Category* C'] [Preadditive C'] [HasZeroObject C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C']
  {D' : Type*} [Category* D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  (F : C ⥤ C') (G : D ⥤ D') [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]

/-- The product of two triangulated functors is triangulated. -/
instance instIsTriangulatedFunctorProd : (F.prod G).IsTriangulated where
  map_distinguished T hT := by
    constructor
    · refine isomorphic_distinguished _ (F.map_distinguished _ hT.1) _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ?_)
      exact (by simp : ((F.map T.mor₃.1 ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁.1) ≫ 𝟙 _) ≫
        (𝟙 (F.obj T.obj₁.1))⟦(1 : ℤ)⟧' =
          𝟙 _ ≫ F.map (T.mor₃.1 ≫ 𝟙 _) ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁.1)
    · refine isomorphic_distinguished _ (G.map_distinguished _ hT.2) _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ?_)
      exact (by simp : ((G.map T.mor₃.2 ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁.2) ≫ 𝟙 _) ≫
        (𝟙 (G.obj T.obj₁.2))⟦(1 : ℤ)⟧' =
          𝟙 _ ≫ G.map (T.mor₃.2 ≫ 𝟙 _) ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁.2)

end Functor

end TauCeti
