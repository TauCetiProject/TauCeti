/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import TauCeti.CategoryTheory.Triangulated.TriangleIso

/-!
# Direct summands and sums of triangles in a pretriangulated category

Facts about binary biproducts in a pretriangulated category `C`.

* A retract is a direct summand: if `X` is a retract of `Y`, then `Y ≅ X ⊞ Z` for some `Z`.
  The pretriangulated category need not be idempotent complete; the complement `Z` is the cone of
  the split monomorphism `X ⟶ Y`, whose distinguished triangle has zero connecting morphism.
  Consequently, for an isomorphism-closed property `P`, an object `X` satisfies
  `P.retractClosure` exactly when `X ⊞ Y` satisfies `P` for some `Y`. If `P` is dense, that is
  `P.retractClosure = ⊤`, every object has such a complement `Y`.
* Distinguished triangles are closed under binary direct sums, up to isomorphism of vertices: for
  distinguished `T₁` and `T₂` there is a distinguished triangle whose vertices are the biproducts
  of the corresponding vertices of `T₁` and `T₂`. It is the product triangle of the pair.
* A distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` whose second morphism is invertible on one
  summand identifies `K` with the other summand: it is isomorphic to a split triangle. The same
  holds after applying a triangulated functor. This is how a glued object is identified with its
  pieces.

The first two are used to manipulate objects up to direct summands in a dense triangulated
subcategory, where every object is a summand of an object of the subcategory.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_biprod_of_mono`: every monomorphism in a
  pretriangulated category splits as a binary biproduct summand.
* `CategoryTheory.Retract.exists_iso_biprod`: a retract of `Y` is a biproduct summand of `Y`.
* `CategoryTheory.ObjectProperty.prop_retractClosure_iff_exists_biprod`: the retract closure of
  an isomorphism-closed property consists of the summands of its objects.
* `CategoryTheory.ObjectProperty.exists_prop_biprod_of_retractClosure_eq_top`: for a dense
  isomorphism-closed property, every object has a complement whose biproduct with it lies in the
  property.
* `CategoryTheory.Pretriangulated.exists_distTriang_iso_biprod`: there is a distinguished triangle
  whose vertices are isomorphic to the vertexwise biproducts of two distinguished triangles.
* `CategoryTheory.Pretriangulated.isIso_comp_biprod_fst`: in a distinguished triangle
  `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` whose second morphism is invertible on `X₂`, the projection
  `K ⟶ X₁` is an isomorphism; `CategoryTheory.Pretriangulated.isIso_comp_biprod_snd` is the
  symmetric statement.
* `CategoryTheory.Functor.map_distTriang_biprod`: the image under a triangulated functor of a
  distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧`, with middle vertex rewritten to
  `F X₁ ⊞ F X₂` through `F.mapBiprod`, is distinguished.
* `CategoryTheory.Functor.isIso_map_comp_biprod_fst` and
  `CategoryTheory.Functor.isIso_map_comp_biprod_snd`: the same after applying a triangulated
  functor, when only the image of the second morphism is invertible on a summand.
-/

public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Splitting of monomorphisms in a pretriangulated category**: every monomorphism `f : X ⟶ Y`
identifies `Y` with a binary biproduct `X ⊞ Z` compatibly with `biprod.inl`. -/
theorem Pretriangulated.exists_iso_biprod_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), f ≫ e.hom = biprod.inl := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT
    (Triangle.mor₃_eq_zero_of_mono₁ _ hT ‹_›)
  exact ⟨Z, e, he⟩

/-- **A retract is a direct summand** in a pretriangulated category: if `X` is a retract of `Y`,
then `Y` is isomorphic to `X ⊞ Z` for some object `Z`. -/
theorem Retract.exists_iso_biprod {X Y : C} (h : Retract X Y) :
    ∃ Z : C, Nonempty (Y ≅ X ⊞ Z) := by
  obtain ⟨Z, e, -⟩ := Pretriangulated.exists_iso_biprod_of_mono h.i
  exact ⟨Z, ⟨e⟩⟩

/-- In a pretriangulated category, an object lies in the retract closure of an
isomorphism-closed property `P` exactly when it becomes an object satisfying `P` after adding a
direct summand. -/
theorem ObjectProperty.prop_retractClosure_iff_exists_biprod (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (X : C) : P.retractClosure X ↔ ∃ Y : C, P (X ⊞ Y) := by
  refine ⟨fun ⟨Y, hY, ⟨r⟩⟩ => ?_, fun ⟨Y, hY⟩ => P.prop_retractClosure hY
    { i := biprod.inl, r := biprod.fst }⟩
  obtain ⟨Z, ⟨e⟩⟩ := r.exists_iso_biprod
  exact ⟨Z, P.prop_of_iso e hY⟩

/-- In a pretriangulated category, every object has a complement for a dense isomorphism-closed
property `P`: a summand whose biproduct with the object satisfies `P`. -/
theorem ObjectProperty.exists_prop_biprod_of_retractClosure_eq_top (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (hP : P.retractClosure = ⊤) (X : C) : ∃ Y : C, P (X ⊞ Y) :=
  (P.prop_retractClosure_iff_exists_biprod X).1 (by rw [hP]; trivial)

namespace Pretriangulated

/-- **Direct sums of distinguished triangles**: for distinguished triangles `T₁` and `T₂` there is
a distinguished triangle whose three vertices are isomorphic to `T₁.obj₁ ⊞ T₂.obj₁`,
`T₁.obj₂ ⊞ T₂.obj₂` and `T₁.obj₃ ⊞ T₂.obj₃`. -/
theorem exists_distTriang_iso_biprod (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C) :
    ∃ T ∈ distTriang C, Nonempty (T.obj₁ ≅ T₁.obj₁ ⊞ T₂.obj₁) ∧
      Nonempty (T.obj₂ ≅ T₁.obj₂ ⊞ T₂.obj₂) ∧ Nonempty (T.obj₃ ≅ T₁.obj₃ ⊞ T₂.obj₃) := by
  -- A product over `WalkingPair` is the binary biproduct of its two factors.
  let e (F : WalkingPair → C) : ∏ᶜ F ≅ F .left ⊞ F .right :=
    HasLimit.isoOfNatIso (diagramIsoPair (Discrete.functor F)) ≪≫ (biprod.isoProd _ _).symm
  refine ⟨productTriangle (pairFunction T₁ T₂), productTriangle_distinguished _ ?_,
    ⟨e _⟩, ⟨e _⟩, ⟨e _⟩⟩
  rintro (_ | _)
  exacts [h₁, h₂]

/-- **A distinguished triangle with an invertible summand of its second morphism**: in a
distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` whose second morphism is invertible on the
summand `X₂`, the first morphism followed by the projection to `X₁` is an isomorphism
`K ≅ X₁`. The triangle is isomorphic to the split triangle `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
theorem isIso_comp_biprod_fst {K X₁ X₂ Y : C} {k : K ⟶ X₁ ⊞ X₂} {Φ : X₁ ⊞ X₂ ⟶ Y}
    {δ : Y ⟶ K⟦(1 : ℤ)⟧} (hT : Triangle.mk k Φ δ ∈ distTriang C) [IsIso (biprod.inr ≫ Φ)] :
    IsIso (k ≫ biprod.fst) := by
  -- The automorphism `b` of `X₁ ⊞ X₂` turns `Φ` into the projection to `X₂`, up to `inr ≫ Φ`.
  let b : X₁ ⊞ X₂ ⟶ X₁ ⊞ X₂ :=
    biprod.lift biprod.fst (biprod.snd - biprod.fst ≫ biprod.inl ≫ Φ ≫ inv (biprod.inr ≫ Φ))
  have hb : IsIso b := ⟨biprod.lift biprod.fst
    (biprod.snd + biprod.fst ≫ biprod.inl ≫ Φ ≫ inv (biprod.inr ≫ Φ)), by ext <;> simp [b],
    by ext <;> simp [b]⟩
  have hΦ : b ≫ Φ = biprod.snd ≫ biprod.inr ≫ Φ := by
    have : Φ = biprod.fst ≫ biprod.inl ≫ Φ + biprod.snd ≫ biprod.inr ≫ Φ := by
      simp only [← Category.assoc, ← Preadditive.add_comp, biprod.total, Category.id_comp]
    conv_lhs => rw [this]
    simp [b, Preadditive.comp_add, Preadditive.sub_comp]
  have hT₁ : Triangle.mk biprod.inl (biprod.snd ≫ biprod.inr ≫ Φ) 0 ∈ distTriang C :=
    isomorphic_distinguished _ (binaryBiproductTriangle_distinguished X₁ X₂) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (biprod.inr ≫ Φ)).symm (by simp)
        (by simp [binaryBiproductTriangle]) (by simp [binaryBiproductTriangle]))
  have hcomm : (biprod.snd ≫ biprod.inr ≫ Φ) ≫ 𝟙 Y = b ≫ Φ := by simpa using hΦ.symm
  obtain ⟨a, ha, ha'⟩ := complete_distinguished_triangle_morphism₁ _ _ hT₁ hT b (𝟙 Y) hcomm
  have : IsIso a := isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a b (𝟙 Y) ha hcomm ha') hT₁ hT hb
    (inferInstanceAs (IsIso (𝟙 Y)))
  have hfst : k ≫ biprod.fst = inv a := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    dsimp at ha
    rw [← Category.assoc, ← ha]
    simp [b]
  rw [hfst]
  infer_instance

/-- **A distinguished triangle with an invertible summand of its second morphism**: in a
distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` whose second morphism is invertible on the
summand `X₁`, the first morphism followed by the projection to `X₂` is an isomorphism
`K ≅ X₂`. -/
theorem isIso_comp_biprod_snd {K X₁ X₂ Y : C} {k : K ⟶ X₁ ⊞ X₂} {Φ : X₁ ⊞ X₂ ⟶ Y}
    {δ : Y ⟶ K⟦(1 : ℤ)⟧} (hT : Triangle.mk k Φ δ ∈ distTriang C) [IsIso (biprod.inl ≫ Φ)] :
    IsIso (k ≫ biprod.snd) := by
  have hT' : Triangle.mk (k ≫ (biprod.braiding X₁ X₂).hom) ((biprod.braiding X₁ X₂).inv ≫ Φ) δ ∈
      distTriang C :=
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _)
      (biprod.braiding X₁ X₂).symm (Iso.refl _) (by simp) (by simp) (by simp))
  have : IsIso (biprod.inr ≫ (biprod.braiding X₁ X₂).inv ≫ Φ) := by
    rw [← Category.assoc,
      show biprod.inr ≫ (biprod.braiding X₁ X₂).inv = biprod.inl by ext <;> simp]
    infer_instance
  simpa using isIso_comp_biprod_fst hT'

end Pretriangulated

section Functor

-- An additive functor, such as a triangulated functor, preserves binary biproducts.
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ]
  [F.IsTriangulated] {K X₁ X₂ Y : C} {k : K ⟶ X₁ ⊞ X₂} {Φ : X₁ ⊞ X₂ ⟶ Y} {δ : Y ⟶ K⟦(1 : ℤ)⟧}

/-- The image of a distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` under a triangulated functor
`F`, with middle vertex `F X₁ ⊞ F X₂`, is distinguished. -/
theorem Functor.map_distTriang_biprod (hT : Triangle.mk k Φ δ ∈ distTriang C) :
    Triangle.mk (F.map k ≫ (F.mapBiprod X₁ X₂).hom) ((F.mapBiprod X₁ X₂).inv ≫ F.map Φ)
      (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang D := by
  simpa using distinguished_mk_of_iso (F.map_distinguished _ hT) (Iso.refl _) (F.mapBiprod _ _)
    (Iso.refl _)

/-- **A triangulated functor and an invertible summand of the second morphism**: for a
triangulated functor `F` and a distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` whose second
morphism becomes invertible on the summand `X₂` after applying `F`, the image under `F` of the
first morphism followed by the projection to `X₁` is an isomorphism `F K ≅ F X₁`. -/
theorem Functor.isIso_map_comp_biprod_fst (hT : Triangle.mk k Φ δ ∈ distTriang C)
    [IsIso (F.map (biprod.inr ≫ Φ))] : IsIso (F.map (k ≫ biprod.fst)) := by
  have : IsIso (biprod.inr ≫ (F.mapBiprod X₁ X₂).inv ≫ F.map Φ) := by
    rwa [mapBiprod_inv, biprod.inr_desc_assoc, ← F.map_comp]
  simpa only [Category.assoc, mapBiprod_hom, biprod.lift_fst, ← F.map_comp] using
    isIso_comp_biprod_fst (F.map_distTriang_biprod hT)

/-- **A triangulated functor and an invertible summand of the second morphism**: for a
triangulated functor `F` and a distinguished triangle `K ⟶ X₁ ⊞ X₂ ⟶ Y ⟶ K⟦1⟧` whose second
morphism becomes invertible on the summand `X₁` after applying `F`, the image under `F` of the
first morphism followed by the projection to `X₂` is an isomorphism `F K ≅ F X₂`. -/
theorem Functor.isIso_map_comp_biprod_snd (hT : Triangle.mk k Φ δ ∈ distTriang C)
    [IsIso (F.map (biprod.inl ≫ Φ))] : IsIso (F.map (k ≫ biprod.snd)) := by
  have : IsIso (biprod.inl ≫ (F.mapBiprod X₁ X₂).inv ≫ F.map Φ) := by
    rwa [mapBiprod_inv, biprod.inl_desc_assoc, ← F.map_comp]
  simpa only [Category.assoc, mapBiprod_hom, biprod.lift_snd, ← F.map_comp] using
    isIso_comp_biprod_snd (F.map_distTriang_biprod hT)

end Functor

end CategoryTheory
