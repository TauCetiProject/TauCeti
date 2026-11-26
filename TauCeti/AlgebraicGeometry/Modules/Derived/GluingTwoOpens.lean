/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Derived.OpenImmersion
public import TauCeti.CategoryTheory.Triangulated.Biproduct
public import TauCeti.CategoryTheory.Triangulated.TriangleIso

/-!
# Gluing objects of derived categories of module sheaves along two opens

Let `U` and `V` be opens of a scheme `X`, `A ∈ D(𝒪_U)`, `B ∈ D(𝒪_V)`, and
`φ : A|_{U∩V} ≅ B|_{U∩V}`. Completing the map
`TauCeti.AlgebraicGeometry.Coherent.gluingTwoOpensMap A B φ :
  Rj_{U*} A ⊕ Rj_{V*} B ⟶ Rj_{U∩V*} (B|_{U∩V})`,
the restriction map followed by `Rj_{U∩V*} φ` on the first summand and minus the restriction map
on the second, to a distinguished triangle `K ⟶ Rj_{U*} A ⊕ Rj_{V*} B ⟶ Rj_{U∩V*} (B|_{U∩V}) ⟶ K[1]`
gives an object `K ∈ D(𝒪_X)` with isomorphisms `K|_U ≅ A` and `K|_V ≅ B` compatible with `φ`
(`TauCeti.AlgebraicGeometry.Coherent.exists_derivedGluing_two_opens`).

Restricted to `U`, the second summand of the map becomes invertible, so the triangle identifies
`K|_U` with `(Rj_{U*} A)|_U ≅ A` (`CategoryTheory.Pretriangulated.isIso_comp_biprod_fst`); the
same holds on `V`. Compatibility with `φ` on `U ∩ V` follows from the vanishing of the composite of
the first two morphisms of the triangle and the compatibility of restriction maps with the derived
counits (`AlgebraicGeometry.Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app`).

## References

* [Stacks: Lemma 20.45.1](https://stacks.math.columbia.edu/tag/08DG), used in the proof of
  Lemma 36.15.1 of [Stacks: Section 36.15](https://stacks.math.columbia.edu/tag/09IP).
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory Functor Pretriangulated

universe w₁ w₂ w₃ w₄ u

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (U V : X.Opens) [HasDerivedCategory.{w₁} X.Modules]
  [HasDerivedCategory.{w₂} U.toScheme.Modules] [HasDerivedCategory.{w₃} V.toScheme.Modules]
  [HasDerivedCategory.{w₄} (U ⊓ V).toScheme.Modules]

/-- The map `Rj_{U*} A ⊕ Rj_{V*} B ⟶ Rj_{U∩V*} (B|_{U∩V})` whose fibre glues `A ∈ D(𝒪_U)` and
`B ∈ D(𝒪_V)` along an isomorphism `φ : A|_{U∩V} ≅ B|_{U∩V}`: on `Rj_{U*} A` it is the restriction
map to `U ∩ V` followed by `Rj_{U∩V*} φ`, and on `Rj_{V*} B` it is minus the restriction map. -/
def gluingTwoOpensMap (A : DerivedCategory U.toScheme.Modules)
    (B : DerivedCategory V.toScheme.Modules)
    (φ : (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.obj A ≅
      (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) :
    U.ι.totalDirectImage.obj A ⊞ V.ι.totalDirectImage.obj B ⟶
      (U ⊓ V).ι.totalDirectImage.obj
        ((X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) :=
  biprod.desc
    (((X.homOfLE inf_le_left).totalDirectImageRestrict U.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_left)).app A ≫ (U ⊓ V).ι.totalDirectImage.map φ.hom)
    (-((X.homOfLE inf_le_right).totalDirectImageRestrict V.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_right)).app B)

omit [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} U.toScheme.Modules]
  [HasDerivedCategory.{w₃} V.toScheme.Modules] [HasDerivedCategory.{w₄} (U ⊓ V).toScheme.Modules]
  in
private lemma isIso_neg {C : Type*} [Category* C] [Preadditive C] {P Q : C} (f : P ⟶ Q)
    [IsIso f] : IsIso (-f) :=
  ⟨-inv f, by simp, by simp⟩

variable {U V} {A : DerivedCategory U.toScheme.Modules} {B : DerivedCategory V.toScheme.Modules}
  {φ : (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.obj A ≅
    (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B}
  {K : DerivedCategory X.Modules} {k : K ⟶ U.ι.totalDirectImage.obj A ⊞ V.ι.totalDirectImage.obj B}

/-- Restricted to `U`, the map `gluingTwoOpensMap` is invertible on the summand `Rj_{V*} B`, so a
distinguished triangle on it identifies `K|_U` with `(Rj_{U*} A)|_U`. -/
private lemma isIso_derivedRestrict_map_comp_biprod_fst
    {δ : (U ⊓ V).ι.totalDirectImage.obj
      ((X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) ⟶
        K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk k (gluingTwoOpensMap U V A B φ) δ ∈ distTriang _) :
    IsIso (U.ι.derivedRestrict.map (k ≫ biprod.fst)) := by
  have : PreservesBinaryBiproducts U.ι.derivedRestrict :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have hTU := distinguished_mk_of_iso (U.ι.derivedRestrict.map_distinguished _ hT) (Iso.refl _)
    (U.ι.derivedRestrict.mapBiprod _ _) (Iso.refl _)
  simp only [mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
    Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] at hTU
  have : IsIso (biprod.inr ≫ (U.ι.derivedRestrict.mapBiprod _ _).inv ≫
      U.ι.derivedRestrict.map (gluingTwoOpensMap U V A B φ)) := by
    simp only [mapBiprod_inv, biprod.inr_desc_assoc, ← Functor.map_comp, gluingTwoOpensMap,
      biprod.inr_desc, Functor.map_neg]
    have := isIso_derivedRestrict_map_totalDirectImageRestrict_app (U := U)
      (inf_le_right : U ⊓ V ≤ V) le_rfl B
    exact isIso_neg _
  simpa [mapBiprod_hom] using isIso_comp_biprod_fst hTU

/-- Restricted to `V`, the map `gluingTwoOpensMap` is invertible on the summand `Rj_{U*} A`, so a
distinguished triangle on it identifies `K|_V` with `(Rj_{V*} B)|_V`. -/
private lemma isIso_derivedRestrict_map_comp_biprod_snd
    {δ : (U ⊓ V).ι.totalDirectImage.obj
      ((X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) ⟶
        K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk k (gluingTwoOpensMap U V A B φ) δ ∈ distTriang _) :
    IsIso (V.ι.derivedRestrict.map (k ≫ biprod.snd)) := by
  have : PreservesBinaryBiproducts V.ι.derivedRestrict :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have hTV := distinguished_mk_of_iso (V.ι.derivedRestrict.map_distinguished _ hT) (Iso.refl _)
    (V.ι.derivedRestrict.mapBiprod _ _) (Iso.refl _)
  simp only [mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
    Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] at hTV
  have : IsIso (biprod.inl ≫ (V.ι.derivedRestrict.mapBiprod _ _).inv ≫
      V.ι.derivedRestrict.map (gluingTwoOpensMap U V A B φ)) := by
    simp only [mapBiprod_inv, biprod.inl_desc_assoc, ← Functor.map_comp, gluingTwoOpensMap,
      biprod.inl_desc]
    have := isIso_derivedRestrict_map_totalDirectImageRestrict_app (U := V)
      (inf_le_left : U ⊓ V ≤ U) (le_of_eq (inf_comm V U)) A
    rw [Functor.map_comp]
    infer_instance
  simpa [mapBiprod_hom] using isIso_comp_biprod_snd hTV

/-- If `k ≫ gluingTwoOpensMap = 0`, the morphisms `K|_U ⟶ A` and `K|_V ⟶ B` induced by `k` and the
derived counits are compatible with `φ` on `U ∩ V`. -/
private lemma derivedRestrict_map_comp_hom_eq (hk : k ≫ gluingTwoOpensMap U V A B φ = 0) :
    (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.map
        (U.ι.derivedRestrict.map (k ≫ biprod.fst) ≫
          (U.ι.totalDirectImageCompDerivedRestrictIso).hom.app A) ≫ φ.hom =
      ((X.homOfLE inf_le_left).derivedRestrictComp U.ι (U ⊓ V).ι
          (X.homOfLE_ι inf_le_left)).hom.app K ≫
        ((X.homOfLE inf_le_right).derivedRestrictComp V.ι (U ⊓ V).ι
          (X.homOfLE_ι inf_le_right)).inv.app K ≫
          (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.map
            (V.ι.derivedRestrict.map (k ≫ biprod.snd) ≫
              (V.ι.totalDirectImageCompDerivedRestrictIso).hom.app B) := by
  have h₀ : k ≫ biprod.fst ≫ ((X.homOfLE inf_le_left).totalDirectImageRestrict U.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_left)).app A ≫ (U ⊓ V).ι.totalDirectImage.map φ.hom =
      k ≫ biprod.snd ≫ ((X.homOfLE inf_le_right).totalDirectImageRestrict V.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_right)).app B := by
    rw [gluingTwoOpensMap, biprod.desc_eq, Preadditive.comp_add, add_eq_zero_iff_eq_neg] at hk
    simpa using hk
  have cA := Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app (X.homOfLE inf_le_left)
    U.ι (U ⊓ V).ι (X.homOfLE_ι inf_le_left) A
  have cB := Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app (X.homOfLE inf_le_right)
    V.ι (U ⊓ V).ι (X.homOfLE_ι inf_le_right) B
  have cU := ((X.homOfLE inf_le_left).derivedRestrictComp U.ι (U ⊓ V).ι
    (X.homOfLE_ι inf_le_left)).hom.naturality (k ≫ biprod.fst)
  have cV := ((X.homOfLE inf_le_right).derivedRestrictComp V.ι (U ⊓ V).ι
    (X.homOfLE_ι inf_le_right)).inv.naturality (k ≫ biprod.snd)
  have εφ := ((U ⊓ V).ι.totalDirectImageCompDerivedRestrictIso).hom.naturality φ.hom
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at cU cV εφ
  rw [(X.homOfLE inf_le_left).derivedRestrict.map_comp,
    (X.homOfLE inf_le_right).derivedRestrict.map_comp, Category.assoc]
  have e : (X.homOfLE inf_le_left).derivedRestrict.map
      (U.ι.derivedRestrict.map (k ≫ biprod.fst)) =
      ((X.homOfLE inf_le_left).derivedRestrictComp U.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_left)).hom.app K ≫ (U ⊓ V).ι.derivedRestrict.map (k ≫ biprod.fst) ≫
        ((X.homOfLE inf_le_left).derivedRestrictComp U.ι (U ⊓ V).ι
          (X.homOfLE_ι inf_le_left)).inv.app _ := by
    rw [← reassoc_of% cU]
    simp
  rw [e]
  simp only [Category.assoc]
  rw [← reassoc_of% cA, ← εφ, ← reassoc_of% cV, ← cB]
  simp only [← Functor.map_comp_assoc, Category.assoc]
  rw [h₀]


variable (U V) in
/-- **Gluing of objects of `D(𝒪_X)` along two opens** ([Stacks, Lemma 20.45.1]): for opens `U` and
`V` of a scheme `X`, objects `A ∈ D(𝒪_U)` and `B ∈ D(𝒪_V)` and an isomorphism
`φ : A|_{U∩V} ≅ B|_{U∩V}`, there are `K ∈ D(𝒪_X)` and isomorphisms `α : K|_U ≅ A` and
`β : K|_V ≅ B` that are compatible with `φ` on `U ∩ V`, together with a distinguished triangle
`K ⟶ Rj_{U*} A ⊕ Rj_{V*} B ⟶ Rj_{U∩V*} (B|_{U∩V}) ⟶ K[1]` whose second morphism is
`TauCeti.AlgebraicGeometry.Coherent.gluingTwoOpensMap`. The isomorphisms `α` and `β` are induced
by the first morphism of the triangle and the derived counits
`Scheme.Hom.totalDirectImageCompDerivedRestrictIso`. When `U ⊔ V = ⊤`, `K` glues `A` and `B`;
in general it is supported on `U ∪ V`. -/
theorem exists_derivedGluing_two_opens (A : DerivedCategory U.toScheme.Modules)
    (B : DerivedCategory V.toScheme.Modules)
    (φ : (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.obj A ≅
      (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) :
    ∃ (K : DerivedCategory X.Modules)
      (k : K ⟶ U.ι.totalDirectImage.obj A ⊞ V.ι.totalDirectImage.obj B)
      (δ : (U ⊓ V).ι.totalDirectImage.obj
        ((X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) ⟶
          K⟦(1 : ℤ)⟧)
      (α : U.ι.derivedRestrict.obj K ≅ A) (β : V.ι.derivedRestrict.obj K ≅ B),
      Triangle.mk k (gluingTwoOpensMap U V A B φ) δ ∈ distTriang _ ∧
      α.hom = U.ι.derivedRestrict.map (k ≫ biprod.fst) ≫
        (U.ι.totalDirectImageCompDerivedRestrictIso).hom.app A ∧
      β.hom = V.ι.derivedRestrict.map (k ≫ biprod.snd) ≫
        (V.ι.totalDirectImageCompDerivedRestrictIso).hom.app B ∧
      (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.map α.hom ≫
          φ.hom =
        ((X.homOfLE inf_le_left).derivedRestrictComp U.ι (U ⊓ V).ι
            (X.homOfLE_ι inf_le_left)).hom.app K ≫
          ((X.homOfLE inf_le_right).derivedRestrictComp V.ι (U ⊓ V).ι
            (X.homOfLE_ι inf_le_right)).inv.app K ≫
            (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.map
              β.hom := by
  obtain ⟨K, k, δ, hT⟩ := distinguished_cocone_triangle₁ (gluingTwoOpensMap U V A B φ)
  have := isIso_derivedRestrict_map_comp_biprod_fst hT
  have := isIso_derivedRestrict_map_comp_biprod_snd hT
  exact ⟨K, k, δ, asIso (U.ι.derivedRestrict.map (k ≫ biprod.fst)) ≪≫
    (U.ι.totalDirectImageCompDerivedRestrictIso).app A,
    asIso (V.ι.derivedRestrict.map (k ≫ biprod.snd)) ≪≫
    (V.ι.totalDirectImageCompDerivedRestrictIso).app B, hT, rfl, rfl,
    derivedRestrict_map_comp_hom_eq (comp_distTriang_mor_zero₁₂ _ hT)⟩

end TauCeti.AlgebraicGeometry.Coherent
