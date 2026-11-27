/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Derived.OpenImmersion
public import TauCeti.CategoryTheory.Triangulated.Biproduct
import TauCeti.CategoryTheory.Preadditive.IsIso

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

The map is described on the two summands by
`TauCeti.AlgebraicGeometry.Coherent.inl_gluingTwoOpensMap` and
`TauCeti.AlgebraicGeometry.Coherent.inr_gluingTwoOpensMap`. Restricted to `U`, its second summand
becomes invertible, so the triangle identifies `K|_U` with `(Rj_{U*} A)|_U ≅ A`
(`CategoryTheory.Functor.isIso_map_comp_biprod_fst`); the same holds on `V`. Compatibility with
`φ` on `U ∩ V` follows from the vanishing of the composite of the first two morphisms of the
triangle and the compatibility of restriction maps with the derived counits
(`AlgebraicGeometry.Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app`).

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

/-- On the summand `Rj_{U*} A`, the map `gluingTwoOpensMap` is the restriction map to `U ∩ V`
followed by `Rj_{U∩V*} φ`. -/
@[reassoc (attr := simp)]
lemma inl_gluingTwoOpensMap (A : DerivedCategory U.toScheme.Modules)
    (B : DerivedCategory V.toScheme.Modules)
    (φ : (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.obj A ≅
      (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) :
    biprod.inl ≫ gluingTwoOpensMap U V A B φ =
      ((X.homOfLE inf_le_left).totalDirectImageRestrict U.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_left)).app A ≫ (U ⊓ V).ι.totalDirectImage.map φ.hom :=
  biprod.inl_desc _ _

/-- On the summand `Rj_{V*} B`, the map `gluingTwoOpensMap` is minus the restriction map to
`U ∩ V`. -/
@[reassoc (attr := simp)]
lemma inr_gluingTwoOpensMap (A : DerivedCategory U.toScheme.Modules)
    (B : DerivedCategory V.toScheme.Modules)
    (φ : (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.obj A ≅
      (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B) :
    biprod.inr ≫ gluingTwoOpensMap U V A B φ =
      -((X.homOfLE inf_le_right).totalDirectImageRestrict V.ι (U ⊓ V).ι
        (X.homOfLE_ι inf_le_right)).app B :=
  biprod.inr_desc _ _

variable {U V} {A : DerivedCategory U.toScheme.Modules} {B : DerivedCategory V.toScheme.Modules}
  {φ : (X.homOfLE inf_le_left : (U ⊓ V : X.Opens).toScheme ⟶ U).derivedRestrict.obj A ≅
    (X.homOfLE inf_le_right : (U ⊓ V : X.Opens).toScheme ⟶ V).derivedRestrict.obj B}
  {K : DerivedCategory X.Modules} {k : K ⟶ U.ι.totalDirectImage.obj A ⊞ V.ι.totalDirectImage.obj B}

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
    rw [← Category.id_comp (gluingTwoOpensMap U V A B φ), ← biprod.total] at hk
    simpa only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      inl_gluingTwoOpensMap, inr_gluingTwoOpensMap, Preadditive.comp_neg, add_neg_eq_zero] using hk
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
  rw [← Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app_assoc, ← εφ,
    ← reassoc_of% cV, ← Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app]
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
in general its restriction to `U ⊔ V` does. -/
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
  -- Restricted to `U`, `gluingTwoOpensMap` is invertible on the summand `Rj_{V*} B`, and
  -- restricted to `V` on the summand `Rj_{U*} A`, by base change of restriction maps.
  have := isIso_derivedRestrict_map_totalDirectImageRestrict_app (U := U)
    (inf_le_right : U ⊓ V ≤ V) le_rfl B
  have := isIso_derivedRestrict_map_totalDirectImageRestrict_app (U := V)
    (inf_le_left : U ⊓ V ≤ U) (le_of_eq (inf_comm V U)) A
  have : IsIso (U.ι.derivedRestrict.map (biprod.inr ≫ gluingTwoOpensMap U V A B φ)) := by
    rw [inr_gluingTwoOpensMap, Functor.map_neg]
    infer_instance
  have : IsIso (V.ι.derivedRestrict.map (biprod.inl ≫ gluingTwoOpensMap U V A B φ)) := by
    rw [inl_gluingTwoOpensMap, Functor.map_comp]
    infer_instance
  have := U.ι.derivedRestrict.isIso_map_comp_biprod_fst hT
  have := V.ι.derivedRestrict.isIso_map_comp_biprod_snd hT
  exact ⟨K, k, δ, asIso (U.ι.derivedRestrict.map (k ≫ biprod.fst)) ≪≫
    (U.ι.totalDirectImageCompDerivedRestrictIso).app A,
    asIso (V.ι.derivedRestrict.map (k ≫ biprod.snd)) ≪≫
    (V.ι.totalDirectImageCompDerivedRestrictIso).app B, hT, rfl, rfl,
    derivedRestrict_map_comp_hom_eq (comp_distTriang_mor_zero₁₂ _ hT)⟩

end TauCeti.AlgebraicGeometry.Coherent
