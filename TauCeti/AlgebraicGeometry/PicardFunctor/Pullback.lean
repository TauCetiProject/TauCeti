/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Fppf

/-!
# Pullback of relative Picard sheaves

A morphism of schemes over a fixed base induces pullback on the relative Picard presheaves and
their fppf sheafifications. The construction uses pullback of line bundles on every test scheme.
It preserves identities and reverses composition. A morphism factoring through a section of the
base induces zero on the additive presheaf and the fppf sheaf.

No properness, smoothness or representability hypothesis is required.

## Main declarations

* `relativePicardPresheafPullback`: pullback on the quotient `Pic(X_T) / Pic(T)`;
* `relativePicardFppfSheafPullback`: the induced morphism of additive fppf sheaves;
* `relativePicardFppfSheafPullback_app_mk`: its action on represented sections;
* `relativePicardFppfSheafPullback_eq_zero`: vanishing for maps through a base section.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {S : Scheme.{u}} {X Y Z : Over S}

/-- Horizontal pullback preserves the classes pulled back from the test scheme. -/
private lemma range_pullbackHom_fst_le_comap_pullbackMap (h : X ⟶ Y) (T : Over S) :
    (LineBundleClass.pullbackHom (pullback.fst T.hom Y.hom)).range ≤
      (LineBundleClass.pullbackHom (pullback.fst T.hom X.hom)).range.comap
        (LineBundleClass.pullbackHom
          (pullback.map _ _ _ _ (𝟙 T.left) h.left (𝟙 S) (by simp) (by simp))) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  simp only [LineBundleClass.pullbackHom_apply, LineBundleClass.pullback_comp,
    pullback.lift_fst, Category.comp_id]

/-- Line-bundle pullback descends to the relative Picard quotient. -/
private def relativePicardPullbackHom (h : X ⟶ Y) (T : Over S) :
    LineBundleClass (pullback T.hom Y.hom) ⧸
        (LineBundleClass.pullbackHom (pullback.fst T.hom Y.hom)).range →*
      LineBundleClass (pullback T.hom X.hom) ⧸
        (LineBundleClass.pullbackHom (pullback.fst T.hom X.hom)).range :=
  QuotientGroup.map _ _ (LineBundleClass.pullbackHom
    (pullback.map _ _ _ _ (𝟙 T.left) h.left (𝟙 S) (by simp) (by simp)))
    (range_pullbackHom_fst_le_comap_pullbackMap h T)

/-- The descended homomorphism sends a representative to its pulled-back class. -/
private lemma relativePicardPullbackHom_mk (h : X ⟶ Y) (T : Over S)
    (a : LineBundleClass (pullback T.hom Y.hom)) :
    relativePicardPullbackHom h T (QuotientGroup.mk a) =
      QuotientGroup.mk (LineBundleClass.pullback
        (pullback.map _ _ _ _ (𝟙 T.left) h.left (𝟙 S) (by simp) (by simp)) a) :=
  (QuotientGroup.map_mk _ _ _ _ a).trans
    (congrArg QuotientGroup.mk (LineBundleClass.pullbackHom_apply _ a))

/-- Horizontal relative Picard pullback commutes with restriction of the test scheme. -/
private lemma relativePicardPullbackHom_naturality (h : X ⟶ Y)
    {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') (a : LineBundleClass (pullback T.unop.hom Y.hom)) :
    relativePicardPullbackHom h T'.unop
        ((relativePicardPresheaf Y.hom).map φ (QuotientGroup.mk a)) =
      (relativePicardPresheaf X.hom).map φ
        (relativePicardPullbackHom h T.unop (QuotientGroup.mk a)) := by
  rw [relativePicardPresheaf_map_mk, relativePicardPullbackHom_mk,
    relativePicardPullbackHom_mk, relativePicardPresheaf_map_mk,
    LineBundleClass.pullback_comp, LineBundleClass.pullback_comp]
  congr 2
  apply pullback.hom_ext <;> simp [Over.pullback_map_left, Category.assoc]

/-- Pullback along a morphism over `S` on the relative Picard presheaves. -/
def relativePicardPresheafPullback (h : X ⟶ Y) :
    relativePicardPresheaf Y.hom ⟶ relativePicardPresheaf X.hom where
  app T := CommGrpCat.ofHom (relativePicardPullbackHom h T.unop)
  naturality T T' φ := by
    ext c
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
    exact relativePicardPullbackHom_naturality h φ a

/-- On a class represented by a line bundle, relative Picard pullback is its actual pullback
on the induced family. -/
@[simp]
lemma relativePicardPresheafPullback_app_mk (h : X ⟶ Y) (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom Y.hom)) :
    (relativePicardPresheafPullback h).app T (QuotientGroup.mk a) =
      QuotientGroup.mk (LineBundleClass.pullback (pullback.map _ _ _ _ (𝟙 T.unop.left)
        h.left (𝟙 S) (by simp) (by simp)) a) :=
  relativePicardPullbackHom_mk h T.unop a

/-- Pullback along the identity is the identity on the relative Picard presheaf. -/
@[simp]
lemma relativePicardPresheafPullback_id :
    relativePicardPresheafPullback (𝟙 X) = 𝟙 (relativePicardPresheaf X.hom) := by
  ext T c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  exact (relativePicardPullbackHom_mk (𝟙 X) T.unop a).trans <| by
    simp only [Over.id_left, pullback.map_id, LineBundleClass.pullback_id]
    rfl

/-- Relative Picard pullback reverses composition of morphisms of schemes. -/
lemma relativePicardPresheafPullback_comp (h : X ⟶ Y) (k : Y ⟶ Z) :
    relativePicardPresheafPullback (h ≫ k) =
      relativePicardPresheafPullback k ≫ relativePicardPresheafPullback h := by
  ext T c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  refine (relativePicardPullbackHom_mk (h ≫ k) T.unop a).trans ?_
  refine Eq.trans ?_ ((congrArg (relativePicardPullbackHom h T.unop)
    (relativePicardPullbackHom_mk k T.unop a)).trans
      (relativePicardPullbackHom_mk h T.unop _)).symm
  rw [LineBundleClass.pullback_comp]
  congr 2
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Pullback on the additive relative Picard presheaves. -/
def relativePicardAddPresheafPullback (h : X ⟶ Y) :
    relativePicardAddPresheaf Y.hom ⟶ relativePicardAddPresheaf X.hom :=
  eqToHom (relativePicardAddPresheaf_eq Y.hom) ≫
    Functor.whiskerRight (relativePicardPresheafPullback h) CommGrpCat.toAddCommGrp ≫
      eqToHom (relativePicardAddPresheaf_eq X.hom).symm

/-- Additive Picard pullback sends a represented section to the class of the pulled-back
line bundle. -/
@[simp]
lemma relativePicardAddPresheafPullback_app_mk (h : X ⟶ Y) (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom Y.hom)) :
    (relativePicardAddPresheafPullback h).app T (relativePicardAddPresheafMk Y.hom T a) =
      relativePicardAddPresheafMk X.hom T
        (LineBundleClass.pullback (pullback.map _ _ _ _ (𝟙 T.unop.left)
          h.left (𝟙 S) (by simp) (by simp)) a) := by
  have hmap : eqToHom (relativePicardAddPresheaf_eq Y.hom).symm ≫
      relativePicardAddPresheafPullback h =
      Functor.whiskerRight (relativePicardPresheafPullback h) CommGrpCat.toAddCommGrp ≫
        eqToHom (relativePicardAddPresheaf_eq X.hom).symm := by
    simp [relativePicardAddPresheafPullback]
  have hcompat := congrArg (fun k ↦ k.app T
    (Additive.ofMul (QuotientGroup.mk a : (relativePicardPresheaf Y.hom).obj T))) hmap
  rw [relativePicardAddPresheafMk_eq, relativePicardAddPresheafMk_eq]
  exact hcompat.trans <|
    congrArg ((eqToHom (relativePicardAddPresheaf_eq X.hom).symm).app T)
      (congrArg Additive.ofMul (relativePicardPresheafPullback_app_mk h T a))

/-- The additive relative Picard pullback sends identities to identities. -/
@[simp]
lemma relativePicardAddPresheafPullback_id :
    relativePicardAddPresheafPullback (𝟙 X) = 𝟙 (relativePicardAddPresheaf X.hom) := by
  simp [relativePicardAddPresheafPullback]

/-- The additive relative Picard pullback reverses composition. -/
lemma relativePicardAddPresheafPullback_comp (h : X ⟶ Y) (k : Y ⟶ Z) :
    relativePicardAddPresheafPullback (h ≫ k) =
      relativePicardAddPresheafPullback k ≫ relativePicardAddPresheafPullback h := by
  simp [relativePicardAddPresheafPullback, relativePicardPresheafPullback_comp,
    Functor.whiskerRight_comp]

/-- A map factoring through a section of the base induces zero on the relative Picard
presheaf: every pulled-back bundle then comes from the test scheme. -/
lemma relativePicardAddPresheafPullback_eq_zero (h : X ⟶ Y)
    (s : Over.mk (𝟙 S) ⟶ Y) (hs : h.left = X.hom ≫ s.left) :
    relativePicardAddPresheafPullback h = 0 := by
  ext T c
  obtain ⟨a, rfl⟩ := relativePicardAddPresheafMk_surjective Y.hom T c
  rw [relativePicardAddPresheafPullback_app_mk]
  have hmap : pullback.map T.unop.hom X.hom T.unop.hom Y.hom
      (𝟙 T.unop.left) h.left (𝟙 S) (by simp) (by simp) =
      pullback.fst T.unop.hom X.hom ≫
      pullback.lift (𝟙 T.unop.left) (T.unop.hom ≫ s.left) (by simp) := by
    apply pullback.hom_ext <;> simp [hs, pullback.condition_assoc]
  have hclass : (QuotientGroup.mk (LineBundleClass.pullback
      (pullback.map T.unop.hom X.hom T.unop.hom Y.hom
        (𝟙 T.unop.left) h.left (𝟙 S) (by simp) (by simp)) a) :
      (relativePicardPresheaf X.hom).obj T) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨LineBundleClass.pullback
      (pullback.lift (𝟙 T.unop.left) (T.unop.hom ≫ s.left) (by simp)) a, ?_⟩
    simp only [LineBundleClass.pullbackHom_apply, LineBundleClass.pullback_comp, hmap]
  simp only [NatTrans.app_zero, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  rw [relativePicardAddPresheafMk_eq]
  exact (congrArg ((eqToHom (relativePicardAddPresheaf_eq X.hom).symm).app T)
    (congrArg Additive.ofMul hclass)).trans (map_zero _)

/-- Pullback of relative Picard fppf sheaves induced by a morphism over the fixed base. -/
def relativePicardFppfSheafPullback (h : X ⟶ Y) :
    relativePicardFppfSheaf Y.hom ⟶ relativePicardFppfSheaf X.hom :=
  (relativePicardFppfSheafHomEquiv Y.hom _).symm
    (relativePicardAddPresheafPullback h ≫ relativePicardToFppfSheaf X.hom)

/-- Picard sheaf pullback agrees with pullback of the classes defining its sections. -/
@[reassoc]
lemma relativePicardToFppfSheaf_comp_pullback (h : X ⟶ Y) :
    relativePicardToFppfSheaf Y.hom ≫ (relativePicardFppfSheafPullback h).hom =
      relativePicardAddPresheafPullback h ≫ relativePicardToFppfSheaf X.hom := by
  rw [← relativePicardFppfSheafHomEquiv_apply, relativePicardFppfSheafPullback,
    Equiv.apply_symm_apply]

/-- On a represented fppf section, Picard sheaf pullback is pullback of its line-bundle class. -/
@[simp]
lemma relativePicardFppfSheafPullback_app_mk (h : X ⟶ Y) (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom Y.hom)) :
    (relativePicardFppfSheafPullback h).hom.app T
        ((relativePicardToFppfSheaf Y.hom).app T (relativePicardAddPresheafMk Y.hom T a)) =
      (relativePicardToFppfSheaf X.hom).app T (relativePicardAddPresheafMk X.hom T
        (LineBundleClass.pullback (pullback.map _ _ _ _ (𝟙 T.unop.left)
          h.left (𝟙 S) (by simp) (by simp)) a)) := by
  simpa using congrArg (fun k ↦ k.app T (relativePicardAddPresheafMk Y.hom T a))
    (relativePicardToFppfSheaf_comp_pullback h)

/-- Pullback along the identity is the identity on the relative Picard fppf sheaf. -/
@[simp]
lemma relativePicardFppfSheafPullback_id :
    relativePicardFppfSheafPullback (𝟙 X) = 𝟙 (relativePicardFppfSheaf X.hom) := by
  apply (relativePicardFppfSheafHomEquiv X.hom _).injective
  simp only [relativePicardFppfSheafHomEquiv_apply,
    relativePicardToFppfSheaf_comp_pullback, relativePicardAddPresheafPullback_id,
    Category.id_comp, ObjectProperty.FullSubcategory.id_hom, Category.comp_id]

/-- Relative Picard fppf sheaf pullback reverses composition. -/
lemma relativePicardFppfSheafPullback_comp (h : X ⟶ Y) (k : Y ⟶ Z) :
    relativePicardFppfSheafPullback (h ≫ k) =
      relativePicardFppfSheafPullback k ≫ relativePicardFppfSheafPullback h := by
  apply (relativePicardFppfSheafHomEquiv Z.hom _).injective
  simp only [relativePicardFppfSheafHomEquiv_apply,
    relativePicardToFppfSheaf_comp_pullback, relativePicardAddPresheafPullback_comp,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    relativePicardToFppfSheaf_comp_pullback_assoc]

/-- A map factoring through a section of the base induces zero on the relative Picard
fppf sheaf. -/
lemma relativePicardFppfSheafPullback_eq_zero (h : X ⟶ Y)
    (s : Over.mk (𝟙 S) ⟶ Y) (hs : h.left = X.hom ≫ s.left) :
    relativePicardFppfSheafPullback h = 0 := by
  apply (relativePicardFppfSheafHomEquiv Y.hom _).injective
  simp [relativePicardFppfSheafHomEquiv_apply, relativePicardToFppfSheaf_comp_pullback,
    relativePicardAddPresheafPullback_eq_zero h s hs]

end

end TauCeti.AlgebraicGeometry
