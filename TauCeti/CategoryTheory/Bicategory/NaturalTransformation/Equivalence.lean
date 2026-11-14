/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import TauCeti.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Pointwise equivalences of strong transformations

A strong transformation `η : F ⟶ G` between pseudofunctors `F, G : B ⥤ᵖ C` into an arbitrary
bicategory `C` upgrades to an adjoint equivalence `F ≌ G` in the bicategory of pseudofunctors,
strong transformations, and modifications whenever each component `η.app a : F.obj a ⟶ G.obj a` is
equipped with a quasi-inverse `inv a` and unit and counit `2`-isomorphisms satisfying the left
triangle identity.

The inverse strong transformation has components `inv a` and naturality cells obtained from those
of `η` via `Bicategory.Equivalence.mateIsoEquiv` (inverted so they point from `G.map f ≫ inv b` to
`inv a ≫ F.map f`). Naturality, identity, and composition coherence of the inverse transformation,
as well as modification naturality of the componentwise units and counits, follow directly from the
naturality, vertical-pasting, unit, and counit laws of `mateEquiv`.

This generalizes the `Cat`-valued construction `StrongTrans.equivalenceOfIsEquivalence` to
arbitrary target bicategories, including bicategories of equivariant lifts.

## Main definitions

* `CategoryTheory.Pseudofunctor.StrongTrans.equivalenceMk`: construct an adjoint equivalence
  `F ≌ G` in `B ⥤ᵖ C` from `η : F ⟶ G` and componentwise adjoint-equivalence data.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Theorem 6.2.13: pointwise characterization
  of equivalences in pseudofunctor bicategories.
-/

public section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Pseudofunctor.StrongTrans

open Bicategory

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᵖ C}

section Helpers

variable (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
  (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
  (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
  (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)

private lemma inverseNaturality_naturality {a b : B} {f g : a ⟶ b} (ξ : f ⟶ g) :
    G.map₂ ξ ▷ inv b ≫
        (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)).mateIsoEquiv
          (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (h b))
          (η.naturality g)).symm).hom =
      (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)).mateIsoEquiv
          (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (h b))
          (η.naturality f)).symm).hom ≫
        inv a ◁ F.map₂ ξ := by
  set ea := Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)
  set eb := Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (h b)
  set θf := (ea.mateIsoEquiv eb (η.naturality f)).symm
  set θg := (ea.mateIsoEquiv eb (η.naturality g)).symm
  rw [← cancel_epi θf.inv, ← cancel_mono θg.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  simp only [θf, θg, Iso.symm_inv, Bicategory.Equivalence.mateIsoEquiv_apply_hom]
  exact ((ea.adj.whiskerLeft_comp_mateEquiv_eq_iff eb.adj).mpr (η.naturality_naturality ξ)).symm

private lemma inverseNaturality_id (a : B) :
    (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)).mateIsoEquiv
        (Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a))
        (η.naturality (𝟙 a))).symm).hom ≫ inv a ◁ (F.mapId a).hom =
      (G.mapId a).hom ▷ inv a ≫ (λ_ (inv a)).hom ≫ (ρ_ (inv a)).inv := by
  let ea : F.obj a ≌ G.obj a := ⟨η.app a, inv a, unit a, counit a, h a⟩
  let θ := (ea.mateIsoEquiv ea (η.naturality (𝟙 a))).symm
  let I₁ : G.map (𝟙 a) ≫ inv a ≅ inv a ≫ 𝟙 (F.obj a) :=
    θ ≪≫ whiskerLeftIso (inv a) (F.mapId a)
  let I₂ : G.map (𝟙 a) ≫ inv a ≅ inv a ≫ 𝟙 (F.obj a) :=
    whiskerRightIso (G.mapId a) (inv a) ≪≫ λ_ (inv a) ≪≫ (ρ_ (inv a)).symm
  have h_id : (F.mapId a).inv ▷ ea.hom ≫ (η.naturality (𝟙 a)).hom =
      ((λ_ ea.hom).hom ≫ (ρ_ ea.hom).inv) ≫ ea.hom ◁ (G.mapId a).inv := by
    dsimp only [ea]
    rw [← cancel_epi ((F.mapId a).hom ▷ η.app a), ← cancel_mono (η.app a ◁ (G.mapId a).hom)]
    simp only [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
      Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.comp_id,
      η.naturality_id]
  have h_inv : I₁.inv = I₂.inv := by
    dsimp only [I₁, I₂, θ]
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
      Bicategory.Equivalence.mateIsoEquiv_apply_hom, Category.assoc]
    have hv := (ea.adj.whiskerLeft_comp_mateEquiv_eq_iff ea.adj).mpr h_id
    rw [mateEquiv_leftUnitor_hom_rightUnitor_inv] at hv
    simpa only [ea, Category.assoc] using hv
  simpa only [I₁, I₂, θ, ea, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Category.assoc] using (I₁.inv_eq_inv I₂).mp h_inv

private lemma inverseNaturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)).mateIsoEquiv
        (Bicategory.Equivalence.mk (η.app c) (inv c) (unit c) (counit c) (h c))
        (η.naturality (f ≫ g))).symm).hom ≫ inv a ◁ (F.mapComp f g).hom =
      (G.mapComp f g).hom ▷ inv c ≫ (α_ _ _ _).hom ≫
        G.map f ◁
          (((Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (h b)).mateIsoEquiv
            (Bicategory.Equivalence.mk (η.app c) (inv c) (unit c) (counit c) (h c))
            (η.naturality g)).symm).hom ≫
        (α_ _ _ _).inv ≫
        (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)).mateIsoEquiv
          (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (h b))
          (η.naturality f)).symm).hom ▷ F.map g ≫
        (α_ _ _ _).hom := by
  let ea : F.obj a ≌ G.obj a := ⟨η.app a, inv a, unit a, counit a, h a⟩
  let eb : F.obj b ≌ G.obj b := ⟨η.app b, inv b, unit b, counit b, h b⟩
  let ec : F.obj c ≌ G.obj c := ⟨η.app c, inv c, unit c, counit c, h c⟩
  let θfg := (ea.mateIsoEquiv ec (η.naturality (f ≫ g))).symm
  let θf := (ea.mateIsoEquiv eb (η.naturality f)).symm
  let θg := (eb.mateIsoEquiv ec (η.naturality g)).symm
  let I₁ : G.map (f ≫ g) ≫ inv c ≅ inv a ≫ (F.map f ≫ F.map g) :=
    θfg ≪≫ whiskerLeftIso (inv a) (F.mapComp f g)
  let I₂ : G.map (f ≫ g) ≫ inv c ≅ inv a ≫ (F.map f ≫ F.map g) :=
    whiskerRightIso (G.mapComp f g) (inv c) ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso (G.map f) θg ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso θf (F.map g) ≪≫ α_ _ _ _
  have h_comp : (F.mapComp f g).inv ▷ η.app c ≫ (η.naturality (f ≫ g)).hom =
      leftAdjointSquare.vcomp (η.naturality f).hom (η.naturality g).hom ≫
        η.app a ◁ (G.mapComp f g).inv := by
    rw [← cancel_epi ((F.mapComp f g).hom ▷ η.app c), ← cancel_mono (η.app a ◁ (G.mapComp f g).hom)]
    simp only [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
      Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.comp_id,
      leftAdjointSquare.vcomp, η.naturality_comp]
  have h_inv : I₁.inv = I₂.inv := by
    dsimp only [I₁, I₂, θfg, θf, θg]
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
      Bicategory.Equivalence.mateIsoEquiv_apply_hom]
    have hv := (ea.adj.whiskerLeft_comp_mateEquiv_eq_iff ec.adj).mpr h_comp
    rw [mateEquiv_vcomp ea.adj eb.adj ec.adj] at hv
    simpa only [ea, eb, ec, rightAdjointSquare.vcomp, Category.assoc] using hv
  simpa only [I₁, I₂, θfg, θf, θg, ea, eb, ec, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, Category.assoc] using (I₁.inv_eq_inv I₂).mp h_inv

end Helpers

/-- A strong transformation `η : F ⟶ G` between pseudofunctors `F, G : B ⥤ᵖ C` upgrades to an
adjoint equivalence `F ≌ G` in `B ⥤ᵖ C` when each component `η.app a` is equipped with a
quasi-inverse `inv a` and unit and counit `2`-isomorphisms satisfying the left triangle identity.
The inverse naturality cells are the inverse mates of those of `η`. -/
-- Expose the record projections so the dependent unit and counit component equations can be stated.
@[expose] def equivalenceMk (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm) :
    F ≌ G where
  hom := η
  -- Keep the inverse data inline so exposing the record does not export proof-only helpers.
  inv :=
    { app := inv
      naturality {a b} f :=
        (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a)
            (left_triangle a)).mateIsoEquiv
          (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (left_triangle b))
          (η.naturality f)).symm)
      naturality_naturality ξ := by
        exact inverseNaturality_naturality η inv unit counit left_triangle ξ
      naturality_id a := by
        exact inverseNaturality_id η inv unit counit left_triangle a
      naturality_comp f g := by
        exact inverseNaturality_comp η inv unit counit left_triangle f g }
  unit := isoMk unit fun {a b} f ↦ by
    simpa only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom,
      Iso.symm_hom] using!
      (Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a)
        (left_triangle a)).unit_mateIsoEquiv_inv
        (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (left_triangle b))
        (η.naturality f)
  counit := isoMk counit fun {a b} f ↦ by
    simpa only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom,
      Iso.symm_hom] using!
      ((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a)
        (left_triangle a)).mateIsoEquiv_inv_counit
        (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (left_triangle b))
        (η.naturality f)).symm
  left_triangle := by
    apply Iso.ext
    simp only [leftZigzagIso_hom, leftZigzag, bicategoricalComp, Iso.trans_hom, Iso.symm_hom]
    apply homCategory.ext
    intro a
    have ha := congrArg Iso.hom (left_triangle a)
    simpa only [leftZigzagIso_hom, leftZigzag, bicategoricalComp, Iso.trans_hom, Iso.symm_hom,
      homCategory_comp_as_app, whiskerRight_as_app, whiskerLeft_as_app, associator_hom_as_app,
      leftUnitor_hom_as_app, rightUnitor_inv_as_app, isoMk_hom_as_app] using! ha

@[simp]
lemma equivalenceMk_hom (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm) :
    (η.equivalenceMk inv unit counit h).hom = η :=
  (rfl)

@[simp]
lemma equivalenceMk_inv_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceMk inv unit counit h).inv.app a = inv a :=
  (rfl)

@[simp]
lemma equivalenceMk_inv_naturality (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    {a b : B} (f : a ⟶ b) :
    (η.equivalenceMk inv unit counit h).inv.naturality f =
      (((Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (h a)).mateIsoEquiv
        (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (h b))
        (η.naturality f)).symm) :=
  (rfl)

@[simp]
lemma equivalenceMk_unit_hom_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceMk inv unit counit h).unit.hom.as.app a = (unit a).hom :=
  (rfl)

@[simp]
lemma equivalenceMk_unit_inv_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceMk inv unit counit h).unit.inv.as.app a = (unit a).inv :=
  (rfl)

@[simp]
lemma equivalenceMk_counit_hom_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceMk inv unit counit h).counit.hom.as.app a = (counit a).hom :=
  (rfl)

@[simp]
lemma equivalenceMk_counit_inv_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (h : ∀ a : B, leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceMk inv unit counit h).counit.inv.as.app a = (counit a).inv :=
  (rfl)

end CategoryTheory.Pseudofunctor.StrongTrans
