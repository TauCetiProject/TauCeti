/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Sites.Descent.Banding
public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.BandEquivalence

/-!
# The groupoid of band-preserving transformations

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be pseudofunctors such that the fibres `G.obj U` of `G` are
groupoids, for instance when `G` is a gerbe. Every modification `m : η ⟶ θ` of strong
transformations `F ⟶ G` is then invertible (`Pseudofunctor.isGroupoid_hom`);
`BandedMorphism.modificationIso` records this as an explicit isomorphism with forward
modification `m`. Hence, for `A`-bandings, band preservation is invariant under every
modification, invertible or not (`BandedMorphism.modification_iff`).

For `A`-bandings `bF`, `bG`, the band-preserving transformations `F ⟶ G` with all modifications
between them form the full subcategory `BandedMorphism.HomCategory bF bG` of Mathlib's category of
strong transformations. It is a groupoid (`BandedMorphism.groupoid`), with inverse given by
`BandedMorphism.homIso` (`BandedMorphism.groupoid_inv`), and each arrow `m : X ⟶ Y` has component
isomorphisms `X_U x ≅ Y_U x` in the fibres (`BandedMorphism.componentIso`). This is the groupoid
of morphisms of `A`-gerbes (Olsson, Definition 31.1 and Lemma 31.3).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `modificationIso`: a modification into a pseudofunctor with groupoid fibres as an isomorphism,
  with `modificationIso_hom`, `modificationIso_inv_app`, `hom_modificationIso_inv`,
  `modificationIso_inv_hom`, `modificationIso_id`, `modificationIso_comp`.
* `modification_iff`: a modification `η ⟶ θ` relates band preservation of `η` and of `θ`.
* `HomCategory`: the full subcategory of band-preserving transformations, with `HomCategory.mk`,
  `HomCategory.homMk` and `hom_ext`.
* `homIso`, `homIso_hom`, `homIso_inv_app`, `hom_homIso_inv`, `homIso_inv_hom`, `homIso_id`,
  `homIso_comp`, `isGroupoid_homCategory`, `hom_isIso`, `groupoid`, `groupoid_inv`,
  `groupoid_comp_inv`, `groupoid_inv_comp`.
* `componentIso`, `componentIso_hom`, `componentIso_inv`, `componentIso_id`, `componentIso_comp`,
  `componentIso_homIso_inv`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  [hG : ∀ U : C, IsGroupoid (G.obj (.mk (op U)))]

/-! ### Modifications into groupoid fibres are invertible -/

/-- **A modification into a pseudofunctor with groupoid fibres is an isomorphism**, with forward
modification `m`: it is `asIso m` for the instance `Pseudofunctor.isGroupoid_hom`, whose
hypothesis on all objects of `LocallyDiscrete Cᵒᵖ` follows from the one on test objects `U`. -/
noncomputable def modificationIso {η θ : F ⟶ G} (m : η ⟶ θ) : η ≅ θ :=
  haveI : ∀ a : LocallyDiscrete Cᵒᵖ, IsGroupoid (G.obj a) := fun a ↦ hG a.as.unop
  asIso m

@[simp]
theorem modificationIso_hom {η θ : F ⟶ G} (m : η ⟶ θ) : (modificationIso m).hom = m :=
  (rfl)

/-- The `(U, x)` component of the inverse of `modificationIso m` is the inverse of the component
of `m`. -/
@[simp]
theorem modificationIso_inv_app {η θ : F ⟶ G} (m : η ⟶ θ) (U : C)
    (x : F.obj (.mk (op U))) :
    ((modificationIso m).inv.as.app (.mk (op U))).toNatTrans.app x =
      inv ((m.as.app (.mk (op U))).toNatTrans.app x) := by
  refine IsIso.eq_inv_of_hom_inv_id ?_
  simpa using congrArg (fun φ : η ⟶ η ↦ (φ.as.app (.mk (op U))).toNatTrans.app x)
    (modificationIso m).hom_inv_id

@[simp]
theorem hom_modificationIso_inv {η θ : F ⟶ G} (m : η ⟶ θ) : m ≫ (modificationIso m).inv = 𝟙 η :=
  (modificationIso m).hom_inv_id

@[simp]
theorem modificationIso_inv_hom {η θ : F ⟶ G} (m : η ⟶ θ) : (modificationIso m).inv ≫ m = 𝟙 θ :=
  (modificationIso m).inv_hom_id

@[simp]
theorem modificationIso_id (η : F ⟶ G) : modificationIso (𝟙 η) = Iso.refl η :=
  Iso.ext rfl

theorem modificationIso_comp {η θ ι : F ⟶ G} (m : η ⟶ θ) (n : θ ⟶ ι) :
    modificationIso (m ≫ n) = modificationIso m ≪≫ modificationIso n :=
  Iso.ext rfl

/-! ### The groupoid of band-preserving transformations -/

variable {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  (bF : F.AbelianBanding J A) (bG : G.AbelianBanding J A)

/-- The property of a strong transformation `F ⟶ G` of preserving the bands `bF`, `bG`. -/
abbrev bandPreservingProperty : ObjectProperty (F ⟶ G) :=
  fun η ↦ BandPreserving bF bG η

/-- **The category of band-preserving transformations**: the full subcategory of Mathlib's
category of strong transformations `F ⟶ G` on those preserving the bands, with all modifications
between them. -/
abbrev HomCategory : Type _ :=
  (bandPreservingProperty bF bG).FullSubcategory

variable {bF bG}

/-- **Band preservation is invariant under modifications** into a pseudofunctor with groupoid
fibres: for any modification `m : η ⟶ θ`, `η` is band-preserving exactly when `θ` is. No
invertibility of `m` is assumed: `m` is invertible as `modificationIso m`. -/
theorem modification_iff {η θ : F ⟶ G} (m : η ⟶ θ) :
    BandPreserving bF bG η ↔ BandPreserving bF bG θ :=
  GerbeBandEquivalence.modificationIso_iff (modificationIso m)

/-- A band-preserving transformation as an object of `HomCategory bF bG`. -/
abbrev HomCategory.mk (η : F ⟶ G) [h : BandPreserving bF bG η] : HomCategory bF bG :=
  ⟨η, h⟩

instance (X : HomCategory bF bG) : BandPreserving bF bG X.obj :=
  X.property

/-- A modification between band-preserving transformations as an arrow of `HomCategory`. -/
abbrev HomCategory.homMk {X Y : HomCategory bF bG} (m : X.obj ⟶ Y.obj) : X ⟶ Y :=
  ObjectProperty.homMk m

omit hG in
/-- Arrows of `HomCategory` are determined by the natural transformations of their components. -/
theorem hom_ext {X Y : HomCategory bF bG} {m n : X ⟶ Y}
    (h : ∀ U : C, (m.hom.as.app (.mk (op U))).toNatTrans = (n.hom.as.app (.mk (op U))).toNatTrans) :
    m = n :=
  ObjectProperty.hom_ext _ (StrongTrans.homCategory.ext fun _ ↦ Cat.Hom₂.ext (h _))

/-- Every arrow of `HomCategory` is an isomorphism, with forward arrow `m`. -/
noncomputable def homIso {X Y : HomCategory bF bG} (m : X ⟶ Y) : X ≅ Y :=
  ObjectProperty.isoMk _ (modificationIso m.hom)

@[simp]
theorem homIso_hom {X Y : HomCategory bF bG} (m : X ⟶ Y) : (homIso m).hom = m :=
  (rfl)

/-- The `(U, x)` component of the inverse of `homIso m` is the inverse of the component of `m`. -/
@[simp]
theorem homIso_inv_app {X Y : HomCategory bF bG} (m : X ⟶ Y) (U : C) (x : F.obj (.mk (op U))) :
    ((homIso m).inv.hom.as.app (.mk (op U))).toNatTrans.app x =
      inv ((m.hom.as.app (.mk (op U))).toNatTrans.app x) := by
  simp [homIso]

@[simp]
theorem hom_homIso_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) : m ≫ (homIso m).inv = 𝟙 X :=
  (homIso m).hom_inv_id

@[simp]
theorem homIso_inv_hom {X Y : HomCategory bF bG} (m : X ⟶ Y) : (homIso m).inv ≫ m = 𝟙 Y :=
  (homIso m).inv_hom_id

@[simp]
theorem homIso_id (X : HomCategory bF bG) : homIso (𝟙 X) = Iso.refl X :=
  Iso.ext rfl

theorem homIso_comp {X Y Z : HomCategory bF bG} (m : X ⟶ Y) (n : Y ⟶ Z) :
    homIso (m ≫ n) = homIso m ≪≫ homIso n :=
  Iso.ext rfl

/-- `HomCategory` is a groupoid: its inclusion into the groupoid of strong transformations
`F ⟶ G` (`Pseudofunctor.isGroupoid_hom`) is fully faithful, so it reflects isomorphisms. -/
instance isGroupoid_homCategory : IsGroupoid (HomCategory bF bG) :=
  haveI : ∀ a : LocallyDiscrete Cᵒᵖ, IsGroupoid (G.obj a) := fun a ↦ hG a.as.unop
  isGroupoid_of_reflects_iso (ObjectProperty.ι _)

/-- Every arrow of `HomCategory` is an isomorphism. -/
theorem hom_isIso {X Y : HomCategory bF bG} (m : X ⟶ Y) : IsIso m :=
  inferInstance

variable (bF bG) in
/-- **The groupoid of band-preserving transformations.** -/
@[expose, instance_reducible]
noncomputable def groupoid : Groupoid (HomCategory bF bG) :=
  Groupoid.ofIsGroupoid

/-- The inverse in `groupoid` is the inverse of `homIso`. -/
theorem groupoid_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (groupoid bF bG).inv m = (homIso m).inv := by
  let := groupoid bF bG
  rw [Groupoid.inv_eq_inv]
  exact IsIso.inv_eq_of_hom_inv_id (homIso m).hom_inv_id

/-- The right inverse law of `groupoid`. -/
theorem groupoid_comp_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    m ≫ (groupoid bF bG).inv m = 𝟙 X := by
  rw [groupoid_inv, hom_homIso_inv]

/-- The left inverse law of `groupoid`. -/
theorem groupoid_inv_comp {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (groupoid bF bG).inv m ≫ m = 𝟙 Y := by
  rw [groupoid_inv, homIso_inv_hom]

/-- The component isomorphism `X_U x ≅ Y_U x` of an arrow `m : X ⟶ Y` of `HomCategory`. -/
noncomputable def componentIso {X Y : HomCategory bF bG} (m : X ⟶ Y) (U : C)
    (x : F.obj (.mk (op U))) :
    (X.obj.app (.mk (op U))).toFunctor.obj x ≅ (Y.obj.app (.mk (op U))).toFunctor.obj x :=
  asIso ((m.hom.as.app (.mk (op U))).toNatTrans.app x)

@[simp]
theorem componentIso_hom {X Y : HomCategory bF bG} (m : X ⟶ Y) (U : C)
    (x : F.obj (.mk (op U))) :
    (componentIso m U x).hom = (m.hom.as.app (.mk (op U))).toNatTrans.app x :=
  (rfl)

/-- The inverse of `componentIso m U x` is the inverse of the component of `m`. -/
@[simp]
theorem componentIso_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) (U : C)
    (x : F.obj (.mk (op U))) :
    (componentIso m U x).inv = inv ((m.hom.as.app (.mk (op U))).toNatTrans.app x) :=
  (rfl)

@[simp]
theorem componentIso_id (X : HomCategory bF bG) (U : C) (x : F.obj (.mk (op U))) :
    componentIso (𝟙 X) U x = Iso.refl _ :=
  Iso.ext rfl

theorem componentIso_comp {X Y Z : HomCategory bF bG} (m : X ⟶ Y) (n : Y ⟶ Z) (U : C)
    (x : F.obj (.mk (op U))) :
    componentIso (m ≫ n) U x = componentIso m U x ≪≫ componentIso n U x :=
  Iso.ext rfl

/-- The component of the inverse of `homIso m` is the inverse of the component of `m`. -/
@[simp]
theorem componentIso_homIso_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) (U : C)
    (x : F.obj (.mk (op U))) :
    componentIso (homIso m).inv U x = (componentIso m U x).symm := by
  ext
  simp [componentIso]

end CategoryTheory.Pseudofunctor.BandedMorphism
