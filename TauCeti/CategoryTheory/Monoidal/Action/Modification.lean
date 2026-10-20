/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import TauCeti.CategoryTheory.Monoidal.Action.LinearFunctor
public import TauCeti.CategoryTheory.Monoidal.Action.StrongTrans

/-!
# Equivariant natural transformations as modifications

Let a monoid `M` act on categories `C` and `D`, and let `F₁ F₂ : C ⥤ D` be equivariant functors
(left-linear for the actions of `Discrete M`). They correspond to the strong transformations
`strongTrans M F₁` and `strongTrans M F₂` between the pseudofunctors `pseudofunctor M C` and
`pseudofunctor M D`. This file shows that the equivariant natural transformations `F₁ ⟶ F₂`
(those satisfying `NatTrans.IsLeftLinear`) are exactly the modifications between these strong
transformations.

* `MonoidalLeftAction.modification M τ` is the modification whose component at the unique object
  is `τ`. Its naturality condition at `g` is the commutation of `τ` with the oplax lineators
  `δₗ F₁ ⟨g⟩` and `δₗ F₂ ⟨g⟩`.
* Conversely `MonoidalLeftAction.natTransOfModification Γ` is the component of a modification `Γ`
  at the unique object; it is equivariant.
* `MonoidalLeftAction.modificationEquiv M F₁ F₂` packages these as an equivalence between the
  equivariant natural transformations `F₁ ⟶ F₂` and the modifications. It sends identities to
  identities and vertical composites to vertical composites.
* `MonoidalLeftAction.strongTransIso M e` is the invertible modification attached to a natural
  isomorphism `e : F₁ ≅ F₂` with equivariant forward map.
* `MonoidalLeftAction.strongTransIdIso M` and `MonoidalLeftAction.strongTransCompIso M F G`
  compare the strong transformations of the identity functor and of a composite `F ⋙ G`, with
  the left-linear structures of `Functor.LeftLinear.id` and `Functor.LeftLinear.comp`, with the
  identity strong transformation and with the vertical composite
  `strongTrans M F ≫ strongTrans M G`. Both are invertible modifications with identity
  components.

Since every strong transformation `pseudofunctor M C ⟶ pseudofunctor M D` is definitionally
`strongTrans M (functorOfStrongTrans η)`, these statements describe the modifications between
arbitrary such strong transformations.
-/

public section

universe w v u

namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction

open Bicategory Functor.LaxLeftLinear Functor.OplaxLeftLinear
open scoped Pseudofunctor.StrongTrans

variable (M : Type u) [Monoid M] {C D : Type w} [Category.{v} C] [Category.{v} D]
  [MonoidalLeftAction (Discrete M) C] [MonoidalLeftAction (Discrete M) D]
  {F₁ F₂ F₃ : C ⥤ D} [F₁.LeftLinear (Discrete M)] [F₂.LeftLinear (Discrete M)]
  [F₃.LeftLinear (Discrete M)]

/-- An equivariant natural transformation `τ : F₁ ⟶ F₂` between equivariant functors is a
modification `strongTrans M F₁ ⟶ strongTrans M F₂` with component `τ` at the unique object. Its
naturality condition at `g` is `τ.app (g ⊙ₗ X) ≫ δₗ F₂ g X = δₗ F₁ g X ≫ g ⊴ₗ τ.app X`. -/
def modification (τ : F₁ ⟶ F₂) [NatTrans.IsLeftLinear τ (Discrete M)] :
    Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂) where
  app _ := τ.toCatHom₂
  -- As in `strongTrans`, the objects of `(pseudofunctor M C).obj a` are only definitionally
  -- objects of `C`, so the condition is stated componentwise in `C` and then applied.
  naturality g := by
    have h (X : C) : τ.app ((⟨g.as⟩ : Discrete M) ⊙ₗ X) ≫
          ((strongTrans M F₂).naturality g).hom.toNatTrans.app X =
        ((strongTrans M F₁).naturality g).hom.toNatTrans.app X ≫
          ((⟨g.as⟩ : Discrete M) ⊴ₗ τ.app X :
            (⟨g.as⟩ : Discrete M) ⊙ₗ F₁.obj X ⟶ (⟨g.as⟩ : Discrete M) ⊙ₗ F₂.obj X) := by
      rw [strongTrans_naturality_hom_toNatTrans_app, strongTrans_naturality_hom_toNatTrans_app]
      exact NatTrans.IsLeftLinear.app_comp_δₗ τ _ X
    ext X
    exact h X

/-- The component of `modification M τ` at every object is `τ`. -/
@[simp]
lemma modification_app_toNatTrans (τ : F₁ ⟶ F₂) [NatTrans.IsLeftLinear τ (Discrete M)]
    (a : LocallyDiscrete (SingleObj M)) :
    ((modification M τ).app a).toNatTrans = τ :=
  (rfl)

variable {M}

/-- The natural transformation `F₁ ⟶ F₂` underlying a modification
`Γ : strongTrans M F₁ ⟶ strongTrans M F₂`: its component at the unique object. -/
def natTransOfModification
    (Γ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂)) :
    F₁ ⟶ F₂ :=
  (Γ.app ⟨SingleObj.star M⟩).toNatTrans

/-- The components of the natural transformation underlying a modification. -/
lemma natTransOfModification_app
    (Γ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂)) (X : C) :
    (natTransOfModification Γ).app X = (Γ.app ⟨SingleObj.star M⟩).toNatTrans.app X :=
  (rfl)

/-- The natural transformation underlying a modification between the strong transformations of
equivariant functors is equivariant: the naturality condition of the modification at `g` is the
commutation with the oplax lineators `δₗ F₁ ⟨g⟩` and `δₗ F₂ ⟨g⟩`. -/
instance isLeftLinear_natTransOfModification
    (Γ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂)) :
    NatTrans.IsLeftLinear (natTransOfModification Γ) (Discrete M) :=
  .of_app_comp_δₗ _ fun c X ↦ by
    obtain ⟨g⟩ := c
    -- The naturality condition of `Γ` at `g`, evaluated at `X`, with its components computed.
    have h : (natTransOfModification Γ).app ((⟨g⟩ : Discrete M) ⊙ₗ X) ≫
          ((strongTrans M F₂).naturality (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩)
            ⟨g⟩).hom.toNatTrans.app X =
        ((strongTrans M F₁).naturality (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩)
            ⟨g⟩).hom.toNatTrans.app X ≫
          ((⟨g⟩ : Discrete M) ⊴ₗ (natTransOfModification Γ).app X :
            (⟨g⟩ : Discrete M) ⊙ₗ F₁.obj X ⟶ (⟨g⟩ : Discrete M) ⊙ₗ F₂.obj X) :=
      congrArg (·.toNatTrans.app X) (Γ.naturality (a := ⟨SingleObj.star M⟩)
        (b := ⟨SingleObj.star M⟩) ⟨g⟩)
    rwa [strongTrans_naturality_hom_toNatTrans_app,
      strongTrans_naturality_hom_toNatTrans_app] at h

/-- The natural transformation underlying `modification M τ` is `τ`. -/
@[simp]
lemma natTransOfModification_modification (τ : F₁ ⟶ F₂) [NatTrans.IsLeftLinear τ (Discrete M)] :
    natTransOfModification (modification M τ) = τ :=
  (rfl)

/-- Every modification `strongTrans M F₁ ⟶ strongTrans M F₂` is the modification of its
underlying natural transformation. -/
@[simp]
lemma modification_natTransOfModification
    (Γ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂)) :
    modification M (natTransOfModification Γ) = Γ := by
  ext ⟨⟨⟩⟩
  rfl

variable (M F₁) in
/-- The modification attached to the identity natural transformation is the identity
modification. -/
@[simp]
lemma modification_id :
    modification M (𝟙 F₁) = Pseudofunctor.StrongTrans.Modification.id (strongTrans M F₁) :=
  (rfl)

variable (M) in
/-- The modification attached to a vertical composite of equivariant natural transformations is
the vertical composite of the modifications. -/
@[simp]
lemma modification_comp (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) [NatTrans.IsLeftLinear τ (Discrete M)]
    [NatTrans.IsLeftLinear τ' (Discrete M)] :
    modification M (τ ≫ τ') = (modification M τ).vcomp (modification M τ') :=
  (rfl)

/-- The natural transformation underlying the identity modification is the identity. -/
@[simp]
lemma natTransOfModification_id :
    natTransOfModification (Pseudofunctor.StrongTrans.Modification.id (strongTrans M F₁)) =
      𝟙 F₁ :=
  (rfl)

/-- The natural transformation underlying a vertical composite of modifications is the composite
of the underlying natural transformations. -/
@[simp]
lemma natTransOfModification_vcomp
    (Γ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂))
    (Δ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₂) (strongTrans M F₃)) :
    natTransOfModification (Γ.vcomp Δ) = natTransOfModification Γ ≫ natTransOfModification Δ :=
  (rfl)

variable (M F₁ F₂) in
/-- Equivariant natural transformations `F₁ ⟶ F₂` correspond to modifications
`strongTrans M F₁ ⟶ strongTrans M F₂`. -/
def modificationEquiv : {τ : F₁ ⟶ F₂ // NatTrans.IsLeftLinear τ (Discrete M)} ≃
    Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂) where
  toFun τ := letI := τ.2; modification M τ.1
  invFun Γ := ⟨natTransOfModification Γ, inferInstance⟩
  left_inv _ := rfl
  right_inv := modification_natTransOfModification

/-- `modificationEquiv` sends an equivariant natural transformation to its modification. -/
@[simp]
lemma modificationEquiv_apply (τ : {τ : F₁ ⟶ F₂ // NatTrans.IsLeftLinear τ (Discrete M)}) :
    modificationEquiv M F₁ F₂ τ = letI := τ.2; modification M τ.1 :=
  (rfl)

/-- The inverse of `modificationEquiv` sends a modification to its underlying natural
transformation. -/
@[simp]
lemma modificationEquiv_symm_apply_coe
    (Γ : Pseudofunctor.StrongTrans.Modification (strongTrans M F₁) (strongTrans M F₂)) :
    ((modificationEquiv M F₁ F₂).symm Γ : F₁ ⟶ F₂) = natTransOfModification Γ :=
  (rfl)

variable (M) in
/-- A natural isomorphism `e : F₁ ≅ F₂` between equivariant functors whose forward map is
equivariant gives an invertible modification `strongTrans M F₁ ≅ strongTrans M F₂`, with
components `e.hom` and `e.inv` at the unique object. -/
def strongTransIso (e : F₁ ≅ F₂) [NatTrans.IsLeftLinear e.hom (Discrete M)] :
    Iso (C := pseudofunctor M C ⟶ pseudofunctor M D) (strongTrans M F₁) (strongTrans M F₂) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ ↦ Cat.Hom.isoMk e) (modification M e.hom).naturality

/-- The forward modification of `strongTransIso M e` is the modification of `e.hom`. -/
@[simp]
lemma strongTransIso_hom_as (e : F₁ ≅ F₂) [NatTrans.IsLeftLinear e.hom (Discrete M)] :
    (strongTransIso M e).hom.as = modification M e.hom :=
  (rfl)

/-- The inverse modification of `strongTransIso M e` is the modification of `e.inv`. -/
@[simp]
lemma strongTransIso_inv_as (e : F₁ ≅ F₂) [NatTrans.IsLeftLinear e.hom (Discrete M)] :
    (strongTransIso M e).inv.as = modification M e.inv :=
  (rfl)

variable (M) in
/-- The strong transformation attached to the identity functor, with its identity lineators, is
isomorphic to the identity strong transformation of `pseudofunctor M C`, through the invertible
modification whose component at the unique object is the identity. -/
def strongTransIdIso :
    Iso (C := pseudofunctor M C ⟶ pseudofunctor M C) (strongTrans M (𝟭 C))
      (𝟙 (pseudofunctor M C)) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ ↦ Iso.refl _) (fun g ↦ by
    have key (c : Discrete M) (X : C) : 𝟙 (c ⊙ₗ X) ≫ 𝟙 (c ⊙ₗ X) ≫ 𝟙 (c ⊙ₗ X) =
        δₗ (𝟭 C) c X ≫ c ⊴ₗ 𝟙 X := by
      simp
    -- The modification condition is computed componentwise in `C`, where the unitors of `Cat`
    -- and the identity `2`-morphisms contribute identities. The type ascriptions keep the
    -- composites in `C` rather than in the values of the pseudofunctor, so that `h X` closes the
    -- goal up to unfolding the bicategory structure of `Cat`.
    have h (X : C) : (𝟙 ((⟨g.as⟩ : Discrete M) ⊙ₗ X) ≫ 𝟙 ((⟨g.as⟩ : Discrete M) ⊙ₗ X) ≫
          𝟙 ((⟨g.as⟩ : Discrete M) ⊙ₗ X) :
          (⟨g.as⟩ : Discrete M) ⊙ₗ X ⟶ (⟨g.as⟩ : Discrete M) ⊙ₗ X) =
        (((strongTrans M (𝟭 C)).naturality g).hom.toNatTrans.app X ≫
          (⟨g.as⟩ : Discrete M) ⊴ₗ 𝟙 X :
          (⟨g.as⟩ : Discrete M) ⊙ₗ X ⟶ (⟨g.as⟩ : Discrete M) ⊙ₗ X) := by
      rw [strongTrans_naturality_hom_toNatTrans_app]
      exact key _ X
    ext X
    exact h X)

/-- The components of the forward modification of `strongTransIdIso M` are identities. -/
@[simp]
lemma strongTransIdIso_hom_as_app_toNatTrans (a : LocallyDiscrete (SingleObj M)) :
    ((strongTransIdIso M (C := C)).hom.as.app a).toNatTrans = 𝟙 (𝟭 C) :=
  (rfl)

/-- The components of the inverse modification of `strongTransIdIso M` are identities. -/
@[simp]
lemma strongTransIdIso_inv_as_app_toNatTrans (a : LocallyDiscrete (SingleObj M)) :
    ((strongTransIdIso M (C := C)).inv.as.app a).toNatTrans = 𝟙 (𝟭 C) :=
  (rfl)

section comp

variable {E : Type w} [Category.{v} E] [MonoidalLeftAction (Discrete M) E]

variable (M) in
/-- The strong transformation attached to a composite `F ⋙ G` of equivariant functors, with the
lineators of `Functor.LeftLinear.comp`, is isomorphic to the vertical composite of the strong
transformations of `F` and `G`, through the invertible modification whose component at the
unique object is the identity. -/
def strongTransCompIso (F : C ⥤ D) (G : D ⥤ E) [F.LeftLinear (Discrete M)]
    [G.LeftLinear (Discrete M)] :
    Iso (C := pseudofunctor M C ⟶ pseudofunctor M E) (strongTrans M (F ⋙ G))
      (strongTrans M F ≫ strongTrans M G) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ ↦ Iso.refl _) (fun g ↦ by
    have key (c : Discrete M) (X : C) :
        𝟙 (G.obj (F.obj (c ⊙ₗ X))) ≫ 𝟙 (G.obj (F.obj (c ⊙ₗ X))) ≫ G.map (δₗ F c X) ≫
          𝟙 (G.obj (c ⊙ₗ F.obj X)) ≫ δₗ G c (F.obj X) ≫ 𝟙 (c ⊙ₗ G.obj (F.obj X)) =
        δₗ (F ⋙ G) c X ≫ c ⊴ₗ 𝟙 (G.obj (F.obj X)) := by
      simp
    -- The modification condition is computed componentwise in `C`, where the associators of
    -- `Cat` and the identity `2`-morphisms contribute identities. As for `strongTransIdIso`, the
    -- type ascriptions keep the composites in `E`.
    have h (X : C) : (𝟙 (G.obj (F.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ X))) ≫
          𝟙 (G.obj (F.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ X))) ≫
          G.map (((strongTrans M F).naturality g).hom.toNatTrans.app X) ≫
          𝟙 (G.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ F.obj X)) ≫
          ((strongTrans M G).naturality g).hom.toNatTrans.app (F.obj X) ≫
          𝟙 ((⟨g.as⟩ : Discrete M) ⊙ₗ G.obj (F.obj X)) :
          G.obj (F.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ X)) ⟶
            (⟨g.as⟩ : Discrete M) ⊙ₗ G.obj (F.obj X)) =
        (((strongTrans M (F ⋙ G)).naturality g).hom.toNatTrans.app X ≫
          (⟨g.as⟩ : Discrete M) ⊴ₗ 𝟙 (G.obj (F.obj X)) :
          G.obj (F.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ X)) ⟶
            (⟨g.as⟩ : Discrete M) ⊙ₗ G.obj (F.obj X)) := by
      rw [strongTrans_naturality_hom_toNatTrans_app, strongTrans_naturality_hom_toNatTrans_app,
        strongTrans_naturality_hom_toNatTrans_app]
      exact key _ X
    ext X
    exact h X)

/-- The components of the forward modification of `strongTransCompIso M F G` are identities. -/
@[simp]
lemma strongTransCompIso_hom_as_app_toNatTrans (F : C ⥤ D) (G : D ⥤ E)
    [F.LeftLinear (Discrete M)] [G.LeftLinear (Discrete M)] (a : LocallyDiscrete (SingleObj M)) :
    ((strongTransCompIso M F G).hom.as.app a).toNatTrans = 𝟙 (F ⋙ G) :=
  (rfl)

/-- The components of the inverse modification of `strongTransCompIso M F G` are identities. -/
@[simp]
lemma strongTransCompIso_inv_as_app_toNatTrans (F : C ⥤ D) (G : D ⥤ E)
    [F.LeftLinear (Discrete M)] [G.LeftLinear (Discrete M)] (a : LocallyDiscrete (SingleObj M)) :
    ((strongTransCompIso M F G).inv.as.app a).toNatTrans = 𝟙 (F ⋙ G) :=
  (rfl)

end comp

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
