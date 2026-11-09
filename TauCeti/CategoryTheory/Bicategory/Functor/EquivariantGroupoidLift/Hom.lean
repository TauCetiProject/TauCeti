/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat

/-!
# Morphisms of equivariant groupoid lifts

Let `L L' : EquivariantGroupoidLift Γ actions` be two coherent equivariant lifts of the same
family of categorical actions of a monoid `H` along a category `Γ`. A morphism `φ : L.Hom L'`
consists of a strong transformation `φ.joint : L.joint ⟶ L'.joint` of the joint pseudofunctors
together with, for each `p : Γ`, an invertible modification

`φ.fiberIso p : φ.joint|_p ≫ L'.comparison p ≅ L.comparison p`

between strong transformations from the restriction of `L.joint` to the fiber
`{p} × SingleObj H` to the prescribed action `actions p`. Here `φ.joint|_p` is the whiskering of
`φ.joint` by `Prod.sectR p (SingleObj H)`. So `φ` is compatible with the fiber comparisons,
equivariantly for the actions of `H`.

A `2`-morphism `Θ : φ ⟶ ψ` is a modification `Θ.joint : φ.joint ⟶ ψ.joint` compatible with the
fiber isomorphisms of `φ` and `ψ`. These form a category `L.Hom L'`, whose isomorphisms are the
invertible modifications compatible with the fiber isomorphisms (`Hom.isoMk`). Morphisms have an
identity `Hom.id` and a composite `Hom.comp`, whose fiber isomorphisms are assembled from those of
the factors with the associator and unitors of the bicategory of pseudofunctors.

On the prescribed fibers, a morphism `φ` compares the transport functors of `L` and `L'`:
`Hom.transportIso φ g : L.transport g ≅ L'.transport g` combines the naturality isomorphism of
`φ.joint` at `(g, 1)` with the components of the fiber isomorphisms at `p` and `q`.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom`: morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.Hom.id`, `TauCeti.EquivariantGroupoidLift.Hom.comp`: the
  identity and composite morphisms;
* `TauCeti.EquivariantGroupoidLift.Hom.Hom₂`: compatible modifications, the morphisms of the
  category `L.Hom L'`, with extensionality `Hom.hom₂_ext` on the joint modification;
* `TauCeti.EquivariantGroupoidLift.Hom.isoMk`: invertible compatible modifications as
  isomorphisms of `L.Hom L'`;
* `TauCeti.EquivariantGroupoidLift.Hom.fiberFunctorIso`: the component
  `φ_p ⋙ e'_p ≅ e_p` of the fiber isomorphism at the unique object;
* `TauCeti.EquivariantGroupoidLift.Hom.jointMapIso`,
  `TauCeti.EquivariantGroupoidLift.Hom.inverseFiberIso`: the naturality isomorphism of the joint
  transformation at `(g, 1)`, and the comparison `e_p⁻¹ ⋙ φ_p ≅ e'_p⁻¹` of inverse fiber
  comparisons;
* `TauCeti.EquivariantGroupoidLift.Hom.transportIso`: the induced isomorphisms
  `L.transport g ≅ L'.transport g` of transport functors on the prescribed fibers.

## References

* Niles Johnson and Donald Yau, [2-Dimensional Categories](https://arxiv.org/abs/2002.06055),
  Oxford University Press (2021), Chapter 4: strong transformations and modifications.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): the families of local categories over
  the groupoid of local Langlands parameters.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- A morphism of coherent equivariant lifts `L ⟶ L'` of the same family of actions: a strong
transformation `joint` of the joint pseudofunctors, together with, for each `p : Γ`, an invertible
modification identifying the restriction of `joint` to the fiber `{p} × SingleObj H`, followed by
the fiber comparison of `L'`, with the fiber comparison of `L`. -/
structure Hom (L L' : EquivariantGroupoidLift Γ actions) where
  /-- The strong transformation of joint pseudofunctors. -/
  joint : L.joint ⟶ L'.joint
  /-- The compatibility of `joint` with the fiber comparisons at `p`. -/
  fiberIso (p : Γ) :
    (Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft joint ≫ L'.comparison p ≅
      L.comparison p

namespace Hom

variable {L L' L'' : EquivariantGroupoidLift Γ actions}

/-- The identity morphism of a lift. Its fiber isomorphism at `p` is the left unitor of the fiber
comparison of `L`. -/
-- The body is exposed so that the joint transformation of `id L` is definitionally `𝟙 L.joint`,
-- which the statement of `id_fiberIso_hom_as_app` requires.
@[expose] noncomputable def id (L : EquivariantGroupoidLift Γ actions) : L.Hom L where
  joint := 𝟙 L.joint
  fiberIso p :=
    whiskerRightIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeftId L.joint) (L.comparison p) ≪≫
      leftUnitor (L.comparison p)

@[simp]
lemma id_joint (L : EquivariantGroupoidLift Γ actions) : (id L).joint = 𝟙 L.joint :=
  (rfl)

@[simp]
lemma id_fiberIso_hom_as_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((id L).fiberIso p).hom.as.app a = (λ_ ((L.comparison p).app a)).hom :=
  (congrArg (· ≫ _) ((congrArg (· ▷ _) (Pseudofunctor.whiskerLeftId_hom_as_app _ _ _)).trans
    (id_whiskerRight _ _))).trans (Category.id_comp _)

@[simp]
lemma id_fiberIso_inv_as_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((id L).fiberIso p).inv.as.app a = (λ_ ((L.comparison p).app a)).inv :=
  (congrArg (_ ≫ ·) ((congrArg (· ▷ _) (Pseudofunctor.whiskerLeftId_inv_as_app _ _ _)).trans
    (id_whiskerRight _ _))).trans (Category.comp_id _)

/-- The composite of two morphisms of lifts. Its fiber isomorphism at `p` whiskers the fiber
isomorphism of the second morphism by the restriction of the first, and follows it by the fiber
isomorphism of the first. -/
-- The body is exposed so that the joint transformation of `φ.comp ψ` is definitionally
-- `φ.joint ≫ ψ.joint`, which the statement of `comp_fiberIso_hom_as_app` requires.
@[expose] noncomputable def comp (φ : L.Hom L') (ψ : L'.Hom L'') : L.Hom L'' where
  joint := φ.joint ≫ ψ.joint
  fiberIso p :=
    whiskerRightIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeftComp φ.joint ψ.joint)
        (L''.comparison p) ≪≫
      Pseudofunctor.StrongTrans.associator _ _ _ ≪≫
      whiskerLeftIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) _ (ψ.fiberIso p) ≪≫
      φ.fiberIso p

@[simp]
lemma comp_joint (φ : L.Hom L') (ψ : L'.Hom L'') : (φ.comp ψ).joint = φ.joint ≫ ψ.joint :=
  (rfl)

@[simp]
lemma comp_fiberIso_hom_as_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((φ.comp ψ).fiberIso p).hom.as.app a =
      (α_ (φ.joint.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a))
          (ψ.joint.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a))
          ((L''.comparison p).app a)).hom ≫
        φ.joint.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ◁
          (ψ.fiberIso p).hom.as.app a ≫ (φ.fiberIso p).hom.as.app a := by
  simp only [comp, Iso.trans_hom, homCategory_comp_as_app]
  -- The first factor is the identity component of `whiskerLeftComp`, whiskered by the fiber
  -- comparison; its source agrees with the composite only up to unfolding, so it is removed by a
  -- term rather than by rewriting.
  refine (congrArg (· ≫ _) ((congrArg (· ▷ (L''.comparison p).app a)
    (Pseudofunctor.whiskerLeftComp_hom_as_app (Prod.sectR p (SingleObj H)).toPseudofunctor
      φ.joint ψ.joint a)).trans (id_whiskerRight _ _))).trans ?_
  exact Category.id_comp _

@[simp]
lemma comp_fiberIso_inv_as_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((φ.comp ψ).fiberIso p).inv.as.app a =
      (φ.fiberIso p).inv.as.app a ≫
        φ.joint.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ◁
          (ψ.fiberIso p).inv.as.app a ≫
        (α_ (φ.joint.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a))
          (ψ.joint.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a))
          ((L''.comparison p).app a)).inv := by
  simp only [comp, Iso.trans_inv, homCategory_comp_as_app]
  -- As in `comp_fiberIso_hom_as_app`, the last factor is an identity component whiskered by the
  -- fiber comparison.
  have h : (whiskerRightIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
      ((Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeftComp φ.joint ψ.joint)
      (L''.comparison p)).inv.as.app a = 𝟙 _ :=
    (congrArg (· ▷ (L''.comparison p).app a)
      (Pseudofunctor.whiskerLeftComp_inv_as_app _ φ.joint ψ.joint a)).trans (id_whiskerRight _ _)
  rw [h]
  exact (Category.comp_id _).trans (Category.assoc _ _ _)

/-- A `2`-morphism `φ ⟶ ψ` of morphisms of lifts: a modification of the joint strong
transformations, compatible with the fiber isomorphisms of `φ` and `ψ` at every object of every
fiber. -/
structure Hom₂ (φ ψ : L.Hom L') where
  /-- The modification of joint strong transformations. -/
  joint : φ.joint ⟶ ψ.joint
  /-- The compatibility of `joint` with the fiber isomorphisms. -/
  comm (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    joint.as.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ▷ (L'.comparison p).app a ≫
      (ψ.fiberIso p).hom.as.app a = (φ.fiberIso p).hom.as.app a

attribute [reassoc] Hom₂.comm
attribute [simp] Hom₂.comm

/-- Morphisms of lifts and their compatible modifications form a category. -/
instance : Category (L.Hom L') where
  Hom := Hom₂
  id φ := ⟨𝟙 φ.joint, fun p a =>
    (congrArg (· ≫ _) (id_whiskerRight _ _)).trans (Category.id_comp _)⟩
  comp {φ ψ χ} Θ Ξ := ⟨Θ.joint ≫ Ξ.joint, fun p a =>
    (congrArg (· ≫ _) (comp_whiskerRight _ _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Ξ.comm p a)).trans (Θ.comm p a)))⟩

@[ext]
lemma hom₂_ext {φ ψ : L.Hom L'} {Θ Ξ : φ ⟶ ψ} (h : Θ.joint = Ξ.joint) : Θ = Ξ := by
  cases Θ; cases Ξ; congr

@[simp]
lemma Hom₂.id_joint (φ : L.Hom L') : Hom₂.joint (𝟙 φ) = 𝟙 φ.joint :=
  (rfl)

@[simp]
lemma Hom₂.comp_joint {φ ψ χ : L.Hom L'} (Θ : φ ⟶ ψ) (Ξ : ψ ⟶ χ) :
    Hom₂.joint (Θ ≫ Ξ) = Θ.joint ≫ Ξ.joint :=
  (rfl)

/-- An invertible modification of joint strong transformations, compatible with the fiber
isomorphisms, is an isomorphism of morphisms of lifts. -/
def isoMk {φ ψ : L.Hom L'} (e : φ.joint ≅ ψ.joint)
    (comm : ∀ (p : Γ) (a : LocallyDiscrete (SingleObj H)),
      e.hom.as.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ▷
          (L'.comparison p).app a ≫ (ψ.fiberIso p).hom.as.app a =
        (φ.fiberIso p).hom.as.app a) :
    φ ≅ ψ where
  hom := ⟨e.hom, comm⟩
  inv := ⟨e.inv, fun p a => by
    rw [← comm p a]
    simpa only [isoApp_hom, isoApp_inv] using inv_hom_whiskerRight_assoc
      (isoApp e ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a)) ((L'.comparison p).app a)
      ((ψ.fiberIso p).hom.as.app a)⟩
  hom_inv_id := hom₂_ext e.hom_inv_id
  inv_hom_id := hom₂_ext e.inv_hom_id

@[simp]
lemma isoMk_hom_joint {φ ψ : L.Hom L'} (e : φ.joint ≅ ψ.joint)
    (comm : ∀ (p : Γ) (a : LocallyDiscrete (SingleObj H)),
      e.hom.as.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ▷
          (L'.comparison p).app a ≫ (ψ.fiberIso p).hom.as.app a =
        (φ.fiberIso p).hom.as.app a) :
    (isoMk e comm).hom.joint = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_joint {φ ψ : L.Hom L'} (e : φ.joint ≅ ψ.joint)
    (comm : ∀ (p : Γ) (a : LocallyDiscrete (SingleObj H)),
      e.hom.as.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ▷
          (L'.comparison p).app a ≫ (ψ.fiberIso p).hom.as.app a =
        (φ.fiberIso p).hom.as.app a) :
    (isoMk e comm).inv.joint = e.inv :=
  (rfl)

/-- A compatible modification is invertible if its underlying joint modification is. -/
lemma isIso_of_isIso_joint {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ) [IsIso Θ.joint] : IsIso Θ := by
  let e : φ ≅ ψ := isoMk (asIso Θ.joint) Θ.comm
  have he : e.hom = Θ := hom₂_ext (by simp [e])
  rw [← he]
  infer_instance

/-- The joint modification of an isomorphism of morphisms of lifts is an isomorphism. -/
def jointIso {φ ψ : L.Hom L'} (e : φ ≅ ψ) : φ.joint ≅ ψ.joint where
  hom := e.hom.joint
  inv := e.inv.joint
  hom_inv_id := by rw [← Hom₂.comp_joint, e.hom_inv_id, Hom₂.id_joint]
  inv_hom_id := by rw [← Hom₂.comp_joint, e.inv_hom_id, Hom₂.id_joint]

@[simp]
lemma jointIso_hom {φ ψ : L.Hom L'} (e : φ ≅ ψ) : (jointIso e).hom = e.hom.joint :=
  (rfl)

@[simp]
lemma jointIso_inv {φ ψ : L.Hom L'} (e : φ ≅ ψ) : (jointIso e).inv = e.inv.joint :=
  (rfl)

/-! ### Components on the prescribed fibers -/

/-- The functor `φ_p : F (p, ⋆) ⥤ F' (p, ⋆)` given by the component of the joint strong
transformation at `(p, ⋆)`. -/
abbrev jointFunctor (φ : L.Hom L') (p : Γ) : L.jointFiber p ⥤ L'.jointFiber p :=
  (φ.joint.app ⟨(p, SingleObj.star H)⟩).toFunctor

@[simp]
lemma id_jointFunctor (L : EquivariantGroupoidLift Γ actions) (p : Γ) :
    (id L).jointFunctor p = 𝟭 (L.jointFiber p) := by
  simp [jointFunctor]

@[simp]
lemma comp_jointFunctor (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ) :
    (φ.comp ψ).jointFunctor p = φ.jointFunctor p ⋙ ψ.jointFunctor p := by
  simp [jointFunctor, comp_app]

/-- The component `φ_p ⋙ e'_p ≅ e_p` of the fiber isomorphism of `φ` at the unique object of the
fiber, where `e_p` and `e'_p` are the fiber comparisons of `L` and `L'`. -/
noncomputable def fiberFunctorIso (φ : L.Hom L') (p : Γ) :
    φ.jointFunctor p ⋙ (L'.fiberEquivalence p).functor ≅ (L.fiberEquivalence p).functor :=
  Cat.Hom.toNatIso (isoApp (φ.fiberIso p) ⟨SingleObj.star H⟩)

@[simp]
lemma fiberFunctorIso_hom_app (φ : L.Hom L') (p : Γ) (Y : L.jointFiber p) :
    (φ.fiberFunctorIso p).hom.app Y =
      ((φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩).toNatTrans.app Y :=
  congrArg (fun m => m.toNatTrans.app Y) (isoApp_hom (φ.fiberIso p) ⟨SingleObj.star H⟩)

@[simp]
lemma fiberFunctorIso_inv_app (φ : L.Hom L') (p : Γ) (Y : L.jointFiber p) :
    (φ.fiberFunctorIso p).inv.app Y =
      ((φ.fiberIso p).inv.as.app ⟨SingleObj.star H⟩).toNatTrans.app Y :=
  congrArg (fun m => m.toNatTrans.app Y) (isoApp_inv (φ.fiberIso p) ⟨SingleObj.star H⟩)

lemma id_fiberFunctorIso_hom_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (Y : L.jointFiber p) :
    ((id L).fiberFunctorIso p).hom.app Y = 𝟙 _ := by
  rw [fiberFunctorIso_hom_app, id_fiberIso_hom_as_app]
  rfl

lemma id_fiberFunctorIso_inv_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (Y : L.jointFiber p) :
    ((id L).fiberFunctorIso p).inv.app Y = 𝟙 _ := by
  rw [fiberFunctorIso_inv_app, id_fiberIso_inv_as_app]
  rfl

lemma comp_fiberFunctorIso_hom_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (Y : L.jointFiber p) :
    ((φ.comp ψ).fiberFunctorIso p).hom.app Y =
      (ψ.fiberFunctorIso p).hom.app ((φ.jointFunctor p).obj Y) ≫
        (φ.fiberFunctorIso p).hom.app Y := by
  -- Give restricted components their joint-fiber endpoints before simplifying in Cat.
  let F : L.jointFiber p ⟶ L'.jointFiber p := φ.joint.app ⟨(p, SingleObj.star H)⟩
  let G : L'.jointFiber p ⟶ L''.jointFiber p := ψ.joint.app ⟨(p, SingleObj.star H)⟩
  let E : L''.jointFiber p ⟶ fiber actions p := (L''.comparison p).app ⟨SingleObj.star H⟩
  let E' : L'.jointFiber p ⟶ fiber actions p := (L'.comparison p).app ⟨SingleObj.star H⟩
  let E₀ : L.jointFiber p ⟶ fiber actions p := (L.comparison p).app ⟨SingleObj.star H⟩
  let a : G ≫ E ⟶ E' :=
    (ψ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
  let b : F ≫ E' ⟶ E₀ :=
    (φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
  have h : ((α_ F G E).hom ≫ F ◁ a ≫ b).toNatTrans.app Y =
      a.toNatTrans.app (F.toFunctor.obj Y) ≫ b.toNatTrans.app Y := by
    simp
  simp only [fiberFunctorIso_hom_app]
  exact (congrArg (fun m => m.toNatTrans.app Y)
      (comp_fiberIso_hom_as_app φ ψ p ⟨SingleObj.star H⟩)).trans h

lemma comp_fiberFunctorIso_inv_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (Y : L.jointFiber p) :
    ((φ.comp ψ).fiberFunctorIso p).inv.app Y =
      (φ.fiberFunctorIso p).inv.app Y ≫
        (ψ.fiberFunctorIso p).inv.app ((φ.jointFunctor p).obj Y) := by
  -- Give restricted components their joint-fiber endpoints before simplifying in Cat.
  let F : L.jointFiber p ⟶ L'.jointFiber p := φ.joint.app ⟨(p, SingleObj.star H)⟩
  let G : L'.jointFiber p ⟶ L''.jointFiber p := ψ.joint.app ⟨(p, SingleObj.star H)⟩
  let E : L''.jointFiber p ⟶ fiber actions p := (L''.comparison p).app ⟨SingleObj.star H⟩
  let E' : L'.jointFiber p ⟶ fiber actions p := (L'.comparison p).app ⟨SingleObj.star H⟩
  let E₀ : L.jointFiber p ⟶ fiber actions p := (L.comparison p).app ⟨SingleObj.star H⟩
  let a : E' ⟶ G ≫ E :=
    (ψ.fiberIso p).inv.as.app ⟨SingleObj.star H⟩
  let b : E₀ ⟶ F ≫ E' :=
    (φ.fiberIso p).inv.as.app ⟨SingleObj.star H⟩
  have h : (b ≫ F ◁ a ≫ (α_ F G E).inv).toNatTrans.app Y =
      b.toNatTrans.app Y ≫ a.toNatTrans.app (F.toFunctor.obj Y) := by
    simp
  simp only [fiberFunctorIso_inv_app]
  exact (congrArg (fun m => m.toNatTrans.app Y)
      (comp_fiberIso_inv_as_app φ ψ p ⟨SingleObj.star H⟩)).trans h

/-- The prescribed-fiber comparison of the identity lift morphism is the identity. -/
@[simp]
lemma id_fiberFunctorIso (L : EquivariantGroupoidLift Γ actions) (p : Γ) :
    (id L).fiberFunctorIso p = Iso.refl (L.fiberEquivalence p).functor := by
  ext Y
  exact id_fiberFunctorIso_hom_app L p Y

/-- Prescribed-fiber comparisons compose by whiskering the second comparison and then
applying the first. -/
@[simp]
lemma comp_fiberFunctorIso (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ) :
    (φ.comp ψ).fiberFunctorIso p =
      Functor.isoWhiskerLeft (φ.jointFunctor p) (ψ.fiberFunctorIso p) ≪≫
        φ.fiberFunctorIso p := by
  ext Y
  exact comp_fiberFunctorIso_hom_app φ ψ p Y

/-- The naturality isomorphism `F (g, 1) ⋙ φ_q ≅ φ_p ⋙ F' (g, 1)` of the joint strong
transformation at the arrow `(g, 1)`. -/
noncomputable def jointMapIso (φ : L.Hom L') {p q : Γ} (g : p ⟶ q) :
    L.jointMap g ⋙ φ.jointFunctor q ≅ φ.jointFunctor p ⋙ L'.jointMap g :=
  Cat.Hom.toNatIso (φ.joint.naturality (g ×ₘ 𝟙 (SingleObj.star H)).toLoc)

@[simp]
lemma jointMapIso_hom_app (φ : L.Hom L') {p q : Γ} (g : p ⟶ q) (Y : L.jointFiber p) :
    (φ.jointMapIso g).hom.app Y =
      (φ.joint.naturality (g ×ₘ 𝟙 (SingleObj.star H)).toLoc).hom.toNatTrans.app Y :=
  (rfl)

@[simp]
lemma jointMapIso_inv_app (φ : L.Hom L') {p q : Γ} (g : p ⟶ q) (Y : L.jointFiber p) :
    (φ.jointMapIso g).inv.app Y =
      (φ.joint.naturality (g ×ₘ 𝟙 (SingleObj.star H)).toLoc).inv.toNatTrans.app Y :=
  (rfl)

lemma id_jointMapIso_hom_app (L : EquivariantGroupoidLift Γ actions) {p q : Γ}
    (g : p ⟶ q) (Y : L.jointFiber p) :
    ((id L).jointMapIso g).hom.app Y = 𝟙 _ := by
  let T : L.jointFiber p ⟶ L.jointFiber q :=
    L.joint.map (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
  have h : ((ρ_ T).hom ≫ (λ_ T).inv).toNatTrans.app Y = 𝟙 _ := by simp
  rw [jointMapIso_hom_app]
  exact (congrArg (fun m => m.toNatTrans.app Y)
    (categoryStruct_id_naturality_hom L.joint (g ×ₘ 𝟙 (SingleObj.star H)).toLoc)).trans h

lemma comp_jointMapIso_hom_app (φ : L.Hom L') (ψ : L'.Hom L'') {p q : Γ}
    (g : p ⟶ q) (Y : L.jointFiber p) :
    ((φ.comp ψ).jointMapIso g).hom.app Y =
      (ψ.jointFunctor q).map ((φ.jointMapIso g).hom.app Y) ≫
        (ψ.jointMapIso g).hom.app ((φ.jointFunctor p).obj Y) := by
  simp only [jointMapIso_hom_app]
  exact Pseudofunctor.StrongTrans.comp_naturality_hom_app φ.joint ψ.joint
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc Y

/-- The joint naturality cell respects the unit comparisons. -/
@[reassoc]
lemma jointMapIso_hom_app_comp_jointMapId (φ : L.Hom L') (p : Γ) (Y : L.jointFiber p) :
    (φ.jointMapIso (𝟙 p)).hom.app Y ≫
        (L'.jointMapId p).hom.app ((φ.jointFunctor p).obj Y) =
      (φ.jointFunctor p).map ((L.jointMapId p).hom.app Y) := by
  dsimp only [jointFunctor]
  have h := congrArg (fun t => t.toNatTrans.app Y)
    (φ.joint.naturality_id ⟨(p, SingleObj.star H)⟩)
  simp only [jointMapIso_hom_app, EquivariantGroupoidLift.jointMapId_hom_app,
    Pseudofunctor.mapId'_eq_mapId, ← prod_id, Quiver.Hom.id_toLoc]
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
    Cat.whiskerRight_app, Cat.leftUnitor_hom_toNatTrans,
    Cat.rightUnitor_inv_toNatTrans, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app] at h
  exact h.trans ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.comp_id _))

/-- The joint naturality cells respect the composition comparisons. -/
@[reassoc]
lemma jointMapIso_hom_app_comp_jointMapComp (φ : L.Hom L') {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (Y : L.jointFiber p) :
    (φ.jointMapIso gh).hom.app Y ≫
        (L'.jointMapComp g h gh hgh).hom.app ((φ.jointFunctor p).obj Y) =
      (φ.jointFunctor r).map ((L.jointMapComp g h gh hgh).hom.app Y) ≫
        (φ.jointMapIso h).hom.app ((L.jointMap g).obj Y) ≫
          (L'.jointMap h).map ((φ.jointMapIso g).hom.app Y) := by
  have hc := φ.joint.naturality_comp'_hom_app
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc (by simp [← Quiver.Hom.comp_toLoc, hgh]) Y
  rw [jointMapIso_hom_app, hc]
  simp only [EquivariantGroupoidLift.jointMapComp_hom_app, jointMapIso_hom_app,
    Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.comp_id _))

/-- The joint naturality cells respect the inverse composition comparisons. -/
@[reassoc]
lemma jointMapIso_comp_inv_app (φ : L.Hom L') {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (Y : L.jointFiber p) :
    (φ.jointMapIso h).hom.app ((L.jointMap g).obj Y) ≫
        (L'.jointMap h).map ((φ.jointMapIso g).hom.app Y) ≫
          (L'.jointMapComp g h gh hgh).inv.app ((φ.jointFunctor p).obj Y) =
      (φ.jointFunctor r).map ((L.jointMapComp g h gh hgh).inv.app Y) ≫
        (φ.jointMapIso gh).hom.app Y := by
  rw [← cancel_epi ((φ.jointFunctor r).map ((L.jointMapComp g h gh hgh).hom.app Y))]
  erw [← φ.jointMapIso_hom_app_comp_jointMapComp_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).trans
    (((congrArg (· ≫ _) ((φ.jointFunctor r).map_id _)).trans (Category.id_comp _)).symm)

/-- The isomorphism `e_p⁻¹ ⋙ φ_p ≅ e'_p⁻¹` between inverse fiber comparisons, obtained from the
fiber isomorphism `φ_p ⋙ e'_p ≅ e_p`. -/
noncomputable def inverseFiberIso (φ : L.Hom L') (p : Γ) :
    (L.fiberEquivalence p).inverse ⋙ φ.jointFunctor p ≅ (L'.fiberEquivalence p).inverse :=
  Iso.inverseCompIso (Iso.isoCompInverse (φ.fiberFunctorIso p))

/-- The inverse-fiber comparison is the mate of the specified fiber comparison. -/
@[reassoc]
lemma functor_map_inverseFiberIso_hom_app_comp_counit (φ : L.Hom L') (p : Γ) (X : fiber actions p) :
    (L'.fiberEquivalence p).functor.map ((φ.inverseFiberIso p).hom.app X) ≫
        (L'.fiberEquivalence p).counit.app X =
      (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj X) ≫
        (L.fiberEquivalence p).counit.app X := by
  simp only [inverseFiberIso, Iso.inverseCompIso_hom_app, Iso.isoCompInverse_hom_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  -- The comparison has a composite strong-transformation source; identify its projections.
  erw [(L'.fiberEquivalence p).counit_naturality,
    (L'.fiberEquivalence p).counit_naturality_assoc,
    (L'.fiberEquivalence p).functor_unit_comp_assoc]

/-- The inverse-fiber comparison respects the units of the two chosen equivalences. -/
@[reassoc]
lemma inverseFiberIso_hom_app_comp_unitInv (φ : L.Hom L') (p : Γ) (Y : L.jointFiber p) :
    (φ.inverseFiberIso p).hom.app ((L.fiberEquivalence p).functor.obj Y) ≫
        (L'.fiberEquivalence p).inverse.map ((φ.fiberFunctorIso p).inv.app Y) ≫
          (L'.fiberEquivalence p).unitInv.app ((φ.jointFunctor p).obj Y) =
      (φ.jointFunctor p).map ((L.fiberEquivalence p).unitInv.app Y) := by
  apply (L'.fiberEquivalence p).functor.map_injective
  simp only [Functor.map_comp]
  erw [← (L'.fiberEquivalence p).counit_app_functor, (L'.fiberEquivalence p).counit_naturality,
    φ.functor_map_inverseFiberIso_hom_app_comp_counit_assoc,
    (L.fiberEquivalence p).counit_app_functor, ← (φ.fiberFunctorIso p).hom.naturality_assoc]
  simp only [Functor.id_obj, Functor.comp_map, Iso.hom_inv_id_app, Category.comp_id]

/-- The mate of the identity fiber comparison is the identity, even with arbitrary chosen
quasi-inverses for the fiber equivalences. -/
lemma id_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (X : fiber actions p) :
    ((id L).inverseFiberIso p).hom.app X = 𝟙 _ := by
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app X)).mp
  rw [functor_map_inverseFiberIso_hom_app_comp_counit, id_fiberFunctorIso_hom_app]
  -- Rebuild the endpoints with the identity joint functor removed, so simp can match map_id.
  change 𝟙 _ ≫ (L.fiberEquivalence p).counit.app X =
    (L.fiberEquivalence p).functor.map (𝟙 ((L.fiberEquivalence p).inverse.obj X)) ≫
      (L.fiberEquivalence p).counit.app X
  simp

/-- Taking mates respects composition of the specified fiber comparisons. -/
@[reassoc]
lemma comp_inverseFiberIso_hom_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (X : fiber actions p) :
    ((φ.comp ψ).inverseFiberIso p).hom.app X =
      (ψ.jointFunctor p).map ((φ.inverseFiberIso p).hom.app X) ≫
        (ψ.inverseFiberIso p).hom.app X := by
  apply (L''.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L''.fiberEquivalence p).counit.app X)).mp
  calc
    _ = (ψ.fiberFunctorIso p).hom.app
          ((φ.jointFunctor p).obj ((L.fiberEquivalence p).inverse.obj X)) ≫
        (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj X) ≫
          (L.fiberEquivalence p).counit.app X := by
      rw [functor_map_inverseFiberIso_hom_app_comp_counit]
      exact (congrArg (· ≫ _) (comp_fiberFunctorIso_hom_app φ ψ p _)).trans
        (Category.assoc _ _ _)
    _ = _ := by
      erw [Functor.map_comp, Category.assoc,
        ψ.functor_map_inverseFiberIso_hom_app_comp_counit,
        (ψ.fiberFunctorIso p).hom.naturality_assoc,
        φ.functor_map_inverseFiberIso_hom_app_comp_counit]
      rfl

/-- The inverse-fiber comparison of the identity lift morphism is the identity. -/
@[simp]
lemma id_inverseFiberIso (L : EquivariantGroupoidLift Γ actions) (p : Γ) :
    (id L).inverseFiberIso p = Iso.refl (L.fiberEquivalence p).inverse := by
  ext X
  exact id_inverseFiberIso_hom_app L p X

/-- Inverse-fiber comparisons compose by whiskering the first comparison and then
applying the second. -/
@[simp]
lemma comp_inverseFiberIso (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ) :
    (φ.comp ψ).inverseFiberIso p =
      Functor.isoWhiskerRight (φ.inverseFiberIso p) (ψ.jointFunctor p) ≪≫
        ψ.inverseFiberIso p := by
  ext X
  exact comp_inverseFiberIso_hom_app φ ψ p X

/-- A morphism of lifts `φ : L ⟶ L'` identifies the transport functors of `L` and `L'` on the
prescribed fibers: `E_g = e_p⁻¹ ⋙ F (g, 1) ⋙ e_q` is isomorphic to
`E'_g = e'_p⁻¹ ⋙ F' (g, 1) ⋙ e'_q`, through the fiber isomorphism `φ_q ⋙ e'_q ≅ e_q`, the
naturality isomorphism `F (g, 1) ⋙ φ_q ≅ φ_p ⋙ F' (g, 1)` and `e_p⁻¹ ⋙ φ_p ≅ e'_p⁻¹`. -/
noncomputable def transportIso (φ : L.Hom L') {p q : Γ} (g : p ⟶ q) :
    L.transport g ≅ L'.transport g :=
  Functor.isoWhiskerLeft ((L.fiberEquivalence p).inverse ⋙ L.jointMap g)
      (φ.fiberFunctorIso q).symm ≪≫
    Functor.isoWhiskerLeft (L.fiberEquivalence p).inverse
      (Functor.isoWhiskerRight (φ.jointMapIso g) (L'.fiberEquivalence q).functor) ≪≫
    Functor.isoWhiskerRight (φ.inverseFiberIso p) (L'.jointMap g ⋙ (L'.fiberEquivalence q).functor)

@[simp]
lemma transportIso_hom_app (φ : L.Hom L') {p q : Γ} (g : p ⟶ q) (X : fiber actions p) :
    (φ.transportIso g).hom.app X =
      (φ.fiberFunctorIso q).inv.app ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X)) ≫
        (L'.fiberEquivalence q).functor.map
          ((φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj X)) ≫
        (L'.fiberEquivalence q).functor.map
          ((L'.jointMap g).map ((φ.inverseFiberIso p).hom.app X)) := by
  simp [transportIso, transport]

/-- Normalizing the identity morphism gives the identity comparison on every transport functor. -/
@[simp]
lemma id_transportIso (L : EquivariantGroupoidLift Γ actions) {p q : Γ} (g : p ⟶ q) :
    (id L).transportIso g = Iso.refl (L.transport g) := by
  ext X
  simp only [transportIso_hom_app, id_fiberFunctorIso_inv_app, id_jointMapIso_hom_app,
    id_inverseFiberIso_hom_app]
  -- The expanded cells still carry the identity joint functor in their endpoint types.
  change 𝟙 _ ≫
      (L.fiberEquivalence q).functor.map
        (𝟙 ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X))) ≫
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map (𝟙 ((L.fiberEquivalence p).inverse.obj X))) = 𝟙 _
  simp

/-- Normalization preserves composition of lift morphisms on the actual transport cells. -/
@[simp]
lemma comp_transportIso (φ : L.Hom L') (ψ : L'.Hom L'') {p q : Γ} (g : p ⟶ q) :
    (φ.comp ψ).transportIso g = φ.transportIso g ≪≫ ψ.transportIso g := by
  ext X
  simp only [transportIso_hom_app, comp_fiberFunctorIso_inv_app,
    comp_jointMapIso_hom_app, comp_inverseFiberIso_hom_app,
    Iso.trans_hom, NatTrans.comp_app]
  -- Move the inverse fiber comparison past the joint naturality cell, then use
  -- naturality of the second joint cell to collect the first transport comparison.
  erw [Functor.map_comp, Category.assoc, Functor.map_comp, Functor.map_comp, Category.assoc]
  erw [← (ψ.fiberFunctorIso q).inv.naturality_assoc]
  erw [← Functor.map_comp_assoc]
  erw [← (ψ.jointMapIso g).hom.naturality]
  erw [Functor.map_comp, Category.assoc, ← (ψ.fiberFunctorIso q).inv.naturality_assoc]
  erw [Category.assoc, Category.assoc]
  rfl

namespace Hom₂

variable {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ)

/-- Compatibility of a modification with the prescribed fiber comparison, on objects. -/
@[reassoc]
lemma map_app_comp_fiberFunctorIso_hom_app (p : Γ) (Y : L.jointFiber p) :
    (L'.fiberEquivalence p).functor.map
        ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y) ≫
      (ψ.fiberFunctorIso p).hom.app Y = (φ.fiberFunctorIso p).hom.app Y := by
  -- Give restricted components their joint-fiber endpoints before simplifying in Cat.
  let F : L.jointFiber p ⟶ L'.jointFiber p := φ.joint.app ⟨(p, SingleObj.star H)⟩
  let G : L.jointFiber p ⟶ L'.jointFiber p := ψ.joint.app ⟨(p, SingleObj.star H)⟩
  let E' : L'.jointFiber p ⟶ fiber actions p := (L'.comparison p).app ⟨SingleObj.star H⟩
  let E : L.jointFiber p ⟶ fiber actions p := (L.comparison p).app ⟨SingleObj.star H⟩
  let a : F ⟶ G := Θ.joint.as.app ⟨(p, SingleObj.star H)⟩
  let b : G ≫ E' ⟶ E := (ψ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
  let c : F ≫ E' ⟶ E := (φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
  have h : a ▷ E' ≫ b = c := Θ.comm p ⟨SingleObj.star H⟩
  have h' := congrArg (fun m => m.toNatTrans.app Y) h
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app] at h'
  simp only [fiberFunctorIso_hom_app]
  exact h'

/-- Naturality of the joint modification along a parameter arrow, on objects. -/
@[reassoc]
lemma app_comp_jointMapIso_hom_app {p q : Γ} (g : p ⟶ q) (Y : L.jointFiber p) :
    (Θ.joint.as.app ⟨(q, SingleObj.star H)⟩).toNatTrans.app ((L.jointMap g).obj Y) ≫
        (ψ.jointMapIso g).hom.app Y =
      (φ.jointMapIso g).hom.app Y ≫ (L'.jointMap g).map
        ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y) := by
  have h := congrArg (fun m => m.toNatTrans.app Y)
    (Θ.joint.as.naturality (g ×ₘ 𝟙 (SingleObj.star H)).toLoc)
  -- These whiskerings take place in Cat; their components are the underlying natural maps.
  erw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
    Cat.whiskerRight_app] at h
  simpa only [jointMapIso_hom_app] using h

/-- The comparison of chosen inverse fibers is compatible with a modification. -/
@[reassoc]
lemma app_comp_inverseFiberIso_hom_app (p : Γ) (X : fiber actions p) :
    (Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj X) ≫ (ψ.inverseFiberIso p).hom.app X =
      (φ.inverseFiberIso p).hom.app X := by
  apply (L'.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L'.fiberEquivalence p).counit.app X)).mp
  rw [Functor.map_comp, Category.assoc,
    functor_map_inverseFiberIso_hom_app_comp_counit,
    functor_map_inverseFiberIso_hom_app_comp_counit,
    Θ.map_app_comp_fiberFunctorIso_hom_app_assoc]

include Θ in
/-- Compatible modifications give the same normalized comparison on each transport functor.
This does not identify the original joint transformations. -/
lemma transportIso_eq {p q : Γ} (g : p ⟶ q) : φ.transportIso g = ψ.transportIso g := by
  ext X
  have hf (Y : L.jointFiber q) :
      (φ.fiberFunctorIso q).inv.app Y ≫
        (L'.fiberEquivalence q).functor.map
          ((Θ.joint.as.app ⟨(q, SingleObj.star H)⟩).toNatTrans.app Y) =
        (ψ.fiberFunctorIso q).inv.app Y := by
    exact (Iso.inv_comp_eq ((φ.fiberFunctorIso q).app Y)).mpr
      ((Iso.eq_comp_inv ((ψ.fiberFunctorIso q).app Y)).mpr
        (Θ.map_app_comp_fiberFunctorIso_hom_app q Y))
  simp only [transportIso_hom_app]
  rw [← Θ.app_comp_inverseFiberIso_hom_app]
  simp only [Functor.map_comp]
  erw [← Functor.map_comp_assoc, ← Θ.app_comp_jointMapIso_hom_app,
    Functor.map_comp, ← Category.assoc, ← Category.assoc, hf]
  exact Category.assoc _ _ _

end Hom₂

end Hom

end TauCeti.EquivariantGroupoidLift
