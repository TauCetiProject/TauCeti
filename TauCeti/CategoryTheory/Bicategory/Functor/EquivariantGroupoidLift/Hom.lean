/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

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

/-- The isomorphism `e_p⁻¹ ⋙ φ_p ≅ e'_p⁻¹` between inverse fiber comparisons, obtained from the
fiber isomorphism `φ_p ⋙ e'_p ≅ e_p`. -/
noncomputable def inverseFiberIso (φ : L.Hom L') (p : Γ) :
    (L.fiberEquivalence p).inverse ⋙ φ.jointFunctor p ≅ (L'.fiberEquivalence p).inverse :=
  Iso.inverseCompIso (Iso.isoCompInverse (φ.fiberFunctorIso p))

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

end Hom

end TauCeti.EquivariantGroupoidLift
