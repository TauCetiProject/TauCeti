/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Equivariant groupoid lifts of categorical group actions

Let `Γ` be a category (in applications a groupoid of parameters) and `H` a monoid, and suppose
that for each `p : Γ` we are given a categorical action of `H` on a category `C p`, presented as
a pseudofunctor `actions p : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat`. A coherent equivariant
transport of these actions along `Γ` is a pseudofunctor

`F : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat`

together with, for each `p`, a strong transformation from the restriction of `F` along
`Prod.sectR p (SingleObj H)` to `actions p` whose component is an equivalence of categories.
This fixes the fiber categories and their `H`-actions up to equivariant equivalence, while the
arrows of `Γ` (including its automorphisms) act through `F`.

From such a lift we extract the transport functors on the prescribed fibers,
`E_g = e_p⁻¹ ⋙ F (g, 1) ⋙ e_q`, where `e_p : F (p, ⋆) ≌ C p` is the fiber comparison, together
with the unit isomorphisms `E_(𝟙 p) ≅ 𝟭`, the composition isomorphisms
`E_g ⋙ E_h ≅ E_(g ≫ h)` and the commuting isomorphisms `T_a ⋙ E_g ≅ E_g ⋙ T_a` with the
actions. The composition isomorphisms are associative and unital, and for an isomorphism `g`
of `Γ` (so for every arrow when `Γ` is a groupoid) `E_g` is an equivalence with inverse
`E_(g⁻¹)`. The commuting isomorphisms satisfy the mixed coherence conditions: they are
compatible with the unit and composition isomorphisms of transport along `Γ`, and with the unit
and composition comparisons `T_1 ≅ 𝟭` and `T_ab ≅ T_a ⋙ T_b` of the actions along `H`.
So transport is a pseudofunctor `LocallyDiscrete Γ ⥤ᵖ Cat`, and in particular the endomorphism
monoid `End p` of each object acts on the fiber `C p` by transport, coherently, through these
unit and composition isomorphisms.

The composition order follows `Γ × SingleObj H`: in `SingleObj H` the composite `a ≫ b` is the
product `b * a`, so the commuting isomorphisms compare the two factorizations
`(𝟙 p, a) ≫ (g, 1) = (g, a) = (g, 1) ≫ (𝟙 q, a)` of the arrow `(g, a)`.

## Main declarations

* `TauCeti.EquivariantGroupoidLift`: the type of coherent equivariant lifts of a family of
  categorical actions along `Γ`;
* `TauCeti.EquivariantGroupoidLift.transport`: the transport functor `E_g` between prescribed
  fibers;
* `TauCeti.EquivariantGroupoidLift.transportId`, `transportComp`: its unit and composition
  isomorphisms, which satisfy `transportComp_associativity`, `transportComp_left_unitality` and
  `transportComp_right_unitality`;
* `TauCeti.EquivariantGroupoidLift.transportCommIso`: the isomorphisms
  `T_a ⋙ E_g ≅ E_g ⋙ T_a` commuting transport with the actions;
* `TauCeti.EquivariantGroupoidLift.transportCommIso_comp`, `transportCommIso_id`,
  `transportCommIso_actComp`, `transportCommIso_actId`: the mixed coherence of the commuting
  isomorphisms with the unit and composition isomorphisms along `Γ` and along `H`;
* `TauCeti.EquivariantGroupoidLift.transportEquivalence`: for an isomorphism `g : p ≅ q`, the
  equivalence `C p ≌ C q` with functor `E_g` and inverse `E_(g⁻¹)`;
* `TauCeti.EquivariantGroupoidLift.transportPseudofunctor`: the transport functors, with their
  unit and composition isomorphisms, as a pseudofunctor `LocallyDiscrete Γ ⥤ᵖ Cat`;
* `TauCeti.EquivariantGroupoidLift.endAction`: the action of the endomorphism monoid `End p` on
  `C p` by the transport functors, as a pseudofunctor `LocallyDiscrete (SingleObj (End p)) ⥤ᵖ Cat`
  restricted from `transportPseudofunctor`.
  When `Γ` is a groupoid this is the action of the automorphism group of `p` on its fiber, so a
  lift retains the isotropy of `Γ`.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): the families of local categories over
  the groupoid of local Langlands parameters, with their loop group actions.
* Edward Frenkel and Dennis Gaitsgory, [Local geometric Langlands correspondence and affine
  Kac–Moody algebras](https://arxiv.org/abs/math/0508382).
-/

public section

universe w v u₂ v₁ u₁

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]

/-- The restriction of a pseudofunctor `F` out of `LocallyDiscrete (Γ × SingleObj H)` to the
fiber `{p} × SingleObj H`, that is, its composite with `Prod.sectR p (SingleObj H)`. Its value
at the unique object is `F.obj ⟨(p, ⋆)⟩` and its value at `a : H` is `F.map (𝟙 p, a)`. -/
abbrev restrictFiber {B : Type*} [Bicategory B] (F : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ B)
    (p : Γ) : LocallyDiscrete (SingleObj H) ⥤ᵖ B :=
  (Prod.sectR p (SingleObj H)).toPseudofunctor.comp F

end CategoryTheory.Pseudofunctor

namespace TauCeti

open CategoryTheory Bicategory CategoryTheory.Prod

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]

variable (Γ) in
/-- A coherent equivariant lift along `Γ` of a family `actions` of categorical actions of `H`.
It consists of a pseudofunctor `joint : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat` and, for each
`p : Γ`, a strong transformation from the restriction of `joint` to `{p} × SingleObj H` to the
prescribed action `actions p`, whose component at the unique object is an equivalence of
categories. -/
structure EquivariantGroupoidLift (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
    where
  /-- The joint pseudofunctor out of `LocallyDiscrete (Γ × SingleObj H)`. -/
  joint : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat.{v, w}
  /-- The comparison of the restriction of `joint` to the fiber at `p` with `actions p`. -/
  comparison (p : Γ) : Pseudofunctor.StrongTrans (joint.restrictFiber p) (actions p)
  /-- The component of each fiber comparison is an equivalence of categories. -/
  isEquivalence_comparison (p : Γ) :
    ((comparison p).app ⟨SingleObj.star H⟩).toFunctor.IsEquivalence

namespace EquivariantGroupoidLift

variable {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (L : EquivariantGroupoidLift Γ actions)

/-- The prescribed fiber category at `p`, the value of `actions p` at the unique object. -/
abbrev fiber (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (p : Γ) : Cat.{v, w} :=
  (actions p).obj ⟨SingleObj.star H⟩

/-- The value `F (p, ⋆)` of the joint pseudofunctor over `p`. -/
abbrev jointFiber (p : Γ) : Cat.{v, w} :=
  L.joint.obj ⟨(p, SingleObj.star H)⟩

/-- The functor `F (g, 1) : F (p, ⋆) ⥤ F (q, ⋆)` of the joint pseudofunctor at an arrow `g` of
`Γ`, paired with the identity of `SingleObj H`. -/
abbrev jointMap {p q : Γ} (g : p ⟶ q) : L.jointFiber p ⥤ L.jointFiber q :=
  (L.joint.map (g ×ₘ 𝟙 (SingleObj.star H)).toLoc).toFunctor

/-- The functor `F (𝟙 p, a) : F (p, ⋆) ⥤ F (p, ⋆)` of the joint pseudofunctor at `a : H`. -/
abbrev jointAct (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H) :
    L.jointFiber p ⥤ L.jointFiber p :=
  (L.joint.map (𝟙 p ×ₘ a).toLoc).toFunctor

/-- The action functor `T_a : C p ⥤ C p` of `a : H` on the prescribed fiber. -/
abbrev act (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) : fiber actions p ⥤ fiber actions p :=
  ((actions p).map a.toLoc).toFunctor

/-- The equivalence `e_p : F (p, ⋆) ≌ C p` given by the fiber comparison at `p`. -/
@[expose] noncomputable def fiberEquivalence (p : Γ) : L.jointFiber p ≌ fiber actions p :=
  letI := L.isEquivalence_comparison p
  ((L.comparison p).app ⟨SingleObj.star H⟩).toFunctor.asEquivalence

lemma fiberEquivalence_functor (p : Γ) :
    (L.fiberEquivalence p).functor = ((L.comparison p).app ⟨SingleObj.star H⟩).toFunctor :=
  rfl

/-- The unit comparison `F (𝟙 p, 1) ≅ 𝟭` of the joint pseudofunctor. -/
noncomputable def jointMapId (p : Γ) : L.jointMap (𝟙 p) ≅ 𝟭 (L.jointFiber p) :=
  Cat.Hom.toNatIso (L.joint.mapId' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc)

lemma jointMapId_hom_app (p : Γ) (Y : L.jointFiber p) :
    (L.jointMapId p).hom.app Y =
      (L.joint.mapId' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc).hom.toNatTrans.app Y := by
  rw [jointMapId]
  rfl

lemma jointMapId_inv_app (p : Γ) (Y : L.jointFiber p) :
    (L.jointMapId p).inv.app Y =
      (L.joint.mapId' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc).inv.toNatTrans.app Y := by
  rw [jointMapId]
  rfl

/-- The composition comparison `F (gh, 1) ≅ F (g, 1) ⋙ F (h, 1)` of the joint pseudofunctor,
for `g ≫ h = gh`. -/
noncomputable def jointMapComp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh := by cat_disch) : L.jointMap gh ≅ L.jointMap g ⋙ L.jointMap h :=
  Cat.Hom.toNatIso (L.joint.mapComp' (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc, hgh]))

lemma jointMapComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh)
    (Y : L.jointFiber p) :
    (L.jointMapComp g h gh hgh).hom.app Y =
      (L.joint.mapComp' (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (by simp [← Quiver.Hom.comp_toLoc, hgh])).hom.toNatTrans.app Y := by
  rw [jointMapComp]
  rfl

lemma jointMapComp_inv_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh)
    (Y : L.jointFiber p) :
    (L.jointMapComp g h gh hgh).inv.app Y =
      (L.joint.mapComp' (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (by simp [← Quiver.Hom.comp_toLoc, hgh])).inv.toNatTrans.app Y := by
  rw [jointMapComp]
  rfl

/-- The naturality isomorphism `F (𝟙 p, a) ⋙ e_p ≅ e_p ⋙ T_a` of the fiber comparison at
`a : H`. -/
noncomputable def comparisonNaturality (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H) :
    L.jointAct p a ⋙ (L.fiberEquivalence p).functor ≅
      (L.fiberEquivalence p).functor ⋙ act actions p a :=
  Cat.Hom.toNatIso ((L.comparison p).naturality a.toLoc)

lemma comparisonNaturality_hom_app (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.comparisonNaturality p a).hom.app Y =
      ((L.comparison p).naturality a.toLoc).hom.toNatTrans.app Y := by
  rw [comparisonNaturality]
  rfl

lemma comparisonNaturality_inv_app (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.comparisonNaturality p a).inv.app Y =
      ((L.comparison p).naturality a.toLoc).inv.toNatTrans.app Y := by
  rw [comparisonNaturality]
  rfl

/-- The joint functors `F (𝟙 p, a)` and `F (g, 1)` commute up to the isomorphism comparing the
two factorizations `(𝟙 p, a) ≫ (g, 1) = (g, a) = (g, 1) ≫ (𝟙 q, a)` of `(g, a)`. -/
noncomputable def jointActCommIso {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H) :
    L.jointAct p a ⋙ L.jointMap g ≅ L.jointMap g ⋙ L.jointAct q a :=
  Cat.Hom.toNatIso (L.joint.isoMapOfCommSq
    (⟨by simp⟩ : CommSq (𝟙 p ×ₘ a) (g ×ₘ 𝟙 (SingleObj.star H)) (g ×ₘ 𝟙 (SingleObj.star H))
      (𝟙 q ×ₘ a)).toLoc)

@[simp]
lemma jointActCommIso_hom_app {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.jointActCommIso g a).hom.app Y =
      (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
          (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app Y ≫
        (L.joint.mapComp' (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ a).toLoc (g ×ₘ a).toLoc
          (by simp [← Quiver.Hom.comp_toLoc])).hom.toNatTrans.app Y := by
  rw [jointActCommIso, Pseudofunctor.isoMapOfCommSq_eq _ _ (g ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc])]
  rfl

@[simp]
lemma jointActCommIso_inv_app {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.jointActCommIso g a).inv.app Y =
      (L.joint.mapComp' (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ a).toLoc (g ×ₘ a).toLoc
          (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app Y ≫
        (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
          (by simp [← Quiver.Hom.comp_toLoc])).hom.toNatTrans.app Y := by
  rw [jointActCommIso, Pseudofunctor.isoMapOfCommSq_eq _ _ (g ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc])]
  rfl

/-- The transport functor `E_g = e_p⁻¹ ⋙ F (g, 1) ⋙ e_q : C p ⥤ C q` of an arrow `g : p ⟶ q`,
expressed on the prescribed fibers. -/
@[expose] noncomputable def transport {p q : Γ} (g : p ⟶ q) : fiber actions p ⥤ fiber actions q :=
  (L.fiberEquivalence p).inverse ⋙ L.jointMap g ⋙ (L.fiberEquivalence q).functor

lemma transport_def {p q : Γ} (g : p ⟶ q) :
    L.transport g = (L.fiberEquivalence p).inverse ⋙ L.jointMap g ⋙
      (L.fiberEquivalence q).functor :=
  rfl

@[simp]
lemma transport_obj {p q : Γ} (g : p ⟶ q) (X : fiber actions p) :
    (L.transport g).obj X =
      (L.fiberEquivalence q).functor.obj
        ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X)) :=
  rfl

@[simp]
lemma transport_map {p q : Γ} (g : p ⟶ q) {X Y : fiber actions p} (f : X ⟶ Y) :
    (L.transport g).map f =
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map f)) :=
  rfl

/-- The unit isomorphism `E_(𝟙 p) ≅ 𝟭`: the unit comparison of the joint pseudofunctor at
`(p, ⋆)`, followed by the counit of the fiber comparison. -/
noncomputable def transportId (p : Γ) : L.transport (𝟙 p) ≅ 𝟭 (fiber actions p) :=
  Functor.isoWhiskerLeft (L.fiberEquivalence p).inverse
      (Functor.isoWhiskerRight (L.jointMapId p) (L.fiberEquivalence p).functor ≪≫
        Functor.leftUnitor _) ≪≫
    (L.fiberEquivalence p).counitIso

@[simp]
lemma transportId_hom_app (p : Γ) (X : fiber actions p) :
    (L.transportId p).hom.app X =
      (L.fiberEquivalence p).functor.map
        ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj X)) ≫
        (L.fiberEquivalence p).counit.app X := by
  simp [transportId, transport]

@[simp]
lemma transportId_inv_app (p : Γ) (X : fiber actions p) :
    (L.transportId p).inv.app X =
      (L.fiberEquivalence p).counitInv.app X ≫ (L.fiberEquivalence p).functor.map
        ((L.jointMapId p).inv.app ((L.fiberEquivalence p).inverse.obj X)) := by
  simp [transportId, transport]

/-- The composition isomorphism `E_g ⋙ E_h ≅ E_gh` for `g ≫ h = gh`: the inverse unit of the
fiber comparison at `q`, followed by the composition comparison of the joint pseudofunctor. -/
noncomputable def transportComp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh := by cat_disch) : L.transport g ⋙ L.transport h ≅ L.transport gh :=
  Functor.isoWhiskerLeft ((L.fiberEquivalence p).inverse ⋙ L.jointMap g)
      (Functor.isoWhiskerRight (L.fiberEquivalence q).unitIso.symm
        (L.jointMap h ⋙ (L.fiberEquivalence r).functor)) ≪≫
    Functor.isoWhiskerLeft (L.fiberEquivalence p).inverse
      (Functor.isoWhiskerRight (L.jointMapComp g h gh hgh).symm (L.fiberEquivalence r).functor)

@[simp]
lemma transportComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) (X : fiber actions p) :
    (L.transportComp g h gh hgh).hom.app X =
      (L.fiberEquivalence r).functor.map ((L.jointMap h).map ((L.fiberEquivalence q).unitInv.app
          ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X))) ≫
        (L.jointMapComp g h gh hgh).inv.app ((L.fiberEquivalence p).inverse.obj X)) := by
  simp [transportComp, transport]

@[simp]
lemma transportComp_inv_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) (X : fiber actions p) :
    (L.transportComp g h gh hgh).inv.app X =
      (L.fiberEquivalence r).functor.map
        ((L.jointMapComp g h gh hgh).hom.app ((L.fiberEquivalence p).inverse.obj X) ≫
          (L.jointMap h).map ((L.fiberEquivalence q).unit.app
            ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X)))) := by
  simp [transportComp, transport]

/-- Left unitality of the composition comparisons of the joint pseudofunctor along `Γ`. -/
lemma jointMapComp_id_comp_inv_app {p q : Γ} (g : p ⟶ q) (hg : 𝟙 p ≫ g = g)
    (Y : L.jointFiber p) :
    (L.jointMapComp (𝟙 p) g g hg).inv.app Y = (L.jointMap g).map ((L.jointMapId p).hom.app Y) := by
  have := L.joint.mapComp'_id_comp_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc Y
  simp only [jointMapComp, jointMapId, ← prod_id, Quiver.Hom.id_toLoc,
    Pseudofunctor.mapId'_eq_mapId] at this ⊢
  exact this

/-- Right unitality of the composition comparisons of the joint pseudofunctor along `Γ`. -/
lemma jointMapComp_comp_id_inv_app {p q : Γ} (g : p ⟶ q) (hg : g ≫ 𝟙 q = g)
    (Y : L.jointFiber p) :
    (L.jointMapComp g (𝟙 q) g hg).inv.app Y = (L.jointMapId q).hom.app ((L.jointMap g).obj Y) := by
  have := L.joint.mapComp'_comp_id_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc Y
  simp only [jointMapComp, jointMapId, ← prod_id, Quiver.Hom.id_toLoc,
    Pseudofunctor.mapId'_eq_mapId] at this ⊢
  exact this

/-- Associativity of the composition comparisons of the joint pseudofunctor along `Γ`. -/
lemma jointMapComp_inv_associativity {p q r s : Γ} (f : p ⟶ q) (g : q ⟶ r) (h : r ⟶ s)
    (fg : p ⟶ r) (gh : q ⟶ s) (fgh : p ⟶ s) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (Y : L.jointFiber p) :
    (L.jointMap h).map ((L.jointMapComp f g fg hfg).inv.app Y) ≫
        (L.jointMapComp fg h fgh hfgh).inv.app Y =
      (L.jointMapComp g h gh hgh).inv.app ((L.jointMap f).obj Y) ≫
        (L.jointMapComp f gh fgh (by rw [← hgh, ← Category.assoc, hfg, hfgh])).inv.app Y := by
  have := L.joint.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
    (f ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (fg ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc (fgh ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc, hfg])
    (by simp [← Quiver.Hom.comp_toLoc, hgh])
    (by simp [← Quiver.Hom.comp_toLoc, hfgh]) Y
  simpa [jointMapComp] using this

/-- Associativity of the composition isomorphisms of transport: the two ways of comparing
`E_f ⋙ E_g ⋙ E_h` with `E_fgh` agree. -/
lemma transportComp_associativity {p q r s : Γ} (f : p ⟶ q) (g : q ⟶ r) (h : r ⟶ s)
    (fg : p ⟶ r) (gh : q ⟶ s) (fgh : p ⟶ s) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (X : fiber actions p) :
    (L.transport h).map ((L.transportComp f g fg hfg).hom.app X) ≫
        (L.transportComp fg h fgh hfgh).hom.app X =
      (L.transportComp g h gh hgh).hom.app ((L.transport f).obj X) ≫
        (L.transportComp f gh fgh (by rw [← hgh, ← Category.assoc, hfg, hfgh])).hom.app X := by
  simp only [transportComp_hom_app, transport, Functor.comp_map, Functor.comp_obj,
    ← Functor.map_comp]
  congr 1
  have := (L.fiberEquivalence r).unitInv_naturality
    ((L.jointMap g).map ((L.fiberEquivalence q).unitInv.app
      ((L.jointMap f).obj ((L.fiberEquivalence p).inverse.obj X))) ≫
      (L.jointMapComp f g fg hfg).inv.app ((L.fiberEquivalence p).inverse.obj X))
  rw [← Functor.map_comp_assoc]
  -- `rw [this]` fails to locate the pattern, whose objects match those of the goal only up to
  -- unfolding the fiber abbreviations, so the rewrite is performed through `congrArg`.
  refine (congrArg (· ≫ _) (congrArg (L.jointMap h).map this)).trans ?_
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [L.jointMapComp_inv_associativity f g h fg gh fgh hfg hgh hfgh]
  exact (L.jointMapComp g h gh hgh).inv.naturality_assoc _ _

/-- Left unitality of the composition isomorphisms of transport: the compositor
`E_(𝟙 p) ⋙ E_g ≅ E_g` is `E_g` applied to the unit isomorphism `E_(𝟙 p) ≅ 𝟭`. -/
lemma transportComp_left_unitality {p q : Γ} (g : p ⟶ q) (hg : 𝟙 p ≫ g = g)
    (X : fiber actions p) :
    (L.transportComp (𝟙 p) g g hg).hom.app X =
      (L.transport g).map ((L.transportId p).hom.app X) := by
  simp only [transportComp_hom_app, transportId_hom_app, jointMapComp_id_comp_inv_app, transport,
    Functor.comp_map, ← Functor.map_comp]
  congr 2
  rw [Functor.map_comp, Equivalence.inv_fun_map]
  simp

/-- Right unitality of the composition isomorphisms of transport: the compositor
`E_g ⋙ E_(𝟙 q) ≅ E_g` is the unit isomorphism `E_(𝟙 q) ≅ 𝟭` at `E_g`. -/
lemma transportComp_right_unitality {p q : Γ} (g : p ⟶ q) (hg : g ≫ 𝟙 q = g)
    (X : fiber actions p) :
    (L.transportComp g (𝟙 q) g hg).hom.app X =
      (L.transportId q).hom.app ((L.transport g).obj X) := by
  simp only [transportComp_hom_app, transportId_hom_app, jointMapComp_comp_id_inv_app, transport,
    Functor.comp_obj]
  -- As in `transportComp_associativity`, `rw` does not locate the naturality square of the
  -- unit comparison, so it is applied through `congrArg`.
  refine (congrArg (L.fiberEquivalence q).functor.map ((L.jointMapId q).hom.naturality _)).trans ?_
  rw [Functor.map_comp, Equivalence.counit_app_functor]
  simp

/-- For an isomorphism `g : p ≅ q` of `Γ`, the transport functor `E_g` is an equivalence
`C p ≌ C q` with inverse `E_(g⁻¹)`; its unit and counit are built from `transportId` and
`transportComp`. -/
@[expose] noncomputable def transportEquivalence {p q : Γ} (g : p ≅ q) :
    fiber actions p ≌ fiber actions q where
  functor := L.transport g.hom
  inverse := L.transport g.inv
  unitIso := (L.transportId p).symm ≪≫ (L.transportComp g.hom g.inv (𝟙 p)).symm
  counitIso := L.transportComp g.inv g.hom (𝟙 q) ≪≫ L.transportId q
  functor_unitIso_comp X := by
    -- The triangle identity follows from the associativity and unitality of `transportComp`.
    have h := L.transportComp_associativity g.hom g.inv g.hom (𝟙 p) (𝟙 q) g.hom
      (by simp) (by simp) (by simp) X
    rw [L.transportComp_left_unitality, L.transportComp_right_unitality] at h
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, ← h,
      ← Functor.map_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    exact (L.transport g.hom).map_id X

@[simp]
lemma transportEquivalence_unitIso {p q : Γ} (g : p ≅ q) :
    (L.transportEquivalence g).unitIso =
      (L.transportId p).symm ≪≫ (L.transportComp g.hom g.inv (𝟙 p)).symm :=
  rfl

@[simp]
lemma transportEquivalence_counitIso {p q : Γ} (g : p ≅ q) :
    (L.transportEquivalence g).counitIso = L.transportComp g.inv g.hom (𝟙 q) ≪≫ L.transportId q :=
  rfl

@[simp]
lemma transportEquivalence_functor {p q : Γ} (g : p ≅ q) :
    (L.transportEquivalence g).functor = L.transport g.hom := by
  rfl

@[simp]
lemma transportEquivalence_inverse {p q : Γ} (g : p ≅ q) :
    (L.transportEquivalence g).inverse = L.transport g.inv := by
  rfl

/-- The transport functor along an isomorphism of `Γ` is an equivalence. In particular, when
`Γ` is a groupoid every transport functor is an equivalence. -/
instance isEquivalence_transport {p q : Γ} (g : p ⟶ q) [IsIso g] : (L.transport g).IsEquivalence :=
  (L.transportEquivalence (asIso g)).isEquivalence_functor

/-- The inverse `e_p⁻¹` of the fiber comparison commutes with the actions:
`T_a ⋙ e_p⁻¹ ≅ e_p⁻¹ ⋙ F (𝟙 p, a)`. It is the naturality isomorphism of the comparison at `a`,
conjugated by the equivalence `e_p`. -/
noncomputable def actInverseIso (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H) :
    act actions p a ⋙ (L.fiberEquivalence p).inverse ≅
      (L.fiberEquivalence p).inverse ⋙ L.jointAct p a :=
  Iso.isoInverseComp (Iso.compInverseIso (L.comparisonNaturality p a).symm)

@[simp]
lemma actInverseIso_hom_app (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.actInverseIso p a).hom.app X =
      (L.fiberEquivalence p).inverse.map ((act actions p a).map
          ((L.fiberEquivalence p).counitInv.app X) ≫
        (L.comparisonNaturality p a).inv.app ((L.fiberEquivalence p).inverse.obj X)) ≫
      (L.fiberEquivalence p).unitInv.app
        ((L.jointAct p a).obj ((L.fiberEquivalence p).inverse.obj X)) := by
  simp [actInverseIso, act]

@[simp]
lemma actInverseIso_inv_app (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.actInverseIso p a).inv.app X =
      (L.fiberEquivalence p).unit.app
          ((L.jointAct p a).obj ((L.fiberEquivalence p).inverse.obj X)) ≫
        (L.fiberEquivalence p).inverse.map
          ((L.comparisonNaturality p a).hom.app ((L.fiberEquivalence p).inverse.obj X) ≫
            (act actions p a).map ((L.fiberEquivalence p).counit.app X)) := by
  simp [actInverseIso, act]

/-- Transport commutes with the prescribed actions: `T_a ⋙ E_g ≅ E_g ⋙ T_a`. It combines the
naturality of the fiber comparisons at `p` and `q` with `jointActCommIso`. -/
noncomputable def transportCommIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) :
    act actions p a ⋙ L.transport g ≅ L.transport g ⋙ act actions q a :=
  Functor.isoWhiskerRight (L.actInverseIso p a) (L.jointMap g ⋙ (L.fiberEquivalence q).functor) ≪≫
    Functor.isoWhiskerLeft (L.fiberEquivalence p).inverse
      (Functor.isoWhiskerRight (L.jointActCommIso g a) (L.fiberEquivalence q).functor ≪≫
        Functor.isoWhiskerLeft (L.jointMap g) (L.comparisonNaturality q a))

@[simp]
lemma transportCommIso_hom_app {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.transportCommIso g a).hom.app X =
      (L.fiberEquivalence q).functor.map ((L.jointMap g).map ((L.actInverseIso p a).hom.app X) ≫
          (L.jointActCommIso g a).hom.app ((L.fiberEquivalence p).inverse.obj X)) ≫
        (L.comparisonNaturality q a).hom.app
          ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X)) := by
  simp [transportCommIso, transport]

@[simp]
lemma transportCommIso_inv_app {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.transportCommIso g a).inv.app X =
      (L.comparisonNaturality q a).inv.app
          ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X)) ≫
        (L.fiberEquivalence q).functor.map
          ((L.jointActCommIso g a).inv.app ((L.fiberEquivalence p).inverse.obj X) ≫
            (L.jointMap g).map ((L.actInverseIso p a).inv.app X)) := by
  simp [transportCommIso, transport]

/-! ### Mixed coherence

The commuting isomorphisms `transportCommIso` are compatible with the unit and composition
isomorphisms of transport along `Γ` and with the unit and composition comparisons of the
prescribed actions along `H`. Each statement is first proved for the joint functors, where it
compares two factorizations of an arrow of `Γ × SingleObj H`, and then transported to the
prescribed fibers through the fiber comparisons.

Together, `transportCommIso_actComp` and `transportCommIso_actId` say that `E_g`, with the
commuting isomorphisms `transportCommIso g`, is compatible with the unit and composition
comparisons of the actions, while `transportCommIso_comp` and `transportCommIso_id` say that
the composition and unit isomorphisms of transport commute with the actions. -/

/-- The composition comparison `F (𝟙 p, ab) ≅ F (𝟙 p, a) ⋙ F (𝟙 p, b)` of the joint pseudofunctor
along `H`, for `a ≫ b = ab` in `SingleObj H`. -/
noncomputable def jointActComp (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab := by cat_disch) : L.jointAct p ab ≅ L.jointAct p a ⋙ L.jointAct p b :=
  Cat.Hom.toNatIso (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (𝟙 p ×ₘ ab).toLoc
    (by simp [← Quiver.Hom.comp_toLoc, hab]))

lemma jointActComp_hom_app (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (Y : L.jointFiber p) :
    (L.jointActComp p a b ab hab).hom.app Y =
      (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (𝟙 p ×ₘ ab).toLoc
        (by simp [← Quiver.Hom.comp_toLoc, hab])).hom.toNatTrans.app Y := by
  rw [jointActComp]
  rfl

lemma jointActComp_inv_app (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (Y : L.jointFiber p) :
    (L.jointActComp p a b ab hab).inv.app Y =
      (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (𝟙 p ×ₘ ab).toLoc
        (by simp [← Quiver.Hom.comp_toLoc, hab])).inv.toNatTrans.app Y := by
  rw [jointActComp]
  rfl

/-- The composition comparison `T_ab ≅ T_a ⋙ T_b` of the prescribed action at `p`, for
`a ≫ b = ab` in `SingleObj H`. -/
noncomputable def actComp (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (p : Γ)
    (a b ab : SingleObj.star H ⟶ SingleObj.star H) (hab : a ≫ b = ab := by cat_disch) :
    act actions p ab ≅ act actions p a ⋙ act actions p b :=
  Cat.Hom.toNatIso ((actions p).mapComp' a.toLoc b.toLoc ab.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, hab]))

omit [Category.{v₁, u₁} Γ] in
lemma actComp_hom_app (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (X : fiber actions p) :
    (actComp actions p a b ab hab).hom.app X =
      ((actions p).mapComp' a.toLoc b.toLoc ab.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, hab])).hom.toNatTrans.app X := by
  rw [actComp]
  rfl

omit [Category.{v₁, u₁} Γ] in
lemma actComp_inv_app (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (X : fiber actions p) :
    (actComp actions p a b ab hab).inv.app X =
      ((actions p).mapComp' a.toLoc b.toLoc ab.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, hab])).inv.toNatTrans.app X := by
  rw [actComp]
  rfl

/-- The unit comparison `T_1 ≅ 𝟭` of the prescribed action at `p`. -/
noncomputable def actId (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (p : Γ) :
    act actions p (𝟙 (SingleObj.star H)) ≅ 𝟭 (fiber actions p) :=
  Cat.Hom.toNatIso ((actions p).mapId' (𝟙 (SingleObj.star H)).toLoc)

omit [Category.{v₁, u₁} Γ] in
lemma actId_hom_app (p : Γ) (X : fiber actions p) :
    (actId actions p).hom.app X =
      ((actions p).mapId' (𝟙 (SingleObj.star H)).toLoc).hom.toNatTrans.app X := by
  rw [actId]
  rfl

omit [Category.{v₁, u₁} Γ] in
lemma actId_inv_app (p : Γ) (X : fiber actions p) :
    (actId actions p).inv.app X =
      ((actions p).mapId' (𝟙 (SingleObj.star H)).toLoc).inv.toNatTrans.app X := by
  rw [actId]
  rfl

/-- Compatibility of the commuting isomorphisms of the joint functors with the composition
comparisons along `Γ`. -/
@[reassoc]
lemma jointActCommIso_comp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.jointMap h).map ((L.jointActCommIso g a).hom.app Y) ≫
        (L.jointActCommIso h a).hom.app ((L.jointMap g).obj Y) ≫
          (L.jointAct r a).map ((L.jointMapComp g h gh hgh).inv.app Y) =
      (L.jointMapComp g h gh hgh).inv.app ((L.jointAct p a).obj Y) ≫
        (L.jointActCommIso gh a).hom.app Y := by
  rw [← cancel_mono ((L.jointAct r a).map ((L.jointMapComp g h gh hgh).hom.app Y))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [jointActCommIso_hom_app, jointMapComp_inv_app, jointMapComp_hom_app,
    Functor.map_comp, Category.assoc, jointMap, jointAct]
  rw [← L.joint.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc (gh ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc, hgh])
    (by simp [← Quiver.Hom.comp_toLoc, ← hgh]),
    ← L.joint.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 r ×ₘ a).toLoc
    (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ a).toLoc (gh ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc, hgh]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc, ← hgh]),
    L.joint.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ a).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc (h ×ₘ a).toLoc (gh ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc, ← hgh])]
  simp

/-- Compatibility of the commuting isomorphisms of the joint functors with the composition
comparisons along `H`. -/
@[reassoc]
lemma jointActCommIso_actComp {p q : Γ} (g : p ⟶ q)
    (a b ab : SingleObj.star H ⟶ SingleObj.star H) (hab : a ≫ b = ab) (Y : L.jointFiber p) :
    (L.jointMap g).map ((L.jointActComp p a b ab hab).hom.app Y) ≫
        (L.jointActCommIso g b).hom.app ((L.jointAct p a).obj Y) ≫
          (L.jointAct q b).map ((L.jointActCommIso g a).hom.app Y) =
      (L.jointActCommIso g ab).hom.app Y ≫
        (L.jointActComp q a b ab hab).hom.app ((L.jointMap g).obj Y) := by
  simp only [jointActCommIso_hom_app, jointActComp_hom_app, Functor.map_comp, Category.assoc,
    jointMap, jointAct]
  rw [L.joint.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ a).toLoc (𝟙 q ×ₘ b).toLoc
    (g ×ₘ a).toLoc (𝟙 q ×ₘ ab).toLoc (g ×ₘ ab).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc, hab])
    (by simp [← Quiver.Hom.comp_toLoc]),
    ← L.joint.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc
    (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (𝟙 p ×ₘ ab).toLoc (g ×ₘ b).toLoc (g ×ₘ ab).toLoc
    (by simp [← Quiver.Hom.comp_toLoc, hab]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc]),
    L.joint.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ b).toLoc
    (g ×ₘ a).toLoc (g ×ₘ b).toLoc (g ×ₘ ab).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc, ← hab])]
  rw [← Functor.map_comp_assoc]
  simp

/-- Mixed unit coherence of the joint functors: the commuting isomorphism of `F (𝟙 p, 1)` with
`F (𝟙 p, a)` is induced by the unit comparison `F (𝟙 p, 1) ≅ 𝟭`. -/
@[reassoc]
lemma jointActCommIso_id (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.jointActCommIso (𝟙 p) a).hom.app Y ≫ (L.jointAct p a).map ((L.jointMapId p).hom.app Y) =
      (L.jointMapId p).hom.app ((L.jointAct p a).obj Y) := by
  simp only [jointActCommIso_hom_app, jointMapId_hom_app, jointAct, jointMap, ← prod_id,
    Quiver.Hom.id_toLoc, Pseudofunctor.mapId'_eq_mapId]
  simp [Pseudofunctor.mapComp'_comp_id_inv_app, Pseudofunctor.mapComp'_id_comp_hom_app,
    ← Functor.map_comp]

/-- Mixed unit coherence of the joint functors: the commuting isomorphism of `F (g, 1)` with
`F (𝟙, 1)` is induced by the unit comparisons `F (𝟙, 1) ≅ 𝟭` at `p` and `q`. -/
@[reassoc]
lemma jointActCommIso_actId {p q : Γ} (g : p ⟶ q) (Y : L.jointFiber p) :
    (L.jointActCommIso g (𝟙 (SingleObj.star H))).hom.app Y ≫
        (L.jointMapId q).hom.app ((L.jointMap g).obj Y) =
      (L.jointMap g).map ((L.jointMapId p).hom.app Y) := by
  simp only [jointActCommIso_hom_app, jointMapId_hom_app, jointAct, jointMap, ← prod_id,
    Quiver.Hom.id_toLoc, Pseudofunctor.mapId'_eq_mapId]
  simp [Pseudofunctor.mapComp'_comp_id_hom_app, Pseudofunctor.mapComp'_id_comp_inv_app]

/-- Compatibility of the naturality isomorphisms of the fiber comparison with the composition
comparisons along `H`: the composition axiom of the strong transformation `L.comparison p`. -/
@[reassoc]
lemma comparisonNaturality_actComp (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (Y : L.jointFiber p) :
    (L.comparisonNaturality p ab).hom.app Y ≫
        (actComp actions p a b ab hab).hom.app ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence p).functor.map ((L.jointActComp p a b ab hab).hom.app Y) ≫
        (L.comparisonNaturality p b).hom.app ((L.jointAct p a).obj Y) ≫
          (act actions p b).map ((L.comparisonNaturality p a).hom.app Y) := by
  subst hab
  have e₁ : (actions p).mapComp' a.toLoc b.toLoc (a ≫ b).toLoc =
      (actions p).mapComp a.toLoc b.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  -- The composition comparison of the restriction of the joint pseudofunctor is, by definition,
  -- the one appearing in `jointActComp`.
  have e₂ : L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (𝟙 p ×ₘ (a ≫ b)).toLoc
      (by simp [← Quiver.Hom.comp_toLoc]) = (L.joint.restrictFiber p).mapComp a.toLoc b.toLoc :=
    rfl
  simp only [comparisonNaturality_hom_app, actComp_hom_app, jointActComp_hom_app, e₁, e₂]
  -- Mathlib's component form of the composition axiom, with the composition comparison of
  -- `actions p` cancelled; it matches the goal since `(a ≫ b).toLoc = a.toLoc ≫ b.toLoc` and
  -- `L.jointFiber p = (L.joint.restrictFiber p).obj ⟨SingleObj.star H⟩` by definition.
  have key := congrArg (· ≫ ((actions p).mapComp a.toLoc b.toLoc).hom.toNatTrans.app _)
    (Pseudofunctor.StrongTrans.naturality_comp_hom_app (L.comparison p) a.toLoc b.toLoc Y)
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app, Cat.Hom.comp_toFunctor,
    Functor.comp_obj, Category.comp_id] at key
  exact key

/-- Compatibility of the naturality isomorphisms of the fiber comparison with the unit
comparisons: the unit axiom of the strong transformation `L.comparison p`. Here
`F (𝟙 p, 1) = L.jointAct p 1` has unit comparison `L.jointMapId p`. -/
@[reassoc]
lemma comparisonNaturality_actId (p : Γ) (Y : L.jointFiber p) :
    (L.comparisonNaturality p (𝟙 (SingleObj.star H))).hom.app Y ≫
        (actId actions p).hom.app ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence p).functor.map ((L.jointMapId p).hom.app Y) := by
  -- The unit comparisons of `actions p` and of the restriction of the joint pseudofunctor are,
  -- by definition, the ones appearing in `actId` and `jointMapId`.
  have e₁ : (actions p).mapId' (𝟙 (SingleObj.star H)).toLoc =
      (actions p).mapId ⟨SingleObj.star H⟩ :=
    Pseudofunctor.mapId'_eq_mapId _ _
  have e₂ : L.joint.mapId' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc =
      (L.joint.restrictFiber p).mapId ⟨SingleObj.star H⟩ :=
    rfl
  simp only [comparisonNaturality_hom_app, actId_hom_app, jointMapId_hom_app, e₁, e₂]
  -- Mathlib's component form of the unit axiom, with the unit comparison of `actions p`
  -- cancelled; it matches the goal since `(𝟙 (SingleObj.star H)).toLoc = 𝟙 ⟨SingleObj.star H⟩`
  -- by definition.
  have key := congrArg (· ≫ ((actions p).mapId ⟨SingleObj.star H⟩).hom.toNatTrans.app _)
    (Pseudofunctor.StrongTrans.naturality_id_hom_app (L.comparison p) ⟨SingleObj.star H⟩ Y)
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app] at key
  exact key.trans (Category.comp_id _)

/-- The image of `actInverseIso` under the fiber comparison, followed by its naturality
isomorphism, is the conjugate of the counit of the fiber comparison by the action. -/
@[reassoc]
lemma functor_map_actInverseIso_hom_app_comp (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.fiberEquivalence p).functor.map ((L.actInverseIso p a).hom.app X) ≫
        (L.comparisonNaturality p a).hom.app ((L.fiberEquivalence p).inverse.obj X) =
      (L.fiberEquivalence p).counit.app ((act actions p a).obj X) ≫
        (act actions p a).map ((L.fiberEquivalence p).counitInv.app X) := by
  simp [← Equivalence.counit_app_functor]

/-- `actInverseIso` at an object in the image of the fiber comparison is the inverse of the
naturality isomorphism, up to the unit of the fiber comparison. -/
@[reassoc]
lemma inverse_map_comparisonNaturality_hom_app_comp (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (L.fiberEquivalence p).inverse.map ((L.comparisonNaturality p a).hom.app Y) ≫
        (L.actInverseIso p a).hom.app ((L.fiberEquivalence p).functor.obj Y) ≫
          (L.jointAct p a).map ((L.fiberEquivalence p).unitInv.app Y) =
      (L.fiberEquivalence p).unitInv.app ((L.jointAct p a).obj Y) := by
  apply (L.fiberEquivalence p).functor.map_injective
  have nat := (L.comparisonNaturality p a).inv.naturality ((L.fiberEquivalence p).unitInv.app Y)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nat
  simp only [Functor.map_comp, actInverseIso_hom_app, Equivalence.fun_inv_map]
  simp only [Functor.comp_obj, Functor.id_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
    Equivalence.counitInv_functor_comp, Category.comp_id]
  rw [← nat, Equivalence.counitInv_app_functor, ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp [Equivalence.counit_app_functor]

/-- Compatibility of `actInverseIso` with the composition comparisons along `H`. -/
@[reassoc]
lemma actInverseIso_actComp (p : Γ) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (X : fiber actions p) :
    (L.fiberEquivalence p).inverse.map ((actComp actions p a b ab hab).hom.app X) ≫
        (L.actInverseIso p b).hom.app ((act actions p a).obj X) ≫
          (L.jointAct p b).map ((L.actInverseIso p a).hom.app X) =
      (L.actInverseIso p ab).hom.app X ≫
        (L.jointActComp p a b ab hab).hom.app ((L.fiberEquivalence p).inverse.obj X) := by
  apply (L.fiberEquivalence p).functor.map_injective
  rw [← cancel_mono ((L.comparisonNaturality p b).hom.app
      ((L.jointAct p a).obj ((L.fiberEquivalence p).inverse.obj X)) ≫
    (act actions p b).map ((L.comparisonNaturality p a).hom.app
      ((L.fiberEquivalence p).inverse.obj X)))]
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.comparisonNaturality_actComp, L.functor_map_actInverseIso_hom_app_comp_assoc]
  have nat := (L.comparisonNaturality p b).hom.naturality ((L.actInverseIso p a).hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nat
  rw [reassoc_of% nat, L.functor_map_actInverseIso_hom_app_comp_assoc, ← Functor.map_comp,
    L.functor_map_actInverseIso_hom_app_comp]
  simp only [Equivalence.fun_inv_map, Functor.id_obj, Functor.comp_obj, Category.assoc,
    Equivalence.counitIso_inv_hom_id_app_assoc, ← Functor.map_comp,
    Equivalence.counitIso_inv_hom_id_app_assoc]
  exact congrArg _ ((actComp actions p a b ab hab).hom.naturality _).symm

/-- Compatibility of `actInverseIso` with the unit comparisons. -/
@[reassoc]
lemma actInverseIso_actId (p : Γ) (X : fiber actions p) :
    (L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app X ≫
        (L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj X) =
      (L.fiberEquivalence p).inverse.map ((actId actions p).hom.app X) := by
  apply (L.fiberEquivalence p).functor.map_injective
  rw [Functor.map_comp, ← L.comparisonNaturality_actId,
    L.functor_map_actInverseIso_hom_app_comp_assoc, Equivalence.fun_inv_map]
  have := (actId actions p).hom.naturality ((L.fiberEquivalence p).counitInv.app X)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at this
  rw [this]
  dsimp only [Functor.id_obj]

/-- Mixed coherence of transport along `Γ`: the commuting isomorphism of `E_gh` with `T_a` is
the composite of those of `E_g` and `E_h`, up to the composition isomorphism
`E_g ⋙ E_h ≅ E_gh`. -/
@[reassoc]
lemma transportCommIso_comp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.transport h).map ((L.transportCommIso g a).hom.app X) ≫
        (L.transportCommIso h a).hom.app ((L.transport g).obj X) ≫
          (act actions r a).map ((L.transportComp g h gh hgh).hom.app X) =
      (L.transportComp g h gh hgh).hom.app ((act actions p a).obj X) ≫
        (L.transportCommIso gh a).hom.app X := by
  -- Unfold both sides into the fiber comparison at `r` applied to a composite in the joint fiber,
  -- followed by the naturality isomorphism of the comparison at `r`.
  have nat₁ := (L.comparisonNaturality r a).hom.naturality
    ((L.jointMap h).map ((L.fiberEquivalence q).unitInv.app
      ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X))) ≫
      (L.jointMapComp g h gh hgh).inv.app ((L.fiberEquivalence p).inverse.obj X))
  dsimp only [Functor.comp_map, Functor.comp_obj] at nat₁
  simp only [Functor.map_comp, Category.assoc] at nat₁
  simp only [transportCommIso_hom_app, transportComp_hom_app, transport_obj]
  dsimp only [Functor.comp_obj, transport_obj]
  simp only [transport_map, Functor.map_comp, Category.assoc]
  rw [← nat₁]
  repeat rw [← Functor.map_comp_assoc (L.fiberEquivalence r).functor]
  refine congrArg (fun f => (L.fiberEquivalence r).functor.map f ≫ _) ?_
  -- In the joint fiber, the fiber comparison at `q` cancels by
  -- `inverse_map_comparisonNaturality_hom_app_comp`, leaving `jointActCommIso_comp`.
  have nat₂ := (L.jointActCommIso h a).hom.naturality
    ((L.fiberEquivalence q).unitInv.app ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj X)))
  have nat₃ := (L.jointMapComp g h gh hgh).inv.naturality ((L.actInverseIso p a).hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nat₂ nat₃
  simp only [Category.assoc]
  rw [← reassoc_of% nat₂]
  repeat rw [← Functor.map_comp_assoc (L.jointMap h)]
  simp only [Category.assoc, L.inverse_map_comparisonNaturality_hom_app_comp,
    Equivalence.inv_fun_map, Equivalence.unitIso_hom_inv_id_app_assoc,
    Equivalence.unitIso_hom_inv_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [L.jointActCommIso_comp, reassoc_of% nat₃]

/-- Mixed coherence of transport along `H`: the commuting isomorphism of `E_g` with `T_ab`
is the composite of those with `T_a` and `T_b`, up to the composition comparisons
`T_ab ≅ T_a ⋙ T_b` of the prescribed actions at `p` and `q`. -/
@[reassoc]
lemma transportCommIso_actComp {p q : Γ} (g : p ⟶ q)
    (a b ab : SingleObj.star H ⟶ SingleObj.star H) (hab : a ≫ b = ab) (X : fiber actions p) :
    (L.transport g).map ((actComp actions p a b ab hab).hom.app X) ≫
        (L.transportCommIso g b).hom.app ((act actions p a).obj X) ≫
          (act actions q b).map ((L.transportCommIso g a).hom.app X) =
      (L.transportCommIso g ab).hom.app X ≫
        (actComp actions q a b ab hab).hom.app ((L.transport g).obj X) := by
  -- As in `transportCommIso_comp`, reduce to an identity in the joint fiber over `q`.
  have nat₁ := (L.comparisonNaturality q b).hom.naturality
    ((L.jointMap g).map ((L.actInverseIso p a).hom.app X) ≫
      (L.jointActCommIso g a).hom.app ((L.fiberEquivalence p).inverse.obj X))
  have nat₂ := (L.jointActCommIso g b).hom.naturality ((L.actInverseIso p a).hom.app X)
  dsimp only [Functor.comp_map] at nat₁ nat₂
  simp only [Functor.map_comp, Category.assoc] at nat₁
  simp only [transportCommIso_hom_app, transport_map, transport_obj]
  dsimp only [Functor.comp_obj, transport_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nat₁, L.comparisonNaturality_actComp]
  repeat rw [← Functor.map_comp_assoc (L.fiberEquivalence q).functor]
  refine congrArg (fun f => (L.fiberEquivalence q).functor.map f ≫ _) ?_
  -- In the joint fiber, `actInverseIso_actComp` and `jointActCommIso_actComp` apply.
  simp only [Category.assoc]
  rw [← reassoc_of% nat₂, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    L.actInverseIso_actComp, Functor.map_comp_assoc, L.jointActCommIso_actComp]

/-- Mixed unit coherence of transport: the commuting isomorphism of `E_(𝟙 p)` with `T_a` is
induced by the unit isomorphism `E_(𝟙 p) ≅ 𝟭`. -/
@[reassoc]
lemma transportCommIso_id (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (L.transportCommIso (𝟙 p) a).hom.app X ≫ (act actions p a).map ((L.transportId p).hom.app X) =
      (L.transportId p).hom.app ((act actions p a).obj X) := by
  have nat₁ := (L.comparisonNaturality p a).hom.naturality
    ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj X))
  have nat₂ := (L.jointMapId p).hom.naturality ((L.actInverseIso p a).hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at nat₁ nat₂
  simp only [transportCommIso_hom_app, transportId_hom_app]
  dsimp only [Functor.comp_obj, transport_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nat₁, ← Functor.map_comp_assoc (L.fiberEquivalence p).functor
    ((L.jointActCommIso (𝟙 p) a).hom.app _), L.jointActCommIso_id,
    ← Functor.map_comp_assoc, nat₂, Functor.map_comp_assoc,
    L.functor_map_actInverseIso_hom_app_comp_assoc, ← Functor.map_comp]
  simp

/-- Mixed unit coherence of transport: the commuting isomorphism of `E_g` with `T_1` is induced
by the unit comparisons `T_1 ≅ 𝟭` of the prescribed actions at `p` and `q`. -/
@[reassoc]
lemma transportCommIso_actId {p q : Γ} (g : p ⟶ q) (X : fiber actions p) :
    (L.transportCommIso g (𝟙 (SingleObj.star H))).hom.app X ≫
        (actId actions q).hom.app ((L.transport g).obj X) =
      (L.transport g).map ((actId actions p).hom.app X) := by
  simp only [transportCommIso_hom_app, transport_map, transport_obj]
  dsimp only [Functor.comp_obj, transport_obj]
  simp only [Category.assoc]
  rw [L.comparisonNaturality_actId, ← Functor.map_comp, Category.assoc,
    L.jointActCommIso_actId, ← Functor.map_comp, L.actInverseIso_actId]

/-! ### The transport pseudofunctor and the action of the endomorphism monoid of an object -/

-- The three lemmas below are the coherence conditions of `transportPseudofunctor`. In them the
-- composite arrows of `Γ` appear in two forms that agree only propositionally (for instance
-- `(f ≫ g) ≫ h` and `f ≫ g ≫ h`), so they are stated for arbitrary composites, related by
-- `eqToHom`.

private lemma transportComp_inv_associativity_eqToHom {p q r s : Γ} (f : p ⟶ q) (g : q ⟶ r)
    (h : r ⟶ s) (fg : p ⟶ r) (gh : q ⟶ s) (fgh fgh' : p ⟶ s) (hfg : f ≫ g = fg)
    (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh') (X : fiber actions p)
    (hX : (L.transport fgh).obj X = (L.transport fgh').obj X) :
    (L.transportComp fg h fgh hfgh).inv.app X ≫
        (L.transport h).map ((L.transportComp f g fg hfg).inv.app X) ≫
          (L.transportComp g h gh hgh).hom.app ((L.transport f).obj X) ≫
            (L.transportComp f gh fgh' hfgh').hom.app X = eqToHom hX := by
  obtain rfl : fgh' = fgh := by rw [← hfgh', ← hfgh, ← hfg, ← hgh, Category.assoc]
  rw [← L.transportComp_associativity f g h fg gh _ hfg hgh hfgh X]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, eqToHom_refl]

private lemma transportComp_inv_left_unitality_eqToHom {p q : Γ} (g k : p ⟶ q)
    (hk : 𝟙 p ≫ g = k) (X : fiber actions p)
    (hX : (L.transport k).obj X = (L.transport g).obj X) :
    (L.transportComp (𝟙 p) g k hk).inv.app X ≫ (L.transport g).map ((L.transportId p).hom.app X) =
      eqToHom hX := by
  obtain rfl : k = g := hk.symm.trans (Category.id_comp g)
  rw [← L.transportComp_left_unitality _ hk X, Iso.inv_hom_id_app, eqToHom_refl]

private lemma transportComp_inv_right_unitality_eqToHom {p q : Γ} (g k : p ⟶ q)
    (hk : g ≫ 𝟙 q = k) (X : fiber actions p)
    (hX : (L.transport k).obj X = (L.transport g).obj X) :
    (L.transportComp g (𝟙 q) k hk).inv.app X ≫ (L.transportId q).hom.app ((L.transport g).obj X) =
      eqToHom hX := by
  obtain rfl : k = g := hk.symm.trans (Category.comp_id g)
  rw [← L.transportComp_right_unitality _ hk X, Iso.inv_hom_id_app, eqToHom_refl]

/-- The transport functors as a pseudofunctor `LocallyDiscrete Γ ⥤ᵖ Cat` with value `C p` at
`p`. It sends `g` to `E_g`; its unit comparison is `transportId` and its composition comparison
at `g ≫ h` is the inverse of `transportComp`, so that `E_(g ≫ h) ≅ E_g ⋙ E_h`. -/
-- The body is exposed so that the value `L.transportPseudofunctor.obj b` is definitionally the
-- fiber `C b.as`, as needed to state the component formulas below in terms of its objects.
@[expose] noncomputable def transportPseudofunctor : LocallyDiscrete Γ ⥤ᵖ Cat.{v, w} :=
  LocallyDiscrete.mkPseudofunctor (fun p ↦ fiber actions p)
    (fun g ↦ (L.transport g).toCatHom)
    (fun p ↦ Cat.Hom.isoMk (L.transportId p))
    (fun g h ↦ Cat.Hom.isoMk (L.transportComp g h (g ≫ h) rfl).symm)
    (fun f g h ↦ by
      ext X
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv, Iso.symm_hom, Iso.symm_inv,
        Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, NatTrans.toCatHom₂_toNatTrans,
        Functor.toCatHom_toFunctor, Cat.Hom.comp_toFunctor, Functor.comp_obj]
      exact L.transportComp_inv_associativity_eqToHom _ _ _ _ _ _ _ _ _ _ _ _ _)
    (fun f ↦ by
      ext X
      simp only [Cat.Hom.isoMk_hom, Iso.symm_hom, Cat.Hom.toNatTrans_comp,
        Cat.whiskerRight_toNatTrans, Cat.leftUnitor_hom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor]
      -- The left unitor of `Cat` contributes an identity whose object is only definitionally
      -- that of the goal, so it is removed through `congrArg` rather than by `rw`.
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (L.transportComp_inv_left_unitality_eqToHom _ _ _ _ _))
    (fun f ↦ by
      ext X
      simp only [Cat.Hom.isoMk_hom, Iso.symm_hom, Cat.Hom.toNatTrans_comp,
        Cat.whiskerLeft_toNatTrans, Cat.rightUnitor_hom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor]
      -- As for the left unitor.
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (L.transportComp_inv_right_unitality_eqToHom _ _ _ _ _))

@[simp]
lemma transportPseudofunctor_obj (b : LocallyDiscrete Γ) :
    L.transportPseudofunctor.obj b = fiber actions b.as :=
  rfl

@[simp]
lemma transportPseudofunctor_map_toFunctor {b b' : LocallyDiscrete Γ} (g : b ⟶ b') :
    (L.transportPseudofunctor.map g).toFunctor = L.transport g.as :=
  rfl

@[simp]
lemma transportPseudofunctor_mapId_hom_toNatTrans_app (b : LocallyDiscrete Γ)
    (X : fiber actions b.as) :
    (L.transportPseudofunctor.mapId b).hom.toNatTrans.app X = (L.transportId b.as).hom.app X :=
  rfl

@[simp]
lemma transportPseudofunctor_mapId_inv_toNatTrans_app (b : LocallyDiscrete Γ)
    (X : fiber actions b.as) :
    (L.transportPseudofunctor.mapId b).inv.toNatTrans.app X = (L.transportId b.as).inv.app X :=
  rfl

@[simp]
lemma transportPseudofunctor_mapComp_hom_toNatTrans_app {b₀ b₁ b₂ : LocallyDiscrete Γ}
    (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) (X : fiber actions b₀.as) :
    (L.transportPseudofunctor.mapComp g h).hom.toNatTrans.app X =
      (L.transportComp g.as h.as (g.as ≫ h.as) rfl).inv.app X :=
  rfl

@[simp]
lemma transportPseudofunctor_mapComp_inv_toNatTrans_app {b₀ b₁ b₂ : LocallyDiscrete Γ}
    (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) (X : fiber actions b₀.as) :
    (L.transportPseudofunctor.mapComp g h).inv.toNatTrans.app X =
      (L.transportComp g.as h.as (g.as ≫ h.as) rfl).hom.app X :=
  rfl

/-- The action of the endomorphism monoid `End p` on the prescribed fiber `C p` by transport,
as a pseudofunctor `LocallyDiscrete (SingleObj (End p)) ⥤ᵖ Cat` with value `C p`: the
restriction of `transportPseudofunctor` along the inclusion `SingleObj (End p) ⥤ Γ`. It sends
`g` to `E_g`; its unit comparison is `transportId` and its composition comparison at `g ≫ h` is
the inverse of `transportComp`. Since `(g * h).asHom = h.asHom ≫ g.asHom` in `End p`, this is a
left action: `E_(g * h) ≅ E_h ⋙ E_g`. When `Γ` is a groupoid, `End p` is the automorphism group
of `p`, so this is the action of the isotropy group of `p` on its fiber. -/
-- The body is exposed so that the value `(L.endAction p).obj b` is definitionally the fiber
-- `C p`, as needed to state the component formulas below in terms of objects of `C p`.
@[expose] noncomputable def endAction (p : Γ) : LocallyDiscrete (SingleObj (End p)) ⥤ᵖ Cat.{v, w} :=
  (SingleObj.functor (MonoidHom.id (End p))).toPseudofunctor.comp L.transportPseudofunctor

-- In the comparisons of `endAction`, the restriction contributes `map₂` of an `eqToHom` between
-- definitionally equal arrows, which is definitionally an identity; it is removed by
-- `Category.id_comp` or `Category.comp_id`.

@[simp]
lemma endAction_obj (p : Γ) (b : LocallyDiscrete (SingleObj (End p))) :
    (L.endAction p).obj b = fiber actions p :=
  rfl

@[simp]
lemma endAction_map_toFunctor (p : Γ) {b b' : LocallyDiscrete (SingleObj (End p))}
    (g : b ⟶ b') : ((L.endAction p).map g).toFunctor = L.transport g.as.asHom :=
  rfl

@[simp]
lemma endAction_mapId_hom_toNatTrans_app (p : Γ) (b : LocallyDiscrete (SingleObj (End p)))
    (X : fiber actions p) :
    ((L.endAction p).mapId b).hom.toNatTrans.app X = (L.transportId p).hom.app X :=
  Category.id_comp _

@[simp]
lemma endAction_mapId_inv_toNatTrans_app (p : Γ) (b : LocallyDiscrete (SingleObj (End p)))
    (X : fiber actions p) :
    ((L.endAction p).mapId b).inv.toNatTrans.app X = (L.transportId p).inv.app X :=
  Category.comp_id _

@[simp]
lemma endAction_mapComp_hom_toNatTrans_app (p : Γ)
    {b₀ b₁ b₂ : LocallyDiscrete (SingleObj (End p))} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂)
    (X : fiber actions p) :
    ((L.endAction p).mapComp g h).hom.toNatTrans.app X =
      (L.transportComp g.as.asHom h.as.asHom (g.as ≫ h.as).asHom rfl).inv.app X :=
  Category.id_comp _

@[simp]
lemma endAction_mapComp_inv_toNatTrans_app (p : Γ)
    {b₀ b₁ b₂ : LocallyDiscrete (SingleObj (End p))} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂)
    (X : fiber actions p) :
    ((L.endAction p).mapComp g h).inv.toNatTrans.app X =
      (L.transportComp g.as.asHom h.as.asHom (g.as ≫ h.as).asHom rfl).hom.app X :=
  Category.comp_id _

end EquivariantGroupoidLift

end TauCeti
