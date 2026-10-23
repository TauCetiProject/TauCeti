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
`E_(g⁻¹)`.

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
* `TauCeti.EquivariantGroupoidLift.transportEquivalence`: for an isomorphism `g : p ≅ q`, the
  equivalence `C p ≌ C q` with functor `E_g` and inverse `E_(g⁻¹)`.

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

end EquivariantGroupoidLift

end TauCeti
