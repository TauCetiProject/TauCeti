/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Lifting problems for strong transformations of pseudofunctors

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be pseudofunctors, thought of as fibred categories over
`C`, and let `f : F ⟶ G` be a strong transformation. For a morphism `j : A ⟶ B` of `C`, a
*lifting problem* `f.LiftingProblem j` is a `2`-commutative square
```
A --x--> F
|        |
j        f
|        |
v        v
B --y--> G
```
that is, objects `x` of `F` over `A` and `y` of `G` over `B` with an isomorphism
`γ : j^* y ≅ f x` over `A`. A *lift* (a *dotted arrow*) is an object `a` of `F` over `B` with
isomorphisms `α : j^* a ≅ x` and `β : y ≅ f a` which recover `γ`, through the naturality
isomorphism `j^* (f a) ≅ f (j^* a)` of `f`. Lifts form a category `P.Lift`, whose morphisms are the
morphisms of `F` over `B` compatible with `α` and `β`; it is a groupoid when the fibre of `F` over
`B` is one (Stacks, Definition 0CLA, which takes `j` to be `Spec K ⟶ Spec A` for a valuation
ring `A` with fraction field `K`).

The category of lifts does not depend on the chosen identification `γ` up to replacing `x` by an
isomorphic object: `LiftingProblem.reidentify e` changes `x` along `e : x ≅ x'`, and
`LiftingProblem.reidentifyEquiv` is the resulting equivalence of categories of lifts. A
commutative square of `C` with right side `j` and left side `j'` pulls a lifting problem along `j`
back to one along `j'` (`LiftingProblem.pullback`), and lifts pull back with it
(`LiftingProblem.pullbackFunctor`); this uses the pseudofunctor coherence isomorphisms of `F` and
`G` and the compatibility of `f` with them. Finally, `LiftingProblem.nonempty_lift` shows that a
lift exists whenever `f` is essentially surjective over `B` and fully faithful over `A`.

These lifts are the dotted arrows of the valuative criteria for morphisms of algebraic stacks.

## Main declarations

* `CategoryTheory.Pseudofunctor.StrongTrans.LiftingProblem`: a `2`-commutative square from `j`
  to `f`.
* `CategoryTheory.Pseudofunctor.StrongTrans.LiftingProblem.Lift`: the category of its lifts.
* `CategoryTheory.Pseudofunctor.StrongTrans.LiftingProblem.reidentifyEquiv`: lifts are
  unchanged by reidentifying `x`.
* `CategoryTheory.Pseudofunctor.StrongTrans.LiftingProblem.pullbackFunctor`: lifts pull back
  along commutative squares.

## References

* [Stacks Project, Definition 0CLA](https://stacks.math.columbia.edu/tag/0CLA)
-/

public section

universe v' u' v u

namespace CategoryTheory.Pseudofunctor.StrongTrans

open Opposite

variable {C : Type u} [Category.{v} C] {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

variable (f : StrongTrans F G) in
/-- A lifting problem for the strong transformation `f` along a morphism `j : A ⟶ B`: a
`2`-commutative square given by an object `top` of `F` over `A`, an object `bottom` of `G` over
`B`, and an isomorphism `iso : j^* bottom ≅ f top` over `A`. -/
structure LiftingProblem {A B : C} (j : A ⟶ B) where
  /-- The object of `F` over the source `A` of `j`. -/
  top : F.obj (.mk (op A))
  /-- The object of `G` over the target `B` of `j`. -/
  bottom : G.obj (.mk (op B))
  /-- The `2`-cell of the square: an identification of `j^* bottom` with `f top`. -/
  iso : (G.map j.op.toLoc).toFunctor.obj bottom ≅ (f.app (.mk (op A))).toFunctor.obj top

namespace LiftingProblem

variable {f : StrongTrans F G} {A B : C} {j : A ⟶ B} (P : f.LiftingProblem j)

/-- A lift (dotted arrow) of a lifting problem `P` along `j : A ⟶ B`: an object `obj` of `F`
over `B` with isomorphisms `isoTop : j^* obj ≅ P.top` and `isoBottom : P.bottom ≅ f obj` whose
composite with the naturality isomorphism of `f` at `j` is the `2`-cell `P.iso`
(Stacks, Definition 0CLA). -/
structure Lift where
  /-- The object of `F` over `B` filling the square. -/
  obj : F.obj (.mk (op B))
  /-- The identification of the restriction of `obj` along `j` with `P.top`. -/
  isoTop : (F.map j.op.toLoc).toFunctor.obj obj ≅ P.top
  /-- The identification of `P.bottom` with the image of `obj` under `f`. -/
  isoBottom : P.bottom ≅ (f.app (.mk (op B))).toFunctor.obj obj
  /-- The two identifications recover the `2`-cell of the square. -/
  comm : (G.map j.op.toLoc).toFunctor.map isoBottom.hom ≫
      (f.naturality j.op.toLoc).inv.toNatTrans.app obj ≫
        (f.app (.mk (op A))).toFunctor.map isoTop.hom = P.iso.hom

attribute [reassoc (attr := simp)] Lift.comm

namespace Lift

variable {P}

/-- A morphism of lifts: a morphism of `F` over `B` compatible with both identifications. -/
@[ext]
structure Hom (a b : P.Lift) where
  /-- The underlying morphism of `F` over `B`. -/
  hom : a.obj ⟶ b.obj
  comm_top : (F.map j.op.toLoc).toFunctor.map hom ≫ b.isoTop.hom = a.isoTop.hom := by
    cat_disch
  comm_bottom : a.isoBottom.hom ≫ (f.app (.mk (op B))).toFunctor.map hom = b.isoBottom.hom := by
    cat_disch

attribute [reassoc (attr := simp)] Hom.comm_top Hom.comm_bottom

instance : Category P.Lift where
  Hom := Hom
  id a := { hom := 𝟙 a.obj }
  comp φ ψ := { hom := φ.hom ≫ ψ.hom }

@[ext]
lemma hom_ext {a b : P.Lift} {φ ψ : a ⟶ b} (h : φ.hom = ψ.hom) : φ = ψ :=
  Hom.ext h

@[simp]
lemma id_hom (a : P.Lift) : Hom.hom (𝟙 a) = 𝟙 a.obj :=
  rfl

@[simp, reassoc]
lemma comp_hom {a b c : P.Lift} (φ : a ⟶ b) (ψ : b ⟶ c) : (φ ≫ ψ).hom = φ.hom ≫ ψ.hom :=
  rfl

/-- An isomorphism of lifts from an isomorphism of the underlying objects compatible with both
identifications. -/
def isoMk {a b : P.Lift} (e : a.obj ≅ b.obj)
    (h₁ : (F.map j.op.toLoc).toFunctor.map e.hom ≫ b.isoTop.hom = a.isoTop.hom := by cat_disch)
    (h₂ : a.isoBottom.hom ≫ (f.app (.mk (op B))).toFunctor.map e.hom = b.isoBottom.hom := by
      cat_disch) :
    a ≅ b where
  hom := { hom := e.hom }
  inv :=
    { hom := e.inv
      comm_top := by rw [← h₁, ← Functor.map_comp_assoc, e.inv_hom_id, Functor.map_id,
        Category.id_comp]
      comm_bottom := by rw [← h₂, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
        Functor.map_id, Category.comp_id] }

@[simp]
lemma isoMk_hom_hom {a b : P.Lift} (e : a.obj ≅ b.obj)
    (h₁ : (F.map j.op.toLoc).toFunctor.map e.hom ≫ b.isoTop.hom = a.isoTop.hom)
    (h₂ : a.isoBottom.hom ≫ (f.app (.mk (op B))).toFunctor.map e.hom = b.isoBottom.hom) :
    (isoMk e h₁ h₂).hom.hom = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom {a b : P.Lift} (e : a.obj ≅ b.obj)
    (h₁ : (F.map j.op.toLoc).toFunctor.map e.hom ≫ b.isoTop.hom = a.isoTop.hom)
    (h₂ : a.isoBottom.hom ≫ (f.app (.mk (op B))).toFunctor.map e.hom = b.isoBottom.hom) :
    (isoMk e h₁ h₂).inv.hom = e.inv :=
  (rfl)

/-- A morphism of lifts is an isomorphism as soon as its underlying morphism is. -/
lemma isIso_of_isIso_hom {a b : P.Lift} (φ : a ⟶ b) [IsIso φ.hom] : IsIso φ :=
  (isoMk (asIso φ.hom) φ.comm_top φ.comm_bottom).isIso_hom

/-- Lifts form a groupoid when the fibre of `F` over the target of `j` is a groupoid, as it is
for stacks in groupoids. -/
instance [IsGroupoid (F.obj (.mk (op B)))] : IsGroupoid P.Lift where
  all_isIso φ := isIso_of_isIso_hom φ

end Lift

section Reidentify

variable {x' : F.obj (.mk (op A))} (e : P.top ≅ x')

/-- The lifting problem obtained from `P` by replacing its top object `x` by an isomorphic object
`x'` along `e : x ≅ x'`, and its `2`-cell `γ` by `γ` followed by `f e`. -/
@[simps]
abbrev reidentify : f.LiftingProblem j where
  top := x'
  bottom := P.bottom
  iso := P.iso ≪≫ (f.app (.mk (op A))).toFunctor.mapIso e

/-- Lifts of `P` give lifts of `P.reidentify e`, by composing their top identification
with `e`. -/
@[simps]
abbrev reidentifyFunctor : P.Lift ⥤ (P.reidentify e).Lift where
  obj a :=
    { obj := a.obj
      isoTop := a.isoTop ≪≫ e
      isoBottom := a.isoBottom
      comm := by
        simp [a.comm_assoc] }
  map φ :=
    { hom := φ.hom
      comm_top := by simp }

/-- Lifts of `P.reidentify e` give lifts of `P`, by composing their top identification
with `e.symm`. -/
@[simps]
abbrev reidentifyInverse : (P.reidentify e).Lift ⥤ P.Lift where
  obj a :=
    { obj := a.obj
      isoTop := a.isoTop ≪≫ e.symm
      isoBottom := a.isoBottom
      comm := by
        have := a.comm
        simp only [Iso.trans_hom, Functor.mapIso_hom] at this
        simp [reassoc_of% this] }
  map φ :=
    { hom := φ.hom
      comm_top := by simp }

/-- Reidentifying the top object of a lifting problem along an isomorphism does not change its
category of lifts. -/
def reidentifyEquiv : P.Lift ≌ (P.reidentify e).Lift where
  functor := P.reidentifyFunctor e
  inverse := P.reidentifyInverse e
  unitIso := NatIso.ofComponents (fun a ↦ Lift.isoMk (Iso.refl a.obj))
  counitIso := NatIso.ofComponents (fun a ↦ Lift.isoMk (Iso.refl a.obj))

@[simp]
lemma reidentifyEquiv_functor : (P.reidentifyEquiv e).functor = P.reidentifyFunctor e :=
  (rfl)

@[simp]
lemma reidentifyEquiv_inverse : (P.reidentifyEquiv e).inverse = P.reidentifyInverse e :=
  (rfl)

end Reidentify

section Pullback

variable {A' B' : C} {h : A' ⟶ A} {j' : A' ⟶ B'} {g : B' ⟶ B} (sq : CommSq h j' j g)

/-- The pullback of a lifting problem `P` along `j` to a lifting problem along `j'`, through a
commutative square `h ≫ j = j' ≫ g`: its objects are `h^* x` and `g^* y`, and its `2`-cell is
`j'^* g^* y ≅ h^* j^* y ≅ h^* (f x) ≅ f (h^* x)`, built from the square isomorphism of `G`, the
restriction of `γ` along `h`, and the naturality isomorphism of `f` at `h`. -/
@[simps]
abbrev pullback : f.LiftingProblem j' where
  top := (F.map h.op.toLoc).toFunctor.obj P.top
  bottom := (G.map g.op.toLoc).toFunctor.obj P.bottom
  iso := (Cat.Hom.toNatIso (G.isoMapOfCommSq sq.op.toLoc)).app P.bottom ≪≫
    (G.map h.op.toLoc).toFunctor.mapIso P.iso ≪≫
      (Cat.Hom.toNatIso (f.naturality h.op.toLoc)).symm.app P.top

/-- A lift of `P` restricts to a lift of its pullback along a commutative square: the object
`g^* a`, with identifications `j'^* g^* a ≅ h^* j^* a ≅ h^* x` and `g^* y ≅ g^* (f a) ≅ f (g^* a)`.
-/
@[expose, simps]
def pullbackFunctor : P.Lift ⥤ (P.pullback sq).Lift where
  obj a :=
    { obj := (F.map g.op.toLoc).toFunctor.obj a.obj
      isoTop := (Cat.Hom.toNatIso (F.isoMapOfCommSq sq.op.toLoc)).app a.obj ≪≫
        (F.map h.op.toLoc).toFunctor.mapIso a.isoTop
      isoBottom := (G.map g.op.toLoc).toFunctor.mapIso a.isoBottom ≪≫
        (Cat.Hom.toNatIso (f.naturality g.op.toLoc)).symm.app a.obj
      comm := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
          Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Functor.map_comp, Category.assoc]
        rw [f.naturality_inv_isoMapOfCommSq_app_assoc sq.op.toLoc, ← a.comm]
        have h₁ := (G.isoMapOfCommSq sq.op.toLoc).hom.toNatTrans.naturality a.isoBottom.hom
        have h₂ := (f.naturality h.op.toLoc).inv.toNatTrans.naturality a.isoTop.hom
        dsimp at h₁ h₂
        simp only [Functor.map_comp, Category.assoc, ← h₂, reassoc_of% h₁] }
  map φ :=
    { hom := (F.map g.op.toLoc).toFunctor.map φ.hom
      comm_top := by
        have := (F.isoMapOfCommSq sq.op.toLoc).hom.toNatTrans.naturality φ.hom
        dsimp at this
        simp only [Iso.trans_hom, Iso.app_hom, Cat.Hom.toNatIso_hom, Functor.mapIso_hom,
          reassoc_of% this, ← Functor.map_comp, φ.comm_top]
      comm_bottom := by
        have := (f.naturality g.op.toLoc).inv.toNatTrans.naturality φ.hom
        dsimp at this
        simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Cat.Hom.toNatIso_inv,
          Functor.mapIso_hom, Category.assoc, ← this, ← Functor.map_comp_assoc, φ.comm_bottom] }
  map_id _ := Lift.hom_ext (Functor.map_id _ _)
  map_comp _ _ := Lift.hom_ext (Functor.map_comp _ _ _)

/-- If a lifting problem has a lift, so does each of its pullbacks. -/
lemma nonempty_lift_pullback [Nonempty P.Lift] : Nonempty (P.pullback sq).Lift :=
  ⟨(P.pullbackFunctor sq).obj (Classical.arbitrary _)⟩

end Pullback

/-- A lifting problem along `j : A ⟶ B` has a lift when `f` is essentially surjective over `B`
and fully faithful over `A`; in particular, when `f` is an equivalence over every object. -/
lemma nonempty_lift [(f.app (.mk (op B))).toFunctor.EssSurj]
    [(f.app (.mk (op A))).toFunctor.Full] [(f.app (.mk (op A))).toFunctor.Faithful] :
    Nonempty P.Lift := by
  let fB := (f.app (.mk (op B))).toFunctor
  let a := fB.objPreimage P.bottom
  let β : P.bottom ≅ fB.obj a := (fB.objObjPreimageIso P.bottom).symm
  let hA := Functor.FullyFaithful.ofFullyFaithful (f.app (.mk (op A))).toFunctor
  let α : (F.map j.op.toLoc).toFunctor.obj a ≅ P.top := hA.preimageIso
    ((Cat.Hom.toNatIso (f.naturality j.op.toLoc)).app a ≪≫
      (G.map j.op.toLoc).toFunctor.mapIso β.symm ≪≫ P.iso)
  exact ⟨{ obj := a, isoTop := α, isoBottom := β, comm := by simp [α] }⟩

end LiftingProblem

end CategoryTheory.Pseudofunctor.StrongTrans
