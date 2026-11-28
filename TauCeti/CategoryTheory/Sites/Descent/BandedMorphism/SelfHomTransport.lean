/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.Fiber.HomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic
public import TauCeti.CategoryTheory.Sites.Descent.PresheafHomMap

/-!
# Transport of the self-morphism sheaves along isomorphisms of objects

Let `b` be an `A`-banding of a prestack `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, and let `X : F ⟶ F` be a
band-preserving self-transformation. For an object `x` of the fibre over `U`, write
`H_x(X) = F.sheafHom J x (X_U x)` for the sheaf on `(Over U, J.over U)` of local morphisms from `x`
to `X_U x` (`BandedMorphism.fiberHomSheafFunctor b b J U x x`). An isomorphism `e : x ≅ x'`
transports `H_x(X)` to `H_{x'}(X)`: a section `p` over `t : T ⟶ U` goes to
`t^* e⁻¹ ≫ p ≫ t^* (X_U e)` (`BandedMorphism.selfHomSheafTransport`). This is an isomorphism of
sheaves with inverse the transport along `e⁻¹` (`BandedMorphism.selfHomSheafTransportIso`),
compatible with identities and composition of isomorphisms, with the action of the band on
sections (`BandedMorphism.selfHomSheafTransport_equivariant`), and with modifications, so that it
is a natural isomorphism of functors of `X` (`BandedMorphism.selfHomSheafTransportNatIso`).
Together these make `x ↦ (X ↦ H_x(X))` a functor on the core of the fibre
(`BandedMorphism.selfHomSheafObjectFunctor`) (Olsson, Remark 31.5; Groechenig, Wyss and Ziegler,
§2.2.1).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `selfHomSheafTransportIso X e` and `selfHomSheafTransport X e`, with
  `selfHomSheafTransport_hom_app`, `selfHomSheafTransport_hom`,
  `selfHomSheafTransportIso_inv`, `selfHomSheafTransportIso_refl`,
  `selfHomSheafTransportIso_trans`, `selfHomSheafTransport_id`,
  `selfHomSheafTransport_comp` and `selfHomSheafTransport_equivariant`.
* `selfHomSheafTransportNatIso e`, with `selfHomSheafTransportNatIso_app`,
  `selfHomSheafTransportNatIso_refl` and `selfHomSheafTransportNatIso_trans`.
* `selfHomSheafObjectFunctor b U`, with `selfHomSheafObjectFunctor_obj` and
  `selfHomSheafObjectFunctor_map`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Remark 31.5
* [Michael Groechenig, Dimitri Wyss and Paul Ziegler](https://link.springer.com/content/pdf/10.1007/s00222-020-00957-8.pdf),
  §2.2.1
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {b : F.AbelianBanding J A} [F.IsPrestack J] {U : C}

/-- **Transport of the self-morphism sheaf along an isomorphism of objects**: for `e : x ≅ x'`,
the isomorphism `H_x(X) ≅ H_{x'}(X)` sending a section `p` over `t : T ⟶ U` to
`t^* e⁻¹ ≫ p ≫ t^* (X_U e)`. -/
noncomputable def selfHomSheafTransportIso (X : HomCategory b b) {x x' : F.obj (.mk (op U))}
    (e : x ≅ x') :
    (fiberHomSheafFunctor b b J U x x).obj X ≅ (fiberHomSheafFunctor b b J U x' x').obj X :=
  F.sheafHomIso J e ((X.obj.app (.mk (op U))).toFunctor.mapIso e)

/-- The forward map of `selfHomSheafTransportIso X e`, the transport `T_e : H_x(X) ⟶ H_{x'}(X)`. -/
noncomputable abbrev selfHomSheafTransport (X : HomCategory b b) {x x' : F.obj (.mk (op U))}
    (e : x ≅ x') :
    (fiberHomSheafFunctor b b J U x x).obj X ⟶ (fiberHomSheafFunctor b b J U x' x').obj X :=
  (selfHomSheafTransportIso X e).hom

/-- The underlying morphism of presheaves of `T_e` is `presheafHomMap e⁻¹ (X_U e)`. -/
theorem selfHomSheafTransport_hom (X : HomCategory b b) {x x' : F.obj (.mk (op U))}
    (e : x ≅ x') :
    (selfHomSheafTransport X e).hom =
      F.presheafHomMap e.inv ((X.obj.app (.mk (op U))).toFunctor.map e.hom) :=
  F.sheafHomIso_hom_hom J _ _

/-- `T_e` sends a section `p` over `t` to `t^* e⁻¹ ≫ p ≫ t^* (X_U e)`. -/
theorem selfHomSheafTransport_hom_app (X : HomCategory b b) {x x' : F.obj (.mk (op U))}
    (e : x ≅ x') (T : (Over U)ᵒᵖ)
    (p : ((fiberHomSheafFunctor b b J U x x).obj X).obj.obj T) :
    (selfHomSheafTransport X e).hom.app T p =
      (F.map T.unop.hom.op.toLoc).toFunctor.map e.inv ≫ p ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map
          ((X.obj.app (.mk (op U))).toFunctor.map e.hom) := by
  rw [selfHomSheafTransport_hom]
  exact F.presheafHomMap_app_apply _ _ T p

/-- The inverse of the transport along `e` is the transport along `e⁻¹`. -/
@[simp]
theorem selfHomSheafTransportIso_inv (X : HomCategory b b) {x x' : F.obj (.mk (op U))}
    (e : x ≅ x') : (selfHomSheafTransportIso X e).inv = selfHomSheafTransport X e.symm :=
  congrArg Iso.hom (F.sheafHomIso_symm J e _)

/-- **Transport along the identity** is the identity isomorphism. -/
@[simp]
theorem selfHomSheafTransportIso_refl (X : HomCategory b b) (x : F.obj (.mk (op U))) :
    selfHomSheafTransportIso X (Iso.refl x) = Iso.refl _ := by
  rw [selfHomSheafTransportIso, Functor.mapIso_refl]
  exact F.sheafHomIso_refl J _ _

/-- **Transport along a composite** is the composite of the transport isomorphisms. -/
theorem selfHomSheafTransportIso_trans (X : HomCategory b b) {x x' x'' : F.obj (.mk (op U))}
    (e : x ≅ x') (f : x' ≅ x'') :
    selfHomSheafTransportIso X (e ≪≫ f) =
      selfHomSheafTransportIso X e ≪≫ selfHomSheafTransportIso X f := by
  rw [selfHomSheafTransportIso, Functor.mapIso_trans]
  exact F.sheafHomIso_trans J _ _ _ _

/-- **Transport along the identity** is the identity. -/
@[simp]
theorem selfHomSheafTransport_id (X : HomCategory b b) (x : F.obj (.mk (op U))) :
    selfHomSheafTransport X (Iso.refl x) = 𝟙 _ := by
  rw [selfHomSheafTransport, selfHomSheafTransportIso_refl, Iso.refl_hom]

/-- **Transport along a composite** is the composite of the transports. -/
theorem selfHomSheafTransport_comp (X : HomCategory b b) {x x' x'' : F.obj (.mk (op U))}
    (e : x ≅ x') (f : x' ≅ x'') :
    selfHomSheafTransport X (e ≪≫ f) = selfHomSheafTransport X e ≫ selfHomSheafTransport X f := by
  rw [selfHomSheafTransport, selfHomSheafTransportIso_trans, Iso.trans_hom]

/-- **Transport commutes with the action of the band**: for a section `p` over `t : T ⟶ U`,
transporting `p` acted on by `a ∈ A(T)` is acting by `a` on the transport of
`p`. -/
theorem selfHomSheafTransport_equivariant (X : HomCategory b b) {x x' : F.obj (.mk (op U))}
    (e : x ≅ x') (T : (Over U)ᵒᵖ)
    (p : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
      (F.map T.unop.hom.op.toLoc).toFunctor.obj ((componentFunctor b b U x).obj X))
    (a : Multiplicative (A.obj.obj (op T.unop.left))) :
    (selfHomSheafTransport X e).hom.app T (b.homAct p a) =
      b.homAct ((selfHomSheafTransport X e).hom.app T p) a := by
  -- The band automorphism commutes with the pullback of `X_U e`, which is an isomorphism.
  have h := b.homAct_comp_hom p ((F.map T.unop.hom.op.toLoc).toFunctor.mapIso
    ((X.obj.app (.mk (op U))).toFunctor.mapIso e)) a
  -- The steps are chained by unification rather than `rw`: the type of `p` mentions
  -- `(componentFunctor b b U x).obj X`, which matches the section type
  -- `(X.obj.app _).toFunctor.obj x` only after unfolding `componentFunctor`, so `rw` cannot
  -- abstract the goal.
  exact (selfHomSheafTransport_hom_app X e T _).trans <| (congrArg _ h).trans <|
    (b.comp_homAct _ _ a).trans
      (congrArg (b.homAct · a) (selfHomSheafTransport_hom_app X e T p).symm)

/-- **Transport is natural in the band-preserving transformation**: for a modification
`m : X ⟶ Y`, acting by `m` and then transporting along `e` is transporting and then acting by
`m`. -/
theorem selfHomSheafTransport_naturality {X Y : HomCategory b b} (m : X ⟶ Y)
    {x x' : F.obj (.mk (op U))} (e : x ≅ x') :
    (fiberHomSheafFunctor b b J U x x).map m ≫ selfHomSheafTransport Y e =
      selfHomSheafTransport X e ≫ (fiberHomSheafFunctor b b J U x' x').map m := by
  apply Sheaf.hom_ext
  -- Both composites are single `presheafHomMap`s; the component of `m` is natural in `e`.
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    fiberHomSheafFunctor_map_hom, fiberHomSheafFunctor_map_hom, selfHomSheafTransport_hom,
    selfHomSheafTransport_hom, ← presheafHomMap_id_left, ← presheafHomMap_id_left]
  -- `rw [← presheafHomMap_comp]` fails here: the middle objects `(componentFunctor b b U x).obj X`
  -- and `(X.obj.app _).toFunctor.obj x` agree only after unfolding `componentFunctor`, so both
  -- composites are merged by unification with `presheafHomMap_comp` instead.
  refine ((presheafHomMap_comp F _ _ _ _).symm.trans ?_).trans (presheafHomMap_comp F _ _ _ _)
  rw [Category.comp_id, Category.id_comp, (m.hom.as.app (.mk (op U))).toNatTrans.naturality]

/-- **The transports form a natural isomorphism** `fiberHomSheafFunctor b b J U x x ≅
fiberHomSheafFunctor b b J U x' x'` of functors of the band-preserving transformation. -/
noncomputable def selfHomSheafTransportNatIso {x x' : F.obj (.mk (op U))} (e : x ≅ x') :
    fiberHomSheafFunctor b b J U x x ≅ fiberHomSheafFunctor b b J U x' x' :=
  NatIso.ofComponents (fun X ↦ selfHomSheafTransportIso X e)
    (fun m ↦ selfHomSheafTransport_naturality m e)

@[simp]
theorem selfHomSheafTransportNatIso_app {x x' : F.obj (.mk (op U))} (e : x ≅ x')
    (X : HomCategory b b) :
    (selfHomSheafTransportNatIso e).app X = selfHomSheafTransportIso X e :=
  NatIso.ofComponents.app _ _ X

@[simp]
theorem selfHomSheafTransportNatIso_refl (x : F.obj (.mk (op U))) :
    selfHomSheafTransportNatIso (b := b) (J := J) (Iso.refl x) = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
  rw [← Iso.app_hom, selfHomSheafTransportNatIso_app, selfHomSheafTransportIso_refl, Iso.refl_hom,
    Iso.refl_hom, NatTrans.id_app]

theorem selfHomSheafTransportNatIso_trans {x x' x'' : F.obj (.mk (op U))} (e : x ≅ x')
    (f : x' ≅ x'') :
    selfHomSheafTransportNatIso (b := b) (J := J) (e ≪≫ f) =
      selfHomSheafTransportNatIso e ≪≫ selfHomSheafTransportNatIso f := by
  refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
  rw [Iso.trans_hom, NatTrans.comp_app, ← Iso.app_hom, ← Iso.app_hom, ← Iso.app_hom,
    selfHomSheafTransportNatIso_app, selfHomSheafTransportNatIso_app,
    selfHomSheafTransportNatIso_app, selfHomSheafTransportIso_trans, Iso.trans_hom]

variable (b U) in
/-- **The self-morphism sheaves as a functor of the object**: on the core of the fibre over `U`,
the functor sending `x` to `X ↦ H_x(X)` and an isomorphism `e` to the transport natural
isomorphism. -/
@[expose]
noncomputable def selfHomSheafObjectFunctor :
    Core (F.obj (.mk (op U))) ⥤ HomCategory b b ⥤ Sheaf (J.over U) (Type v') where
  obj x := fiberHomSheafFunctor b b J U x.of x.of
  map e := (selfHomSheafTransportNatIso e.iso).hom
  map_id x := by
    rw [coreCategory_id_iso, selfHomSheafTransportNatIso_refl, Iso.refl_hom]
  map_comp e f := by
    rw [coreCategory_comp_iso, selfHomSheafTransportNatIso_trans, Iso.trans_hom]

@[simp]
theorem selfHomSheafObjectFunctor_obj (x : Core (F.obj (.mk (op U)))) :
    (selfHomSheafObjectFunctor b U).obj x = fiberHomSheafFunctor b b J U x.of x.of :=
  (rfl)

@[simp]
theorem selfHomSheafObjectFunctor_map {x y : Core (F.obj (.mk (op U)))} (e : x ⟶ y) :
    (selfHomSheafObjectFunctor b U).map e = (selfHomSheafTransportNatIso e.iso).hom :=
  (rfl)

end CategoryTheory.Pseudofunctor.BandedMorphism
