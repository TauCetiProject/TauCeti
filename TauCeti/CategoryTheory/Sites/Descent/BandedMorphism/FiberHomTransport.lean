/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.Fiber.HomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.Restriction

/-!
# Sections of the fibre morphism sheaves as transported isomorphisms

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` carry `A`-bandings `bF`, `bG`, with groupoid fibres for `G`,
and fix objects `x` of the fibre of `F` and `y` of the fibre of `G` over `U`. For a band-preserving
transformation `X : F ⟶ G`, a section of the sheaf `H_X = G.sheafHom J y (X_U x)` over
`t : T ⟶ U` is a morphism `G(t) y ⟶ G(t) (X_U x)`, hence an isomorphism. Composing with the
restriction comparison `BandedMorphism.restrictionIso t X x : G(t) (X_U x) ≅ X_T (F(t) x)`
identifies these sections with isomorphisms `G(t) y ≅ X_T (F(t) x)`
(`BandedMorphism.fiberHomTransportIsoEquiv`). Under this identification, the action of a
modification `m : X ⟶ Y` on `H_X` (`BandedMorphism.fiberHomSheafFunctor`) becomes composition with
the component isomorphism of `m` at `F(t) x`
(`BandedMorphism.fiberHomTransportIsoEquiv_modification`; Olsson, Remark 31.5; Groechenig, Wyss and
Ziegler, §2.2.1).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `fiberHomTransportIsoEquiv`, with `fiberHomTransportIsoEquiv_apply_hom` and
  `fiberHomTransportIsoEquiv_symm_apply`.
* `fiberHomTransportIsoEquiv_modification`.

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
  {A : Sheaf J AddCommGrpCat.{w}} {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  [G.IsPrestack J] [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
  {U : C} (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- **Sections of the fibre morphism sheaf as transported isomorphisms**: over `t : T ⟶ U`, a
section `p` of `H_X = G.sheafHom J y (X_U x)` is sent to the isomorphism with forward morphism `p`
(`Groupoid.isoEquivHom`) followed by the restriction comparison `G(t) (X_U x) ≅ X_T (F(t) x)` of
`X` along `t` (`Iso.isoCongrRight`). -/
noncomputable def fiberHomTransportIsoEquiv (X : HomCategory bF bG) (T : Over U) :
    ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op T) ≃
      ((G.map T.hom.op.toLoc).toFunctor.obj y ≅
        (X.obj.app (.mk (op T.left))).toFunctor.obj ((F.map T.hom.op.toLoc).toFunctor.obj x)) :=
  letI := Groupoid.ofIsGroupoid (C := G.obj (.mk (op T.left)))
  (Groupoid.isoEquivHom _ _).symm.trans (Iso.isoCongrRight (restrictionIso T.hom X.obj x))

theorem fiberHomTransportIsoEquiv_apply_hom (X : HomCategory bF bG) (T : Over U)
    (p : ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op T)) :
    (fiberHomTransportIsoEquiv x y X T p).hom =
      p ≫ (restrictionIso T.hom X.obj x).hom :=
  Category.id_comp _

/-- The inverse of `fiberHomTransportIsoEquiv` composes with the inverse restriction comparison
and takes the forward morphism. -/
theorem fiberHomTransportIsoEquiv_symm_apply (X : HomCategory bF bG) (T : Over U)
    (q : (G.map T.hom.op.toLoc).toFunctor.obj y ≅
      (X.obj.app (.mk (op T.left))).toFunctor.obj ((F.map T.hom.op.toLoc).toFunctor.obj x)) :
    (fiberHomTransportIsoEquiv x y X T).symm q = q.hom ≫ (restrictionIso T.hom X.obj x).inv :=
  Category.id_comp _

/-- **Modifications act on transported isomorphisms by their components**: transporting the image
of a section `p` of `H_X` under the action of `m : X ⟶ Y` gives the transport of `p` followed by
the component isomorphism of `m` at `F(t) x`. -/
theorem fiberHomTransportIsoEquiv_modification {X Y : HomCategory bF bG} (m : X ⟶ Y)
    (T : Over U) (p : ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op T)) :
    fiberHomTransportIsoEquiv x y Y T (((fiberHomSheafFunctor bF bG J U x y).map m).hom.app _ p) =
      fiberHomTransportIsoEquiv x y X T p ≪≫
        componentIso m T.left ((F.map T.hom.op.toLoc).toFunctor.obj x) := by
  ext
  have h := congrArg Iso.hom (restrictionIso_modification T.hom m x)
  simp only [Iso.trans_hom, Functor.mapIso_hom, componentIso_hom] at h
  rw [Iso.trans_hom, fiberHomTransportIsoEquiv_apply_hom, fiberHomTransportIsoEquiv_apply_hom,
    fiberHomSheafFunctor_map_hom_app, componentIso_hom]
  -- Term mode: a section `p` is a morphism only after unfolding `presheafHom`, beyond the reducible
  -- transparency at which `simp` and `rw` would apply `Category.assoc`.
  exact (Category.assoc _ _ _).trans ((p ≫= h).trans (Category.assoc _ _ _).symm)

end CategoryTheory.Pseudofunctor.BandedMorphism
