/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic
public import TauCeti.CategoryTheory.Quotient.Monoidal

/-!
# Monoidal categories presented by generators and relations

A *presentation* of a monoidal category consists of a tensor signature `S` (generating objects,
and generating morphisms, or coupons, between tensor words in them) together with a family
`R : HomRel S.FreeMonoidal` of typed equations between morphisms of the free monoidal category
on `S`. The monoidal category `S.Presented R` it presents is the quotient of
`TauCeti.TensorSignature.FreeMonoidal S` by the least congruence which contains `R` and is
compatible with the monoidal structure: the quotient category by the monoidal closure
`HomRel.MonoidalClosure R`, with the monoidal structure descended to it. Only the equations `R`
are imposed beyond the axioms of a monoidal category; with `R` empty, distinct composites of
coupons stay distinct.

Its universal property is that of the free monoidal category restricted to the interpretations
satisfying the equations: a choice of images of the generating objects and coupons in an
arbitrary (not necessarily strict) monoidal category `D` whose induced strong monoidal functor
`TauCeti.TensorSignature.FreeMonoidal.lift` identifies the two sides of every equation of `R`
factors through a strong monoidal functor `S.Presented R ⥤ D`, which is unique up to a unique
monoidal natural isomorphism extending given isomorphisms on the generating objects.

## Main definitions and results

* `TauCeti.TensorSignature.Presented S R`: the monoidal category presented by `S` and `R`, and
  `TauCeti.TensorSignature.Presented.quotientFunctor R` the strict monoidal quotient functor from
  the free monoidal category, which identifies the two sides of every equation of `R`
  (`TauCeti.TensorSignature.Presented.sound`).
* `TauCeti.TensorSignature.Presented.lift fo fc h`: the strong monoidal functor determined by the
  images `fo` of the generating objects and `fc` of the coupons satisfying the equations, with
  computation rules `TauCeti.TensorSignature.Presented.lift_obj` and
  `TauCeti.TensorSignature.Presented.lift_map`, and the factorization
  `TauCeti.TensorSignature.Presented.quotientFunctor_comp_lift`.
* `TauCeti.TensorSignature.Presented.monoidalNatIso`: two strong monoidal functors out of
  `S.Presented R` agreeing up to isomorphism on the generating objects, compatibly with the
  coupons, are monoidally naturally isomorphic; `TauCeti.TensorSignature.Presented.natTrans_ext`:
  monoidal natural transformations out of `S.Presented R` are determined by their components at
  the generating objects.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1
  (free monoidal categories on tensor schemes; presentations are their quotients).
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v}) (R : HomRel S.FreeMonoidal)

/-- The monoidal category presented by the tensor signature `S` and the equations `R` between
morphisms of the free monoidal category on `S`: the quotient of the free monoidal category by the
least monoidal congruence containing `R`. Its objects are the tensor words in the generating
objects of `S`. -/
abbrev Presented : Type u :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure R)

namespace Presented

variable {S}

/-- The quotient functor from the free monoidal category on `S` onto the monoidal category
presented by `S` and `R`. It is strict monoidal for the descended monoidal structure. -/
abbrev quotientFunctor : S.FreeMonoidal ⥤ S.Presented R :=
  CategoryTheory.Quotient.functor _

variable {R}

/-- The equations `R` hold in the presented monoidal category. -/
theorem sound {X Y : S.FreeMonoidal} {f g : X ⟶ Y} (h : R f g) :
    (quotientFunctor R).map f = (quotientFunctor R).map g :=
  CategoryTheory.Quotient.sound _ (.of h)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon,
    FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
  (h : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g)

/-- The functor out of the monoidal category presented by `S` and `R` determined by the images
`fo` of the generating objects and `fc` of the coupons, provided the induced interpretation of the
free monoidal category satisfies the equations `R`. It is strong monoidal, with identity
tensorator and unit comparison. -/
-- The body is exposed so that the object part reduces, as for `FreeMonoidal.lift`: the statements
-- of `lift_ε` and its companions only typecheck once objects of the form `(lift fo fc h).obj X`
-- reduce to the corresponding tensor products in `D`.
@[expose] def lift : S.Presented R ⥤ D :=
  CategoryTheory.Quotient.lift _ (FreeMonoidal.lift fo fc) fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq h hfg

instance : (lift fo fc h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

/-- The functor `lift fo fc h` restricts along the quotient functor to the interpretation
`FreeMonoidal.lift fo fc` of the free monoidal category. -/
theorem quotientFunctor_comp_lift : quotientFunctor R ⋙ lift fo fc h = FreeMonoidal.lift fo fc :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem lift_obj (X : S.FreeMonoidal) :
    (lift fo fc h).obj ((quotientFunctor R).obj X) = (FreeMonoidal.lift fo fc).obj X :=
  (rfl)

@[simp]
theorem lift_map {X Y : S.FreeMonoidal} (f : X ⟶ Y) :
    (lift fo fc h).map ((quotientFunctor R).map f) = (FreeMonoidal.lift fo fc).map f :=
  (rfl)

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans (FreeMonoidal.lift_ε fo fc)

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans (FreeMonoidal.lift_η fo fc)

@[simp]
theorem lift_μ (X Y : S.Presented R) : Functor.LaxMonoidal.μ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans (FreeMonoidal.lift_μ fo fc X.as Y.as)

@[simp]
theorem lift_δ (X Y : S.Presented R) : Functor.OplaxMonoidal.δ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans (FreeMonoidal.lift_δ fo fc X.as Y.as)

end Lift

section Uniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of the presented
monoidal category to a lax monoidal one is determined by its components at the generating
objects. -/
theorem natTrans_ext {F G : S.Presented R ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a, α.app ((quotientFunctor R).obj (.of a)) = β.app ((quotientFunctor R).obj (.of a))) :
    α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _ (FreeMonoidal.natTrans_ext h)

variable (F G : S.Presented R ⥤ D) [F.Monoidal] [G.Monoidal]
  (e : ∀ a, F.obj ((quotientFunctor R).obj (.of a)) ≅ G.obj ((quotientFunctor R).obj (.of a)))

/-- Two strong monoidal functors out of the monoidal category presented by `S` and `R` that agree
up to isomorphisms `e` on the generating objects, compatibly with every coupon, are isomorphic by
a monoidal natural isomorphism extending `e`. The compatibility is stated with the isomorphisms
`FreeMonoidal.wordIso` which `e` induces on all tensor words. -/
def monoidalNatIso
    (he : ∀ g, F.map ((quotientFunctor R).map (FreeMonoidal.coupon g)) ≫
        (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
      (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
        G.map ((quotientFunctor R).map (FreeMonoidal.coupon g))) :
    F ≅ G :=
  CategoryTheory.Quotient.natIsoLift _ (FreeMonoidal.monoidalNatIso he)

variable {F G e}
  (he : ∀ g, F.map ((quotientFunctor R).map (FreeMonoidal.coupon g)) ≫
      (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
    (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
      G.map ((quotientFunctor R).map (FreeMonoidal.coupon g)))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeMonoidal) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj X) =
      (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e X.as).hom :=
  FreeMonoidal.monoidalNatIso_hom_app he X

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj (.of a)) = (e a).hom :=
  FreeMonoidal.monoidalNatIso_hom_app_of he a

instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.natTransLift _ (FreeMonoidal.monoidalNatIso he).hom))

end Uniqueness

end Presented

end TauCeti.TensorSignature
