/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
-- The coset action is defined on the coset presheaf and extended along its sheafification, so
-- this file needs the definitions of both, not only their API.
import all TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic

/-!
# The left action of an affine group on its fppf homogeneous quotients

Let `G` be an affine group over a commutative ring `R` and `N` a closed subgroup cut out by a
Hopf ideal `I`. Left multiplication of `G` on itself descends to an action morphism of
presheaves on the affine fppf site

```text
G × G/N ⟶ G/N,    (x, gN) ↦ xgN,
```

where `G/N` is the fppf homogeneous quotient. On the presheaf of left cosets this is the usual
left action of `G(A)` on `G(A)/N(A)`. Sheafification commutes with taking the product with `G`,
in the sense that `G × (cosets) ⟶ G × G/N` becomes an isomorphism after sheafification, so the
coset action extends uniquely to the sheaf `G/N`. Over every value algebra `A` this makes the
`A`-points of `G/N` a `G(A)`-set, naturally in `A`; unlike the translations of
`CommHopfAlgCat.fppfHomogeneousQuotientTranslation`, the acting points need not come from the
base ring.

Every section of `G/N` is fppf locally a coset, and `G/N` is a sheaf, so identities between
sections that hold on cosets hold everywhere
(`CommHopfAlgCat.eq_of_forall_fppfHomogeneousQuotient_map_eq_projection`). This gives the action
laws and shows that translation by a base-ring point is the action of that point.

No finiteness, smoothness, reducedness or normality hypothesis is imposed on `R`, `G` or `N`.

## Main declarations

* `CommHopfAlgCat.fppfHomogeneousQuotientAction`: the action morphism `G × G/N ⟶ G/N`.
* `CommHopfAlgCat.instMulActionPointsFppfHomogeneousQuotient`: the resulting action of `G(A)`
  on the `A`-points of `G/N`, with `x • gN = xgN`
  (`CommHopfAlgCat.smul_fppfHomogeneousQuotientProjection_app`). At the base object it is
  `CommHopfAlgCat.instMulActionPointsBaseFppfHomogeneousQuotient`.
* `CommHopfAlgCat.map_smul_fppfHomogeneousQuotient`: the action is natural in the value algebra.
* `CommHopfAlgCat.fppfHomogeneousQuotientTranslation_hom_app`: translation by a base-ring point is
  the action of its extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c, homogeneous spaces and quotient sheaves.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§14–15.
-/

public section

open CategoryTheory Opposite MonoidalCategory

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)

/-- Left multiplication on the presheaf of left cosets, `(x, gN(A)) ↦ xgN(A)`. -/
private def homogeneousQuotientPresheafAction :
    (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u}) ⊗ homogeneousQuotientPresheaf H I ⟶
      homogeneousQuotientPresheaf H I where
  app A := ↾fun p ↦ ULift.up
    (HSMul.hSMul (α := HopfAlgebra.points (R := R) (H := H) A.unop.unop) p.1.down p.2.down)
  naturality {A B} χ := by
    ext ⟨⟨x⟩, q⟩
    induction q using homogeneousQuotientPresheaf_induction_on H I with | h g =>
    -- On a coset, naturality is multiplicativity of the induced map on points.
    exact congrArg (homogeneousQuotientPresheafMk H I B)
      ((HopfAlgebra.mapPoints (H := H) χ.unop.unop).hom.map_mul x g).symm

/-- Taking the product with any presheaf preserves the sheafification of the coset presheaf. -/
private theorem W_whiskerLeft_toSheafify (P : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :
    (CommAlgCat.fppfTopology R).W
      (P ◁ toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I)) :=
  GrothendieckTopology.W.whiskerLeft (GrothendieckTopology.W_toSheafify _ _) P

/-- The left action `G × G/N ⟶ G/N` of an affine group on its fppf homogeneous quotient by the
closed subgroup cut out by `I`. It is the unique extension of left multiplication on cosets,
`(x, gN) ↦ xgN`, along the sheafification of the coset presheaf. -/
def fppfHomogeneousQuotientAction :
    (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u}) ⊗
        (fppfHomogeneousQuotient H I).obj ⟶
      (fppfHomogeneousQuotient H I).obj :=
  ((W_whiskerLeft_toSheafify H I _).homEquiv _ (fppfHomogeneousQuotient H I).property).symm
    (homogeneousQuotientPresheafAction H I ≫
      toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I))

/-- The action on the sheaf extends the action on cosets. -/
private theorem whiskerLeft_toSheafify_comp_fppfHomogeneousQuotientAction :
    (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u}) ◁
        toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I) ≫
      fppfHomogeneousQuotientAction H I =
    homogeneousQuotientPresheafAction H I ≫
      toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I) :=
  ((W_whiskerLeft_toSheafify H I _).homEquiv _
    (fppfHomogeneousQuotient H I).property).apply_symm_apply _

/-- The action of an `A`-point of `G` on the `A`-points of `G/N`. -/
instance instSMulPointsFppfHomogeneousQuotient (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    SMul (HopfAlgebra.points (R := R) (H := H) A.unop.unop)
      ((fppfHomogeneousQuotient H I).obj.obj A) where
  smul x z := (fppfHomogeneousQuotientAction H I).app A (ULift.up x, z)

/-- The components of the action morphism are the scalar actions on points. -/
@[simp]
theorem fppfHomogeneousQuotientAction_app (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
    (z : (fppfHomogeneousQuotient H I).obj.obj A) :
    dsimp% (fppfHomogeneousQuotientAction H I).app A (ULift.up x, z) = x • z :=
  (rfl)

/-- **The action on cosets.** An `A`-point `x` of `G` sends the image of `g` in `G/N` to the
image of `xg`. -/
@[simp]
theorem smul_fppfHomogeneousQuotientProjection_app (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% x • (fppfHomogeneousQuotientProjection H I).app A (ULift.up g) =
      (fppfHomogeneousQuotientProjection H I).app A (ULift.up (x * g)) :=
  -- The projection is the coset projection followed by sheafification, so this is the
  -- defining equation of the action evaluated at the coset of `g`.
  congrArg (fun α ↦ α.app A (ULift.up x, homogeneousQuotientPresheafMk H I A g))
    (whiskerLeft_toSheafify_comp_fppfHomogeneousQuotientAction H I)

/-- **Naturality of the action.** Changing the value algebra along `f` commutes with the action,
the acting point being mapped along `f` as well. -/
@[simp]
theorem map_smul_fppfHomogeneousQuotient {A B : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
    (z : (fppfHomogeneousQuotient H I).obj.obj A) :
    (fppfHomogeneousQuotient H I).obj.map f (x • z) =
      HopfAlgebra.mapPoints (H := H) f.unop.unop x • (fppfHomogeneousQuotient H I).obj.map f z :=
  (congrArg (fun t ↦ t (ULift.up x, z)) ((fppfHomogeneousQuotientAction H I).naturality f)).symm

/-- **The action laws.** The `A`-points of `G` act on the `A`-points of `G/N`. -/
instance instMulActionPointsFppfHomogeneousQuotient (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    MulAction (HopfAlgebra.points (R := R) (H := H) A.unop.unop)
      ((fppfHomogeneousQuotient H I).obj.obj A) where
  one_smul z := by
    refine eq_of_forall_fppfHomogeneousQuotient_map_eq_projection H I _ z fun B f g hg ↦ ?_
    rw [map_smul_fppfHomogeneousQuotient, map_one, hg, smul_fppfHomogeneousQuotientProjection_app,
      one_mul]
  mul_smul x y z := by
    refine eq_of_forall_fppfHomogeneousQuotient_map_eq_projection H I _ z fun B f g hg ↦ ?_
    rw [map_smul_fppfHomogeneousQuotient, map_smul_fppfHomogeneousQuotient,
      map_smul_fppfHomogeneousQuotient, map_mul, hg, smul_fppfHomogeneousQuotientProjection_app,
      smul_fppfHomogeneousQuotientProjection_app, smul_fppfHomogeneousQuotientProjection_app,
      mul_assoc]

/-- The action of the `R`-points of `G` on the `R`-points of `G/N`, at the base object where fixed
points live. Instance search does not find `instMulActionPointsFppfHomogeneousQuotient` here: it
indexes the acting group by the carrier of `A.unop.unop`, which reduces to `R` at the base object
and so no longer matches. -/
instance instMulActionPointsBaseFppfHomogeneousQuotient :
    MulAction (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
      ((fppfHomogeneousQuotient H I).obj.obj (op (op (CommAlgCat.of R R)))) :=
  instMulActionPointsFppfHomogeneousQuotient H I (op (op (CommAlgCat.of R R)))

/-- **Translation is the action of a base-ring point.** Left translation of `G/N` by a point
`t ∈ G(R)` acts on `A`-points as the extension of `t` to `A`. -/
theorem fppfHomogeneousQuotientTranslation_hom_app
    (t : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (z : (fppfHomogeneousQuotient H I).obj.obj A) :
    (fppfHomogeneousQuotientTranslation H I t).hom.hom.app A z =
      HopfAlgebra.extendPoint H A.unop.unop t • z := by
  refine eq_of_forall_fppfHomogeneousQuotient_map_eq_projection H I _ z fun B f g hg ↦ ?_
  rw [← NatTrans.naturality_apply, hg, map_smul_fppfHomogeneousQuotient, hg,
    HopfAlgebra.mapPoints_extendPoint, smul_fppfHomogeneousQuotientProjection_app]
  exact fppfHomogeneousQuotientTranslation_hom_app_projection H I t B g

end

end CommHopfAlgCat
