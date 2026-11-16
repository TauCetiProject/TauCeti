/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.Category.CommAlgCat.Fppf
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# Affine-group points on the affine fppf site

For a commutative ring `R`, the category `(CommAlgCat R)ᵒᵖ` is the category of affine schemes
over `Spec R`. The imported generic affine-site module equips it with the fppf topology induced by
Mathlib's fppf topology on schemes over `Spec R`. Thus a presheaf on this site has the expected
variance

```text
CommAlgCat R ⥤ Type.
```

For a commutative Hopf algebra `H`, the imported Yoneda module registers the underlying type-valued
presheaf of convolution points `A ↦ WithConv (H →ₐ[R] A)` as representable. Its representability
and subcanonicity imply that affine-group points form an fppf sheaf.

Whiskering `TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf` with `uliftFunctor`
identifies the universe-lifted convolution-points presheaf of `H` with the fppf points sheaf of
`(Spec H).asOver (Spec R)`. Combining this comparison with the full faithfulness of
`TauCeti.CommAlgCat.pointsSheafFunctor` yields a bijection between `R`-scheme morphisms
`(Spec H).asOver (Spec R) ⟶ Y` and natural transformations from the universe-lifted convolution
points of `H` to `(CommAlgCat.pointsSheaf Y).obj`.

This is the affine-site foundation for fppf sheafification of pointwise quotients. It does not
assert that such a quotient sheaf is representable; representability requires separate hypotheses.

## Main declarations

* `TauCeti.HopfAlgebra.pointsPresheaf_isSheaf`: affine-group points satisfy fppf descent.
* `TauCeti.HopfAlgebra.pointsFppfSheaf`: affine-group points bundled as an fppf sheaf.
* `CommHopfAlgCat.pointsPresheafUliftIsoPointsSheaf`: natural isomorphism between the
  universe-lifted convolution points of `H` and
  `(CommAlgCat.pointsSheaf ((Spec H).asOver (Spec R))).obj`.
* `CommHopfAlgCat.specAsOverHomEquivPointsPresheafHom`: morphisms `(Spec H).asOver (Spec R) ⟶ Y`
  correspond bijectively to natural maps from `HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor` to
  `(CommAlgCat.pointsSheaf Y).obj`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 2 and 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 1 and 14.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- **Affine-group points form an fppf sheaf.** The type-valued convolution-points presheaf is
representable on the opposite site because the original covariant points functor is
corepresentable. -/
theorem pointsPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsPresheaf H) := by
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr <|
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (pointsPresheaf H)

/-- **The group-valued convolution-points presheaf is an fppf sheaf.** This is the group-valued
form of `pointsPresheaf_isSheaf`; the forgetful functor from groups preserves limits and reflects
isomorphisms. -/
theorem pointsGroupPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsGroupPresheaf H) := by
  exact Presheaf.isSheaf_of_isSheaf_comp
    (CommAlgCat.fppfTopology R) (pointsGroupPresheaf H) (forget GrpCat.{u})
    (pointsPresheaf_isSheaf H)

/-- The convolution-points functor, bundled as a group-valued sheaf on the affine fppf site. -/
noncomputable def pointsFppfSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Sheaf (CommAlgCat.fppfTopology R) GrpCat.{u} :=
  ⟨pointsGroupPresheaf H, pointsGroupPresheaf_isSheaf H⟩

/-- The presheaf underlying `pointsFppfSheaf` is the convolution-points presheaf. -/
@[simp]
theorem pointsFppfSheaf_obj (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsFppfSheaf H).obj = pointsGroupPresheaf H :=
  by rw [pointsFppfSheaf]

end HopfAlgebra

end TauCeti

namespace CommHopfAlgCat

open CategoryTheory AlgebraicGeometry Opposite WithConv
open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- **Universe-lifted convolution points agree naturally with the fppf points of `Spec H`.** -/
noncomputable def pointsPresheafUliftIsoPointsSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ≅
      (CommAlgCat.pointsSheaf
        ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))).obj :=
  Functor.isoWhiskerRight (pointsPresheafIsoSchemePointsPresheaf H) uliftFunctor.{u + 1, u}

-- Deliberately not `@[simp]`: `simpNF` unfolds the presheaf evaluation on the left-hand side.
/-- Evaluating `(pointsPresheafUliftIsoPointsSheaf H).hom` at an `A`-point `g` gives
`Spec.mapMulEquiv g`. -/
theorem pointsPresheafUliftIsoPointsSheaf_hom_app_apply (H : _root_.CommHopfAlgCat.{u} R)
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    (pointsPresheafUliftIsoPointsSheaf H).hom.app (op (op A)) (ULift.up g) =
      ULift.up (Spec.mapMulEquiv g) :=
  congrArg ULift.up (pointsPresheafIsoSchemePointsPresheaf_hom_app_apply H (op (op A)) g)

-- Deliberately not `@[simp]`: `simpNF` unfolds the presheaf evaluation on the left-hand side.
/-- Evaluating `(pointsPresheafUliftIsoPointsSheaf H).inv` at an `A`-point `p` recovers the
convolution point `Spec.mapMulEquiv.symm p`. -/
theorem pointsPresheafUliftIsoPointsSheaf_inv_app_apply (H : _root_.CommHopfAlgCat.{u} R)
    (A : CommAlgCat.{u} R)
    (p : (algSpec (CommRingCat.of R)).obj (op A) ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :
    (pointsPresheafUliftIsoPointsSheaf H).inv.app (op (op A)) (ULift.up p) =
      ULift.up (Spec.mapMulEquiv.symm p) :=
  congrArg ULift.up (pointsPresheafIsoSchemePointsPresheaf_inv_app_apply H (op (op A)) p)

/-- **Morphisms from `Spec H` to an `R`-scheme `Y` are natural maps on affine points.** Morphisms
`(Spec H).asOver (Spec R) ⟶ Y` correspond bijectively to natural transformations from the
universe-lifted convolution-points presheaf of `H` to `(CommAlgCat.pointsSheaf Y).obj`. -/
noncomputable def specAsOverHomEquivPointsPresheafHom (H : _root_.CommHopfAlgCat.{u} R)
    (Y : Over (Spec (CommRingCat.of R))) :
    ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y) ≃
      (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
        (CommAlgCat.pointsSheaf Y).obj) :=
  (CommAlgCat.pointsSheafHomEquiv
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) Y).trans
    (Sheaf.homEquiv.trans (pointsPresheafUliftIsoPointsSheaf H).homFromEquiv.symm)

/-- The natural map attached to `q : (Spec H).asOver (Spec R) ⟶ Y` precomposes
`pointsSheafMap q` with `pointsPresheafUliftIsoPointsSheaf`. -/
theorem specAsOverHomEquivPointsPresheafHom_apply (H : _root_.CommHopfAlgCat.{u} R)
    (Y : Over (Spec (CommRingCat.of R)))
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y) :
    specAsOverHomEquivPointsPresheafHom H Y q =
      (pointsPresheafUliftIsoPointsSheaf H).hom ≫ (CommAlgCat.pointsSheafMap q).hom := by
  simp [specAsOverHomEquivPointsPresheafHom]
  rfl

-- Deliberately not `@[simp]`: `simpNF` unfolds the presheaf evaluation on the left-hand side.
/-- Evaluating `specAsOverHomEquivPointsPresheafHom H Y q` at an `A`-point `g` gives
`Spec.mapMulEquiv g ≫ q`. -/
theorem specAsOverHomEquivPointsPresheafHom_apply_app_apply (H : _root_.CommHopfAlgCat.{u} R)
    (Y : Over (Spec (CommRingCat.of R)))
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    (specAsOverHomEquivPointsPresheafHom H Y q).app (op (op A)) (ULift.up g) =
      ULift.up (Spec.mapMulEquiv g ≫ q) := by
  rw [specAsOverHomEquivPointsPresheafHom_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, pointsPresheafUliftIsoPointsSheaf_hom_app_apply]
  exact CommAlgCat.pointsSheafMap_hom_app_apply q (op (op A)) (Spec.mapMulEquiv g)

/-- Recovering a morphism `(Spec H).asOver (Spec R) ⟶ Y` from a natural map on affine points
evaluates at the universal point `AlgHom.id R H`. -/
theorem specAsOverHomEquivPointsPresheafHom_symm_apply (H : _root_.CommHopfAlgCat.{u} R)
    (Y : Over (Spec (CommRingCat.of R)))
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (CommAlgCat.pointsSheaf Y).obj) :
    (specAsOverHomEquivPointsPresheafHom H Y).symm α =
      (α.app (op (op (CommAlgCat.of R H)))
        (ULift.up (toConv (AlgHom.id R H) :
          HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R H)))).down := by
  have h := congrArg
    (fun β ↦ (β.app (op (op (CommAlgCat.of R H)))
      (ULift.up (toConv (AlgHom.id R H) :
        HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R H)))).down)
    ((specAsOverHomEquivPointsPresheafHom H Y).apply_symm_apply α)
  rw [specAsOverHomEquivPointsPresheafHom_apply_app_apply, mapMulEquiv_toConv_id,
    Category.id_comp] at h
  exact h

/-- Postcomposing a morphism out of `Spec H` with `f : Y ⟶ Z` postcomposes the corresponding
natural map on points with `pointsSheafMap f`. -/
theorem specAsOverHomEquivPointsPresheafHom_comp (H : _root_.CommHopfAlgCat.{u} R)
    {Y Z : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y) (f : Y ⟶ Z) :
    specAsOverHomEquivPointsPresheafHom H Z (q ≫ f) =
      specAsOverHomEquivPointsPresheafHom H Y q ≫ (CommAlgCat.pointsSheafMap f).hom := by
  simp [specAsOverHomEquivPointsPresheafHom_apply, Category.assoc]

/-- Postcomposing a recovered morphism out of `Spec H` with `f : Y ⟶ Z` corresponds to
postcomposing the natural map on points with `pointsSheafMap f`. -/
theorem specAsOverHomEquivPointsPresheafHom_symm_comp (H : _root_.CommHopfAlgCat.{u} R)
    {Y Z : Over (Spec (CommRingCat.of R))}
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (CommAlgCat.pointsSheaf Y).obj)
    (f : Y ⟶ Z) :
    (specAsOverHomEquivPointsPresheafHom H Y).symm α ≫ f =
      (specAsOverHomEquivPointsPresheafHom H Z).symm
        (α ≫ (CommAlgCat.pointsSheafMap f).hom) := by
  apply (specAsOverHomEquivPointsPresheafHom H Z).injective
  rw [specAsOverHomEquivPointsPresheafHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end CommHopfAlgCat
