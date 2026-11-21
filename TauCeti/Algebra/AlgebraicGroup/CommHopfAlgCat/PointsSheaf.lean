/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.Category.CommAlgCat.PointsSheaf

/-!
# Affine fppf points sheaves of Hopf spectra

For a commutative ring `R` and a same-universe commutative Hopf algebra `H`, this file bridges
between the universe-lifted convolution points presheaf `HopfAlgebra.pointsPresheaf H` and the
affine fppf sheaf of points `CommAlgCat.pointsSheaf (Spec H)`.

Using full faithfulness of `CommAlgCat.pointsSheafFunctor`, morphisms out of
`HopfAlgebra.pointsPresheaf H` into `CommAlgCat.pointsSheaf Y` correspond bijectively to scheme
morphisms `Spec H ⟶ Y` over `Spec R`. Pushing a locally surjective scheme morphism forward along
this identification preserves fppf local surjectivity.

## Main declarations

* `TauCeti.CommHopfAlgCat.hopfPointsPresheafIsoPointsSheaf`: natural isomorphism between the
  lifted convolution points presheaf of `H` and `CommAlgCat.pointsSheaf (Spec H)`.
* `TauCeti.CommHopfAlgCat.hopfPointsToPointsSheaf`: push a scheme morphism `Spec H ⟶ Y` over
  `Spec R` forward to a morphism from convolution points to `CommAlgCat.pointsSheaf Y`.
* `TauCeti.CommHopfAlgCat.pointsSheafHomOfHopfPoints`: recover a scheme morphism `Spec H ⟶ Y`
  from a morphism of points presheaves.
* `TauCeti.CommHopfAlgCat.hopfPointsToPointsSheaf_injective`: morphisms `Spec H ⟶ Y` over
  `Spec R` are determined by their induced maps on convolution points.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- The natural isomorphism identifying the universe-lifted convolution points presheaf of `H` with
the underlying presheaf of `CommAlgCat.pointsSheaf (Spec H)`. -/
noncomputable def hopfPointsPresheafIsoPointsSheaf :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ≅
      (TauCeti.CommAlgCat.pointsSheaf ((hopfSpec (CommRingCat.of R)).obj (op H)).X).obj :=
  Functor.isoWhiskerRight
    (pointsPresheafIsoSchemePointsPresheaf H)
    uliftFunctor.{u + 1, u}

/-- Evaluating `hopfPointsPresheafIsoPointsSheaf` on a lifted convolution `A`-point converts it via
`hopfPointMulEquiv`. -/
theorem hopfPointsPresheafIsoPointsSheaf_hom_app_apply
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (hopfPointsPresheafIsoPointsSheaf H).hom.app A (ULift.up g) =
      ULift.up (hopfPointMulEquiv H A.unop.unop g) :=
  congrArg ULift.up
    ((pointsPresheafIsoSchemePointsPresheaf_hom_app_apply H A g).trans
      (hopfPointMulEquiv_apply H A.unop.unop g).symm)

/-- Push a scheme morphism `Spec H ⟶ Y` over `Spec R` forward to a morphism from the convolution
points presheaf of `H` to the affine fppf points sheaf of `Y`. -/
noncomputable def hopfPointsToPointsSheaf {Y : Over (Spec (CommRingCat.of R))}
    (f : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y) :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (TauCeti.CommAlgCat.pointsSheaf Y).obj :=
  (hopfPointsPresheafIsoPointsSheaf H).hom ≫ (TauCeti.CommAlgCat.pointsSheafMap f).hom

/-- On `A`-valued convolution points, `hopfPointsToPointsSheaf H f` converts `g` via
`hopfPointMulEquiv` and postcomposes with `f`. -/
theorem hopfPointsToPointsSheaf_app_apply {Y : Over (Spec (CommRingCat.of R))}
    (f : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (hopfPointsToPointsSheaf H f).app A (ULift.up g) =
      ULift.up (hopfPointMulEquiv H A.unop.unop g ≫ f) := by
  rw [hopfPointsToPointsSheaf, NatTrans.comp_app, types_comp_apply,
    hopfPointsPresheafIsoPointsSheaf_hom_app_apply,
    TauCeti.CommAlgCat.pointsSheafMap_hom_app_apply]

/-- Two convolution `A`-points have the same image under `hopfPointsToPointsSheaf H f` if and only
if their corresponding scheme points have the same postcomposition with `f`. -/
theorem hopfPointsToPointsSheaf_app_eq_iff {Y : Over (Spec (CommRingCat.of R))}
    (f : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g g' : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (hopfPointsToPointsSheaf H f).app A (ULift.up g) =
        (hopfPointsToPointsSheaf H f).app A (ULift.up g') ↔
      hopfPointMulEquiv H A.unop.unop g ≫ f = hopfPointMulEquiv H A.unop.unop g' ≫ f := by
  rw [hopfPointsToPointsSheaf_app_apply, hopfPointsToPointsSheaf_app_apply]
  exact ULift.up_inj

/-- `hopfPointsToPointsSheaf` is functorial in postcomposition on the target scheme. -/
@[simp]
theorem hopfPointsToPointsSheaf_comp {Y Z : Over (Spec (CommRingCat.of R))}
    (f : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y) (h : Y ⟶ Z) :
    hopfPointsToPointsSheaf H (f ≫ h) =
      hopfPointsToPointsSheaf H f ≫ (TauCeti.CommAlgCat.pointsSheafMap h).hom := by
  rw [hopfPointsToPointsSheaf, hopfPointsToPointsSheaf, TauCeti.CommAlgCat.pointsSheafMap_comp,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

/-- Recover a scheme morphism `Spec H ⟶ Y` over `Spec R` from a natural transformation out of the
convolution points presheaf of `H` into the affine fppf points sheaf of `Y`. -/
noncomputable def pointsSheafHomOfHopfPoints {Y : Over (Spec (CommRingCat.of R))}
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (TauCeti.CommAlgCat.pointsSheaf Y).obj) :
    ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y :=
  TauCeti.CommAlgCat.pointsSheafHomEquiv.symm
    ⟨(hopfPointsPresheafIsoPointsSheaf H).inv ≫ α⟩

/-- Converting a points map to a scheme morphism and back recovers the original points map. -/
@[simp]
theorem hopfPointsToPointsSheaf_pointsSheafHomOfHopfPoints {Y : Over (Spec (CommRingCat.of R))}
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (TauCeti.CommAlgCat.pointsSheaf Y).obj) :
    hopfPointsToPointsSheaf H (pointsSheafHomOfHopfPoints H α) = α := by
  unfold hopfPointsToPointsSheaf pointsSheafHomOfHopfPoints
  rw [TauCeti.CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm]
  exact Iso.hom_inv_id_assoc (hopfPointsPresheafIsoPointsSheaf H) α

/-- Converting a scheme morphism to a points map and back recovers the original scheme morphism. -/
@[simp]
theorem pointsSheafHomOfHopfPoints_hopfPointsToPointsSheaf {Y : Over (Spec (CommRingCat.of R))}
    (f : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y) :
    pointsSheafHomOfHopfPoints H (hopfPointsToPointsSheaf H f) = f := by
  apply TauCeti.CommAlgCat.pointsSheafMap_injective
  unfold pointsSheafHomOfHopfPoints hopfPointsToPointsSheaf
  rw [TauCeti.CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm]
  ext1
  exact Iso.inv_hom_id_assoc (hopfPointsPresheafIsoPointsSheaf H)
    (TauCeti.CommAlgCat.pointsSheafMap f).hom

/-- Two morphisms `Spec H ⟶ Y` over `Spec R` agree if they induce the same map on convolution
points. -/
theorem hopfPointsToPointsSheaf_injective {Y : Over (Spec (CommRingCat.of R))}
    {f g : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y}
    (h : hopfPointsToPointsSheaf H f = hopfPointsToPointsSheaf H g) :
    f = g := by
  rw [← pointsSheafHomOfHopfPoints_hopfPointsToPointsSheaf H f,
    ← pointsSheafHomOfHopfPoints_hopfPointsToPointsSheaf H g, h]

/-- Pushing a locally surjective scheme morphism forward along `hopfPointsToPointsSheaf` preserves
fppf local surjectivity. -/
instance isLocallySurjective_hopfPointsToPointsSheaf {Y : Over (Spec (CommRingCat.of R))}
    (f : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Y)
    [Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (TauCeti.CommAlgCat.pointsSheafMap f).hom] :
    Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (hopfPointsToPointsSheaf H f) :=
  Presheaf.isLocallySurjective_comp (TauCeti.CommAlgCat.fppfTopology R)
    (hopfPointsPresheafIsoPointsSheaf H).hom (TauCeti.CommAlgCat.pointsSheafMap f).hom

/-- Recovering a scheme morphism from a locally surjective points map yields a morphism whose
map on affine points sheaves is fppf locally surjective. -/
instance isLocallySurjective_pointsSheafHomOfHopfPoints {Y : Over (Spec (CommRingCat.of R))}
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (TauCeti.CommAlgCat.pointsSheaf Y).obj)
    [Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R) α] :
    Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (TauCeti.CommAlgCat.pointsSheafMap (pointsSheafHomOfHopfPoints H α)).hom := by
  unfold pointsSheafHomOfHopfPoints
  rw [TauCeti.CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm]
  exact Presheaf.isLocallySurjective_comp (TauCeti.CommAlgCat.fppfTopology R)
    (hopfPointsPresheafIsoPointsSheaf H).inv α

end TauCeti.CommHopfAlgCat
