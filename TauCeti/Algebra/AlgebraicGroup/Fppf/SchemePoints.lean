/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.Category.CommAlgCat.Fppf

/-!
# Affine-group points and fppf sheaves of points of relative schemes

For a commutative ring `R` and a commutative `R`-Hopf algebra `H`,
`TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf` identifies the convolution-points
presheaf `HopfAlgebra.pointsPresheaf H` with relative-spectrum morphisms into `Spec H` via
`AlgebraicGeometry.Spec.mapMulEquiv`. Together with full faithfulness of the fppf sheaf-of-points
functor (`TauCeti.CommAlgCat.fullyFaithfulPointsSheafFunctor`), this identifies `R`-scheme morphisms
`Spec H ⟶ Y` for an arbitrary `Y : Over (Spec R)` with natural transformations from universe-lifted
convolution points of `H` to `(CommAlgCat.pointsSheaf Y).obj`.

## Main declarations

* `CommHopfAlgCat.pointsPresheafUliftIsoPointsSheaf`: natural isomorphism between universe-lifted
  convolution points of `H` and the fppf sheaf of points of `Spec H` over `Spec R`.
* `CommHopfAlgCat.specPointsHomEquiv`: equivalence between `R`-scheme morphisms `Spec H ⟶ Y` and
  natural transformations `HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor ⟶ (pointsSheaf Y).obj`.
* `CommHopfAlgCat.over_hom_ext_of_mapMulEquiv`: extensionality for `R`-scheme morphisms
  `Spec H ⟶ Y` along `Spec.mapMulEquiv` on convolution points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2, 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§1, 14.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- Universe-lifted convolution points of `H` are naturally isomorphic to the underlying presheaf
of the fppf sheaf of points of `Spec H` over `Spec R`. -/
def pointsPresheafUliftIsoPointsSheaf :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ≅
      (CommAlgCat.pointsSheaf ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))).obj :=
  Functor.isoWhiskerRight
    (TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf H) uliftFunctor.{u + 1, u}

/-- Forward evaluation of `pointsPresheafUliftIsoPointsSheaf` applies `Spec.mapMulEquiv` inside
`ULift`. -/
@[simp] theorem pointsPresheafUliftIsoPointsSheaf_hom_app_apply
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (pointsPresheafUliftIsoPointsSheaf H).hom.app A (ULift.up g) =
      ULift.up (Spec.mapMulEquiv g) :=
  congrArg ULift.up
    (TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf_hom_app_apply H A g)

/-- Inverse evaluation of `pointsPresheafUliftIsoPointsSheaf` applies `Spec.mapMulEquiv.symm`
inside `ULift`. -/
@[simp] theorem pointsPresheafUliftIsoPointsSheaf_inv_app_apply (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : (algSpec (CommRingCat.of R)).obj A.unop ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :
    dsimp% (pointsPresheafUliftIsoPointsSheaf H).inv.app A (ULift.up p) =
      ULift.up (Spec.mapMulEquiv.symm p) :=
  congrArg ULift.up
    (TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf_inv_app_apply H A p)

/-- Natural maps from `A`-valued convolution points of `H` to `A`-valued points of an `R`-scheme
`Y` correspond to `R`-scheme morphisms `Spec H ⟶ Y`. -/
def specPointsHomEquiv (Y : Over (Spec (CommRingCat.of R))) :
    ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y) ≃
      (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ (CommAlgCat.pointsSheaf Y).obj) :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).homEquiv.trans <|
    (fullyFaithfulSheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).homEquiv.trans
      (Iso.homFromEquiv (pointsPresheafUliftIsoPointsSheaf H)).symm

/-- `specPointsHomEquiv` sends `q : Spec H ⟶ Y` to `(pointsPresheafUliftIsoPointsSheaf H).hom`
followed by `((CommAlgCat.pointsSheafFunctor R).map q).hom`. -/
theorem specPointsHomEquiv_eq_comp {Y : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y) :
    specPointsHomEquiv H Y q =
      (pointsPresheafUliftIsoPointsSheaf H).hom ≫
        ((CommAlgCat.pointsSheafFunctor R).map q).hom := by
  unfold specPointsHomEquiv
  simp only [Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply, ObjectProperty.ι_map,
    Iso.homFromEquiv_symm_apply]

/-- Forward evaluation of `specPointsHomEquiv` sends an `A`-point `g` of `H` to
`Spec.mapMulEquiv g ≫ q`. -/
@[simp] theorem specPointsHomEquiv_apply_app_apply {Y : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (specPointsHomEquiv H Y q).app A (ULift.up g) = ULift.up (Spec.mapMulEquiv g ≫ q) := by
  rw [specPointsHomEquiv_eq_comp]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply,
    pointsPresheafUliftIsoPointsSheaf_hom_app_apply]
  exact CommAlgCat.pointsSheafFunctor_map_hom_app q A (Spec.mapMulEquiv g)

/-- Point equality under `specPointsHomEquiv` reduces to equality of the underlying
`Spec.mapMulEquiv` composites. -/
theorem specPointsHomEquiv_apply_app_apply_eq_iff {Y : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (g g' : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (specPointsHomEquiv H Y q).app A (ULift.up g) =
        (specPointsHomEquiv H Y q).app A (ULift.up g') ↔
      Spec.mapMulEquiv g ≫ q = Spec.mapMulEquiv g' ≫ q := by
  rw [specPointsHomEquiv_apply_app_apply, specPointsHomEquiv_apply_app_apply]
  exact ⟨congrArg ULift.down, congrArg ULift.up⟩

/-- Precomposing `(specPointsHomEquiv H Y).symm f` with `Spec.mapMulEquiv g` evaluates `f`. -/
@[reassoc (attr := simp)] theorem comp_specPointsHomEquiv_symm {Y : Over (Spec (CommRingCat.of R))}
    (f : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ (CommAlgCat.pointsSheaf Y).obj)
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv g ≫ (specPointsHomEquiv H Y).symm f =
      (f.app (op (op A)) (ULift.up g)).down := by
  have h := congrArg (fun α ↦ (α.app (op (op A)) (ULift.up g)).down)
    ((specPointsHomEquiv H Y).apply_symm_apply f)
  rwa [specPointsHomEquiv_apply_app_apply] at h

/-- `specPointsHomEquiv` is natural with respect to postcomposition by `R`-scheme morphisms. -/
@[simp] theorem specPointsHomEquiv_comp {Y Z : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y) (f : Y ⟶ Z) :
    specPointsHomEquiv H Z (q ≫ f) =
      specPointsHomEquiv H Y q ≫ ((CommAlgCat.pointsSheafFunctor R).map f).hom := by
  rw [specPointsHomEquiv_eq_comp, specPointsHomEquiv_eq_comp,
    Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

/-- Inverse `specPointsHomEquiv` is natural with respect to postcomposition by `R`-scheme
morphisms. -/
@[simp] theorem specPointsHomEquiv_symm_comp {Y Z : Over (Spec (CommRingCat.of R))}
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ (CommAlgCat.pointsSheaf Y).obj)
    (f : Y ⟶ Z) :
    (specPointsHomEquiv H Z).symm (α ≫ ((CommAlgCat.pointsSheafFunctor R).map f).hom) =
      (specPointsHomEquiv H Y).symm α ≫ f :=
  (specPointsHomEquiv H Z).injective <| by simp

omit H in
/-- Two `R`-scheme morphisms `Spec H ⟶ Y` are equal when they agree after precomposition with
`Spec.mapMulEquiv g` for every `A`-valued convolution point `g` of `H`. -/
theorem over_hom_ext_of_mapMulEquiv {H : _root_.CommHopfAlgCat.{u} R}
    {Y : Over (Spec (CommRingCat.of R))}
    {q₁ q₂ : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y}
    (h : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A),
      Spec.mapMulEquiv g ≫ q₁ = Spec.mapMulEquiv g ≫ q₂) : q₁ = q₂ := by
  apply (specPointsHomEquiv H Y).injective; ext A ⟨g⟩
  exact (specPointsHomEquiv_apply_app_apply H q₁ A g).trans <|
    congrArg ULift.up (h A.unop.unop g) |>.trans (specPointsHomEquiv_apply_app_apply H q₂ A g).symm

end

end CommHopfAlgCat
