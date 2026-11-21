/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PointsSheaf
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Homogeneous
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Orbit-map comparison for fppf homogeneous quotients

Let `G = Spec H` be an affine algebraic group scheme over a commutative ring `R` acting on a
scheme `X` over `Spec R`, and let `x : Spec R ⟶ X` be a section that is a closed immersion (for
instance, any rational point when `R` is a field).

The scheme-theoretic stabilizer `stabilizer G x` is a closed subgroup scheme of `G`, hence cut out
by a unique Hopf ideal `stabilizerHopfIdeal H x` of `H`. Over every `R`-algebra `A`, the subgroup
of `A`-points cut out by this Hopf ideal is precisely the stabilizer of `x` in `G(A)`, and the
orbit morphism `orbitMap G x` descends to a morphism of fppf sheaves from the fppf homogeneous
quotient `G / Stab_G(x)` to `CommAlgCat.pointsSheaf X`.

When `R = k` is an algebraically closed field and `H` is reduced and of finite type over `k`, and
`X` is of finite type over `k`:

* The descended orbit projection `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf (orbitOver G x)` is an
  isomorphism of fppf sheaves, for every orbit (without assuming `X` reduced, separated, or
  homogeneous).
* If moreover `X` is reduced (or smooth) and `orbit G x = Set.univ` (equivalently, `G(k)` acts
  transitively on `X(k)`), then the descended orbit morphism
  `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf sheaves, and the orbit
  morphism `G ⟶ X` is smooth if and only if the coordinate Hopf algebra of the stabilizer is
  smooth over `k`.
* Because `CommAlgCat.pointsSheafFunctor` is fully faithful, any scheme `Q` over `Spec k`
  representing `G / Stab_G(x)` — in particular, Chevalley's projective-orbit quotient model — is
  canonically isomorphic over `Spec k` to `orbitOver G x` (and to `X` when `X` is reduced and
  homogeneous), intertwining the quotient projection with the orbit morphism and respecting the
  `G`-action whenever the quotient projection is equivariant.

## Main declarations

* `TauCeti.SchemeAction.stabilizerClosedSubgroup`: the scheme-theoretic stabilizer of `x` as a
  `ClosedSubgroupScheme` of `Spec H`.
* `TauCeti.SchemeAction.stabilizerHopfIdeal`: the defining Hopf ideal of `stabilizer G x`.
* `TauCeti.SchemeAction.quotientSpecStabilizerHopfIdealIso`: the group-scheme isomorphism
  `Spec (H ⧸ stabilizerHopfIdeal H x) ≅ stabilizer G x` over `Spec H`.
* `TauCeti.SchemeAction.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff`: the `A`-points cut
  out by `stabilizerHopfIdeal H x` are precisely the stabilizing `A`-points of `G`.
* `TauCeti.SchemeAction.fppfHomogeneousQuotientIsoOrbitPoints`: the fppf sheaf isomorphism
  `G / Stab_G(x) ≅ CommAlgCat.pointsSheaf (orbitOver G x)`.
* `TauCeti.SchemeAction.fppfHomogeneousQuotientIsoPointsSheaf`: for a reduced homogeneous scheme
  `X`, the fppf sheaf isomorphism `G / Stab_G(x) ≅ CommAlgCat.pointsSheaf X`.
* `TauCeti.SchemeAction.representedQuotientIsoOrbitOver` and
  `TauCeti.SchemeAction.representedQuotientIsoOfOrbitEqUniv`: scheme-level comparison with any
  scheme representing `G / Stab_G(x)`, with equivariance descent.
* `TauCeti.SchemeAction.exists_projectiveOrbit_iso_orbitOver` and
  `TauCeti.SchemeAction.exists_projectiveOrbit_iso_of_orbit_eq_univ`: scheme-level comparison
  with Chevalley's projective-orbit quotient model.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.e, Propositions 7.11 and 7.15, and §7.f.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

section HopfPointsBridge

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- Identify the convolution `A`-points of `H` with morphisms `Spec A ⟶ Spec H` over `Spec R`
into `((hopfSpec (CommRingCat.of R)).obj (op H)).X`, preserving group multiplication. -/
def hopfPointMulEquiv (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R) (H := H) A ≃*
      ((algSpec (CommRingCat.of R)).obj (op A) ⟶
        ((hopfSpec (CommRingCat.of R)).obj (op H)).X) :=
  ((_root_.CommHopfAlgCat.pointsFunctorIsoAlgebraPointsFunctor H).app A).groupIsoToMulEquiv

/-- `hopfPointMulEquiv` agrees with Mathlib's `Spec.mapMulEquiv`. -/
theorem hopfPointMulEquiv_apply (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    hopfPointMulEquiv H A g = AlgebraicGeometry.Spec.mapMulEquiv g :=
  _root_.CommHopfAlgCat.pointsFunctorIsoAlgebraPointsFunctor_hom_app_apply H A g

/-- The underlying scheme morphism of `hopfPointMulEquiv H A g` is `Spec.map g`. -/
theorem hopfPointMulEquiv_left (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    (hopfPointMulEquiv H A g).left =
      Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) := by
  rw [hopfPointMulEquiv_apply, AlgHom.toRingHom_eq_coe]
  exact TauCeti.CommHopfAlgCat.mapMulEquiv_left g

/-- The natural isomorphism identifying the universe-lifted convolution points presheaf of `H` with
the underlying presheaf of `CommAlgCat.pointsSheaf (Spec H)`. -/
def hopfPointsPresheafIsoPointsSheaf :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ≅
      (TauCeti.CommAlgCat.pointsSheaf ((hopfSpec (CommRingCat.of R)).obj (op H)).X).obj :=
  Functor.isoWhiskerRight
    (TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf H)
    uliftFunctor.{u + 1, u}

/-- Evaluating `hopfPointsPresheafIsoPointsSheaf` on a lifted convolution `A`-point converts it via
`hopfPointMulEquiv`. -/
theorem hopfPointsPresheafIsoPointsSheaf_hom_app_apply
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (hopfPointsPresheafIsoPointsSheaf H).hom.app A (ULift.up g) =
      ULift.up (hopfPointMulEquiv H A.unop.unop g) :=
  congrArg ULift.up
    ((TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf_hom_app_apply H A g).trans
      (hopfPointMulEquiv_apply H A.unop.unop g).symm)

/-- Push a scheme morphism `Spec H ⟶ Y` over `Spec R` forward to a morphism from the convolution
points presheaf of `H` to the affine fppf points sheaf of `Y`. -/
def hopfPointsToPointsSheaf {Y : Over (Spec (CommRingCat.of R))}
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
def pointsSheafHomOfHopfPoints {Y : Over (Spec (CommRingCat.of R))}
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

/-- The quotient morphism `Spec H ⟶ Q` induced by an fppf sheaf isomorphism identifying `G / N`
with the points sheaf of a representing scheme `Q`. -/
def quotientMapOfRep (I : HopfIdeal R H) {Q : Over (Spec (CommRingCat.of R))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ TauCeti.CommAlgCat.pointsSheaf Q) :
    ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Q :=
  pointsSheafHomOfHopfPoints H
    (_root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H I ≫ e.hom.hom)

/-- On convolution points, `quotientMapOfRep` agrees with the fppf quotient projection composed
with the representing isomorphism. -/
@[simp]
theorem hopfPointsToPointsSheaf_quotientMapOfRep (I : HopfIdeal R H)
    {Q : Over (Spec (CommRingCat.of R))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ TauCeti.CommAlgCat.pointsSheaf Q) :
    hopfPointsToPointsSheaf H (quotientMapOfRep H I e) =
      _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H I ≫ e.hom.hom :=
  hopfPointsToPointsSheaf_pointsSheafHomOfHopfPoints H _

/-- The scheme quotient morphism induced by any representing model of `G / N` is fppf locally
surjective on affine points sheaves. -/
instance isLocallySurjective_quotientMapOfRep (I : HopfIdeal R H)
    {Q : Over (Spec (CommRingCat.of R))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ TauCeti.CommAlgCat.pointsSheaf Q) :
    Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (TauCeti.CommAlgCat.pointsSheafMap (quotientMapOfRep H I e)).hom := by
  unfold quotientMapOfRep pointsSheafHomOfHopfPoints
  rw [TauCeti.CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm]
  have : IsIso e.hom.hom :=
    ((sheafToPresheaf (TauCeti.CommAlgCat.fppfTopology R) (Type (u + 1))).mapIso e).isIso_hom
  have : Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (_root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H I ≫ e.hom.hom) :=
    Presheaf.isLocallySurjective_comp (TauCeti.CommAlgCat.fppfTopology R) _ _
  exact Presheaf.isLocallySurjective_comp (TauCeti.CommAlgCat.fppfTopology R)
    (hopfPointsPresheafIsoPointsSheaf H).inv
    (_root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H I ≫ e.hom.hom)

end HopfPointsBridge

section StabilizerIdeal

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)
  {X : Over (Spec (CommRingCat.of R))}
  [ModObj ((hopfSpec (CommRingCat.of R)).obj (op H)).X X]
  (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X)

/-- The inclusion of the scheme-theoretic stabilizer of `x` into `Spec H`, bundled as a morphism
of group schemes over `Spec R`. -/
def stabilizerInclGrpHom :
    Grp.mk (stabilizer ((hopfSpec (CommRingCat.of R)).obj (op H)).X x) ⟶
      (hopfSpec (CommRingCat.of R)).obj (op H) :=
  Grp.homMk (stabilizer.incl ((hopfSpec (CommRingCat.of R)).obj (op H)).X x)

/-- The underlying `Over`-morphism of `stabilizerInclGrpHom` is `stabilizer.incl`. -/
@[simp]
theorem stabilizerInclGrpHom_hom_hom :
    (stabilizerInclGrpHom H x).hom.hom =
      stabilizer.incl ((hopfSpec (CommRingCat.of R)).obj (op H)).X x :=
  (rfl)

variable [IsClosedImmersion x.left]

instance : IsClosedImmersion (stabilizerInclGrpHom H x).hom.hom.left :=
  isClosedImmersion_orbitFiber_incl ((hopfSpec (CommRingCat.of R)).obj (op H)).X x x

/-- The scheme-theoretic stabilizer of `x` as a `ClosedSubgroupScheme` of `Spec H`. -/
def stabilizerClosedSubgroup :
    ClosedSubgroupScheme ((hopfSpec (CommRingCat.of R)).obj (op H)) :=
  ClosedSubgroupScheme.mk (stabilizerInclGrpHom H x)

/-- The unique Hopf ideal of `H` cutting out the scheme-theoretic stabilizer of `x`. -/
def stabilizerHopfIdeal : HopfIdeal R H :=
  OrderDual.ofDual
    ((TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup H).symm
      (stabilizerClosedSubgroup H x))

/-- The closed subgroup cut out by `stabilizerHopfIdeal H x` is `stabilizerClosedSubgroup H x`. -/
@[simp]
theorem quotientClosedSubgroup_stabilizerHopfIdeal :
    TauCeti.CommHopfAlgCat.quotientClosedSubgroup H (stabilizerHopfIdeal H x) =
      stabilizerClosedSubgroup H x :=
  TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup_apply_symm_apply H _

private theorem subobject_quotientSpecι_eq_stabilizerInclGrpHom :
    Subobject.mk (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x)) =
      Subobject.mk (stabilizerInclGrpHom H x) := by
  calc
    Subobject.mk (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))
        = (TauCeti.CommHopfAlgCat.quotientClosedSubgroup H (stabilizerHopfIdeal H x)).1 :=
          (TauCeti.CommHopfAlgCat.quotientClosedSubgroup_coe H _).symm
    _ = (stabilizerClosedSubgroup H x).1 :=
          congrArg Subtype.val (quotientClosedSubgroup_stabilizerHopfIdeal H x)
    _ = Subobject.mk (stabilizerInclGrpHom H x) :=
          ClosedSubgroupScheme.coe_mk (stabilizerInclGrpHom H x)

/-- The canonical isomorphism of group schemes over `Spec R` identifying the quotient Hopf
spectrum `Spec (H ⧸ stabilizerHopfIdeal H x)` with the scheme-theoretic stabilizer of `x`. -/
def quotientSpecStabilizerHopfIdealIso :
    TauCeti.CommHopfAlgCat.quotientSpec H (stabilizerHopfIdeal H x) ≅
      Grp.mk (stabilizer ((hopfSpec (CommRingCat.of R)).obj (op H)).X x) :=
  (Subobject.underlyingIso
      (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))).symm ≪≫
    Subobject.underlying.mapIso
      (eqToIso (subobject_quotientSpecι_eq_stabilizerInclGrpHom H x)) ≪≫
    Subobject.underlyingIso (stabilizerInclGrpHom H x)

/-- The isomorphism `quotientSpecStabilizerHopfIdealIso` intertwines the stabilizer inclusion
with the quotient closed-subgroup immersion. -/
@[reassoc (attr := simp)]
theorem quotientSpecStabilizerHopfIdealIso_hom_comp :
    (quotientSpecStabilizerHopfIdealIso H x).hom ≫ stabilizerInclGrpHom H x =
      TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x) := by
  have h1 : (Subobject.underlyingIso (stabilizerInclGrpHom H x)).hom ≫ stabilizerInclGrpHom H x =
      (Subobject.mk (stabilizerInclGrpHom H x)).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk (stabilizerInclGrpHom H x)
  have h2 : Subobject.underlying.map
        (eqToHom (subobject_quotientSpecι_eq_stabilizerInclGrpHom H x)) ≫
      (Subobject.mk (stabilizerInclGrpHom H x)).arrow =
      (Subobject.mk (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))).arrow := by
    rw [eqToHom_map]
    exact Subobject.arrow_congr _ _ (subobject_quotientSpecι_eq_stabilizerInclGrpHom H x)
  calc
    (quotientSpecStabilizerHopfIdealIso H x).hom ≫ stabilizerInclGrpHom H x
        = (Subobject.underlyingIso
            (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))).inv ≫
          Subobject.underlying.map
            (eqToHom (subobject_quotientSpecι_eq_stabilizerInclGrpHom H x)) ≫
          (Subobject.underlyingIso (stabilizerInclGrpHom H x)).hom ≫
          stabilizerInclGrpHom H x := by
            simp only [quotientSpecStabilizerHopfIdealIso, Iso.trans_hom, Iso.symm_hom,
              Functor.mapIso_hom, eqToIso.hom, Category.assoc]
    _ = (Subobject.underlyingIso
            (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))).inv ≫
          (Subobject.mk
            (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))).arrow := by
            rw [h1, h2]
    _ = TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x) :=
          Subobject.underlyingIso_arrow _

/-- The inverse of `quotientSpecStabilizerHopfIdealIso` intertwines the quotient closed-subgroup
immersion with the stabilizer inclusion. -/
@[reassoc (attr := simp)]
theorem quotientSpecStabilizerHopfIdealIso_inv_comp :
    (quotientSpecStabilizerHopfIdealIso H x).inv ≫
        TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x) =
      stabilizerInclGrpHom H x := by
  rw [← quotientSpecStabilizerHopfIdealIso_hom_comp H x, Iso.inv_hom_id_assoc]

/-- **Points of the stabilizer Hopf ideal.** Over every commutative `R`-algebra `A`, an `A`-point
of `Spec H` lies in the subgroup cut out by `stabilizerHopfIdeal H x` if and only if it stabilizes
`x`. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      hopfPointMulEquiv H A g ∈
        stabilizerPoints ((hopfSpec (CommRingCat.of R)).obj (op H)).X x
          ((algSpec (CommRingCat.of R)).obj (op A)) := by
  let I := stabilizerHopfIdeal H x
  let e := quotientSpecStabilizerHopfIdealIso H x
  rw [← stabilizer.exists_lift_iff, TauCeti.CommHopfAlgCat.quotientPointsSubgroup,
    MonoidHom.mem_range]
  have hdom : ∀ q : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.quotient H I) A,
      hopfPointMulEquiv H A (TauCeti.CommHopfAlgCat.quotientPointsHom H I A q) =
        hopfPointMulEquiv (_root_.CommHopfAlgCat.quotient H I) A q ≫
          (TauCeti.CommHopfAlgCat.quotientSpecι H I).hom.hom := fun q ↦ by
    apply Over.OverMorphism.ext
    have hleft : ((TauCeti.CommHopfAlgCat.quotientSpecι H I).hom.hom).left =
        Spec.map (CommRingCat.ofHom
          (_root_.CommHopfAlgCat.mkQuotient H I).hom.toAlgHom.toRingHom) := by
      rw [TauCeti.CommHopfAlgCat.quotientSpecι_def]
      rfl
    have hring : CommRingCat.ofHom
        (TauCeti.CommHopfAlgCat.quotientPointsHom H I A q).ofConv.toRingHom =
        CommRingCat.ofHom (_root_.CommHopfAlgCat.mkQuotient H I).hom.toAlgHom.toRingHom ≫
          CommRingCat.ofHom q.ofConv.toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext a
      rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
      rfl
    rw [Over.comp_left, hopfPointMulEquiv_left, hopfPointMulEquiv_left, hleft]
    exact (congrArg Spec.map hring).trans (Spec.map_comp _ _)
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨hopfPointMulEquiv (_root_.CommHopfAlgCat.quotient H I) A q ≫ e.hom.hom.hom, ?_⟩
    rw [Category.assoc]
    have hcomp : e.hom.hom.hom ≫
        stabilizer.incl ((hopfSpec (CommRingCat.of R)).obj (op H)).X x =
        (TauCeti.CommHopfAlgCat.quotientSpecι H I).hom.hom :=
      congrArg (fun f ↦ f.hom.hom) (quotientSpecStabilizerHopfIdealIso_hom_comp H x)
    rw [hcomp, ← hdom q]
  · rintro ⟨s, hs⟩
    let q : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.quotient H I) A :=
      (hopfPointMulEquiv (_root_.CommHopfAlgCat.quotient H I) A).symm (s ≫ e.inv.hom.hom)
    refine ⟨q, (hopfPointMulEquiv H A).injective ?_⟩
    rw [hdom q, MulEquiv.apply_symm_apply, Category.assoc]
    have hcomp : e.inv.hom.hom ≫
        (TauCeti.CommHopfAlgCat.quotientSpecι H I).hom.hom =
        stabilizer.incl ((hopfSpec (CommRingCat.of R)).obj (op H)).X x :=
      congrArg (fun f ↦ f.hom.hom) (quotientSpecStabilizerHopfIdealIso_inv_comp H x)
    rw [hcomp, hs]

/-- Over every commutative `R`-algebra `A`, two `A`-points of `Spec H` lie in the same left coset
of `stabilizerHopfIdeal H x` if and only if they have the same image under the orbit morphism. -/
theorem inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
    (A : CommAlgCat.{u} R) (g g' : HopfAlgebra.points (R := R) (H := H) A) :
    g⁻¹ * g' ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      hopfPointMulEquiv H A g ≫
          orbitMap ((hopfSpec (CommRingCat.of R)).obj (op H)).X x =
        hopfPointMulEquiv H A g' ≫
          orbitMap ((hopfSpec (CommRingCat.of R)).obj (op H)).X x := by
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff, map_mul, map_inv,
    inv_mul_mem_stabilizerPoints_iff]

/-- Smoothness of the quotient coordinate Hopf algebra `H ⧸ stabilizerHopfIdeal H x` is equivalent
to smoothness of the scheme-theoretic stabilizer `stabilizer (Spec H) x` over `Spec R`. -/
theorem smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff :
    smoothCommHopfAlgProperty R (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)) ↔
      Smooth (stabilizer ((hopfSpec (CommRingCat.of R)).obj (op H)).X x).hom := by
  rw [algebraSmooth_iff_smooth_hopfSpec, smoothAffineGroupSchemeProperty_iff]
  dsimp only
  let e : ((hopfSpec (CommRingCat.of R)).obj
      (op (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)))).X ≅
      stabilizer ((hopfSpec (CommRingCat.of R)).obj (op H)).X x :=
    (Grp.forget _).mapIso (quotientSpecStabilizerHopfIdealIso H x)
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  exact ⟨fun _ ↦ by rw [← Over.w e.inv]; infer_instance,
    fun _ ↦ by rw [← Over.w e.hom]; infer_instance⟩

/-- The orbit morphism `Spec H ⟶ X` descends to a morphism of fppf sheaves from the fppf
homogeneous quotient `G / Stab_G(x)` to `CommAlgCat.pointsSheaf X`. -/
def fppfHomogeneousQuotientToPointsSheaf :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ⟶
      TauCeti.CommAlgCat.pointsSheaf X :=
  (_root_.CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv H (stabilizerHopfIdeal H x) _).symm
    ⟨hopfPointsToPointsSheaf H (orbitMap ((hopfSpec (CommRingCat.of R)).obj (op H)).X x),
      fun A g n ↦ (hopfPointsToPointsSheaf_app_eq_iff H _ A (g * n.val) g).mpr <|
        (inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff H x A.unop.unop
          (g * n.val) g).mp (by
          simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using inv_mem n.property)⟩

/-- Restricting the descended orbit map along the quotient projection recovers the orbit map on
convolution points. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toPointsSheaf :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H (stabilizerHopfIdeal H x) ≫
        (fppfHomogeneousQuotientToPointsSheaf H x).hom =
      hopfPointsToPointsSheaf H (orbitMap ((hopfSpec (CommRingCat.of R)).obj (op H)).X x) :=
  _root_.CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_symm_apply H _ _ _ _

end StabilizerIdeal

section OrbitComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (.of k))}
  [ModObj ((hopfSpec (CommRingCat.of k)).obj (op H)).X X]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

local instance :
    LocallyOfFiniteType ((hopfSpec (CommRingCat.of k)).obj (op H)).X.hom :=
  (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance

local instance :
    CompactSpace ((hopfSpec (CommRingCat.of k)).obj (op H)).X.left := by
  rw [hopfSpec_obj_X_left]
  infer_instance

local instance :
    IsAffine ((hopfSpec (CommRingCat.of k)).obj (op H)).X.left := by
  rw [hopfSpec_obj_X_left]
  exact isAffine_Spec _

local instance [_root_.IsReduced H] :
    IsReduced ((hopfSpec (CommRingCat.of k)).obj (op H)).X.left := by
  rw [hopfSpec_obj_X_left, affine_isReduced_iff]
  infer_instance

/-- Over every `k`-algebra `A`, two `A`-points of `Spec H` have the same image under the orbit
projection `Spec H ⟶ orbitOver (Spec H) x` if and only if they lie in the same left coset of
`stabilizerHopfIdeal H x`. -/
theorem hopfPointsToPointsSheaf_orbitProjection_app_eq_iff
    (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g g' : HopfAlgebra.points (R := k) (H := H) A.unop.unop) :
    (hopfPointsToPointsSheaf H
        (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x)).app A (ULift.up g) =
      (hopfPointsToPointsSheaf H
        (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x)).app A (ULift.up g') ↔
      g⁻¹ * g' ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H
        (stabilizerHopfIdeal H x) A.unop.unop := by
  rw [hopfPointsToPointsSheaf_app_eq_iff,
    ← cancel_mono (orbitInclusion ((hopfSpec (CommRingCat.of k)).obj (op H)).X x),
    Category.assoc, Category.assoc, orbitProjection_inclusion,
    inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff]

/-- The orbit projection `Spec H ⟶ orbitOver (Spec H) x` descends to a morphism of fppf sheaves
from `G / Stab_G(x)` to `CommAlgCat.pointsSheaf (orbitOver (Spec H) x)`. -/
def fppfHomogeneousQuotientToOrbitPoints :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ⟶
      TauCeti.CommAlgCat.pointsSheaf
        (orbitOver ((hopfSpec (CommRingCat.of k)).obj (op H)).X x) :=
  (_root_.CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv H (stabilizerHopfIdeal H x) _).symm
    ⟨hopfPointsToPointsSheaf H (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x),
      fun A g n ↦ (hopfPointsToPointsSheaf_orbitProjection_app_eq_iff H x A (g * n.val) g).mpr (by
        simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using inv_mem n.property)⟩

/-- Restricting `fppfHomogeneousQuotientToOrbitPoints` along the quotient projection recovers the
orbit projection on convolution points. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toOrbitPoints :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H (stabilizerHopfIdeal H x) ≫
        (fppfHomogeneousQuotientToOrbitPoints H x).hom =
      hopfPointsToPointsSheaf H
        (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x) :=
  _root_.CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_symm_apply H _ _ _ _

/-- Composing the descended orbit projection with the orbit inclusion recovers the descended orbit
morphism into the ambient scheme `X`. -/
@[reassoc]
theorem fppfHomogeneousQuotientToOrbitPoints_comp_orbitInclusion :
    fppfHomogeneousQuotientToOrbitPoints H x ≫
        TauCeti.CommAlgCat.pointsSheafMap
          (orbitInclusion ((hopfSpec (CommRingCat.of k)).obj (op H)).X x) =
      fppfHomogeneousQuotientToPointsSheaf H x := by
  apply _root_.CommHopfAlgCat.fppfHomogeneousQuotient_hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    fppfHomogeneousQuotientProjection_comp_toOrbitPoints,
    fppfHomogeneousQuotientProjection_comp_toPointsSheaf,
    ← hopfPointsToPointsSheaf_comp, orbitProjection_inclusion]

/-- **Orbit schemes represent fppf homogeneous quotients.** For a reduced affine group of finite
type over an algebraically closed field acting on a finite-type scheme, the descended orbit
projection `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf (orbitOver G x)` is an isomorphism of fppf
sheaves. -/
instance isIso_fppfHomogeneousQuotientToOrbitPoints [_root_.IsReduced H] :
    IsIso (fppfHomogeneousQuotientToOrbitPoints H x) := by
  have hflat : Flat (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x).left := by
    rw [orbitProjection_left]
    infer_instance
  have hsurj :
      Surjective (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x).left := by
    rw [orbitProjection_left]
    infer_instance
  have hfp : LocallyOfFinitePresentation
      (orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x).left := by
    rw [orbitProjection_left]
    infer_instance
  exact _root_.CommHopfAlgCat.isIso_fppfHomogeneousQuotientHomEquiv_symm H _ _ _ _
    fun A g g' h ↦ (hopfPointsToPointsSheaf_orbitProjection_app_eq_iff H x A g g').mp h

/-- **Orbit-map comparison for any orbit.** The canonical isomorphism of fppf sheaves
`G / Stab_G(x) ≅ CommAlgCat.pointsSheaf (orbitOver G x)`. -/
def fppfHomogeneousQuotientIsoOrbitPoints [_root_.IsReduced H] :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf
        (orbitOver ((hopfSpec (CommRingCat.of k)).obj (op H)).X x) :=
  asIso (fppfHomogeneousQuotientToOrbitPoints H x)

/-- The forward direction of `fppfHomogeneousQuotientIsoOrbitPoints` is
`fppfHomogeneousQuotientToOrbitPoints`. -/
@[simp]
theorem fppfHomogeneousQuotientIsoOrbitPoints_hom [_root_.IsReduced H] :
    (fppfHomogeneousQuotientIsoOrbitPoints H x).hom =
      fppfHomogeneousQuotientToOrbitPoints H x :=
  (rfl)

/-- **Homogeneous orbit comparison.** When `X` is reduced and `orbit G x = Set.univ`, the
descended orbit map `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf
sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) := by
  have : IsIso (orbitInclusion ((hopfSpec (CommRingCat.of k)).obj (op H)).X x) :=
    isIso_orbitInclusion_of_orbit_eq_univ _ x h
  rw [← fppfHomogeneousQuotientToOrbitPoints_comp_orbitInclusion H x]
  infer_instance

/-- **Homogeneous orbit comparison from rational-point transitivity.** When `X` is reduced and
`G(k)` acts transitively on `X(k)`, the descended orbit map
`G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_forall_exists_smul [_root_.IsReduced H]
    [IsReduced X.left]
    (htrans : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ ((hopfSpec (CommRingCat.of k)).obj (op H)).X,
        g • x = y) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) :=
  isIso_fppfHomogeneousQuotientToPointsSheaf H x
    ((orbit_eq_univ_iff_forall_exists_smul _ x).mpr htrans)

/-- **Homogeneous orbit comparison for smooth targets.** When `X` is smooth over `Spec k` and
`orbit G x = Set.univ`, the descended orbit map `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is
an isomorphism of fppf sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_smooth [_root_.IsReduced H]
    [Smooth X.hom]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) := by
  have : IsReduced X.left := X.hom.isReduced_of_smooth
  exact isIso_fppfHomogeneousQuotientToPointsSheaf H x h

/-- **The canonical fppf quotient isomorphism for a reduced homogeneous scheme:**
`G / Stab_G(x) ≅ CommAlgCat.pointsSheaf X`. -/
def fppfHomogeneousQuotientIsoPointsSheaf [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ) :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf X :=
  have : IsIso (fppfHomogeneousQuotientToPointsSheaf H x) :=
    isIso_fppfHomogeneousQuotientToPointsSheaf H x h
  asIso (fppfHomogeneousQuotientToPointsSheaf H x)

/-- The forward direction of `fppfHomogeneousQuotientIsoPointsSheaf` is
`fppfHomogeneousQuotientToPointsSheaf`. -/
@[simp]
theorem fppfHomogeneousQuotientIsoPointsSheaf_hom [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ) :
    (fppfHomogeneousQuotientIsoPointsSheaf H x h).hom =
      fppfHomogeneousQuotientToPointsSheaf H x :=
  (rfl)

/-- For a reduced finite-type affine group acting transitively on a reduced finite-type scheme
`X` over an algebraically closed field, the orbit morphism `Spec H ⟶ X` is smooth if and only if
the coordinate Hopf algebra `H ⧸ stabilizerHopfIdeal H x` of the stabilizer is smooth over `k`. -/
theorem smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal
    [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ) :
    Smooth (orbitMap ((hopfSpec (CommRingCat.of k)).obj (op H)).X x).left ↔
      smoothCommHopfAlgProperty k
        (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)) :=
  (smooth_orbitMap_iff_of_orbit_eq_univ _ x h).trans
    (smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff H x).symm

/-- **Scheme-level comparison for any orbit.** Every scheme `Q` over `Spec k` representing
`G / Stab_G(x)` is canonically isomorphic over `Spec k` to the orbit scheme `orbitOver G x`. -/
def representedQuotientIsoOrbitOver [_root_.IsReduced H]
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    Q ≅ orbitOver ((hopfSpec (CommRingCat.of k)).obj (op H)).X x :=
  TauCeti.CommAlgCat.pointsSheafIsoEquiv.symm
    (e.symm ≪≫ fppfHomogeneousQuotientIsoOrbitPoints H x)

/-- The scheme isomorphism `representedQuotientIsoOrbitOver` intertwines the quotient map
`Spec H ⟶ Q` with the orbit projection `Spec H ⟶ orbitOver (Spec H) x`. -/
@[reassoc (attr := simp)]
theorem quotientMapOfRep_comp_representedQuotientIsoOrbitOver_hom [_root_.IsReduced H]
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    quotientMapOfRep H (stabilizerHopfIdeal H x) e ≫
        (representedQuotientIsoOrbitOver H x e).hom =
      orbitProjection ((hopfSpec (CommRingCat.of k)).obj (op H)).X x := by
  apply hopfPointsToPointsSheaf_injective H
  rw [hopfPointsToPointsSheaf_comp, hopfPointsToPointsSheaf_quotientMapOfRep]
  have hmap :
      (TauCeti.CommAlgCat.pointsSheafMap
          (representedQuotientIsoOrbitOver H x e).hom).hom =
        e.inv.hom ≫ (fppfHomogeneousQuotientToOrbitPoints H x).hom :=
    congrArg (fun α : TauCeti.CommAlgCat.pointsSheaf Q ⟶ _ ↦ α.hom)
      (TauCeti.CommAlgCat.pointsSheafMap_pointsSheafIsoEquiv_symm_hom
        (e.symm ≪≫ fppfHomogeneousQuotientIsoOrbitPoints H x))
  rw [hmap, Category.assoc, ← Category.assoc e.hom.hom]
  have he : e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
    congrArg (fun α : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ⟶
        _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ↦ α.hom)
      e.hom_inv_id
  rw [he, Category.id_comp, fppfHomogeneousQuotientProjection_comp_toOrbitPoints]

/-- When a representing quotient scheme `Q` carries a `G`-action making the quotient map
equivariant, the isomorphism `Q ≅ orbitOver G x` is `G`-equivariant. -/
theorem isModHom_representedQuotientIsoOrbitOver_hom [_root_.IsReduced H]
    {Q : Over (Spec (.of k))}
    [ModObj ((hopfSpec (CommRingCat.of k)).obj (op H)).X Q]
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q)
    (hq : μ[((hopfSpec (CommRingCat.of k)).obj (op H)).X] ≫
        quotientMapOfRep H (stabilizerHopfIdeal H x) e =
      ((hopfSpec (CommRingCat.of k)).obj (op H)).X ◁
          quotientMapOfRep H (stabilizerHopfIdeal H x) e ≫
        γ[((hopfSpec (CommRingCat.of k)).obj (op H)).X,Q]) :
    IsModHom ((hopfSpec (CommRingCat.of k)).obj (op H)).X
      (representedQuotientIsoOrbitOver H x e).hom := by
  refine TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_mul_comp
    (quotientMapOfRep H (stabilizerHopfIdeal H x) e) hq
    (representedQuotientIsoOrbitOver H x e).hom ?_
  rw [quotientMapOfRep_comp_representedQuotientIsoOrbitOver_hom]
  exact mul_orbitProjection _ x

/-- **Scheme-level homogeneous orbit comparison.** Every scheme `Q` over `Spec k` representing
`G / Stab_G(x)` is canonically isomorphic over `Spec k` to a reduced homogeneous scheme `X`. -/
def representedQuotientIsoOfOrbitEqUniv [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ)
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    Q ≅ X :=
  TauCeti.CommAlgCat.pointsSheafIsoEquiv.symm
    (e.symm ≪≫ fppfHomogeneousQuotientIsoPointsSheaf H x h)

/-- The scheme isomorphism `representedQuotientIsoOfOrbitEqUniv` intertwines the quotient map
`Spec H ⟶ Q` with the orbit morphism `Spec H ⟶ X`. -/
@[reassoc (attr := simp)]
theorem quotientMapOfRep_comp_representedQuotientIsoOfOrbitEqUniv_hom [_root_.IsReduced H]
    [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ)
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    quotientMapOfRep H (stabilizerHopfIdeal H x) e ≫
        (representedQuotientIsoOfOrbitEqUniv H x h e).hom =
      orbitMap ((hopfSpec (CommRingCat.of k)).obj (op H)).X x := by
  apply hopfPointsToPointsSheaf_injective H
  rw [hopfPointsToPointsSheaf_comp, hopfPointsToPointsSheaf_quotientMapOfRep]
  have hmap :
      (TauCeti.CommAlgCat.pointsSheafMap
          (representedQuotientIsoOfOrbitEqUniv H x h e).hom).hom =
        e.inv.hom ≫ (fppfHomogeneousQuotientToPointsSheaf H x).hom :=
    congrArg (fun α : TauCeti.CommAlgCat.pointsSheaf Q ⟶ _ ↦ α.hom)
      (TauCeti.CommAlgCat.pointsSheafMap_pointsSheafIsoEquiv_symm_hom
        (e.symm ≪≫ fppfHomogeneousQuotientIsoPointsSheaf H x h))
  rw [hmap, Category.assoc, ← Category.assoc e.hom.hom]
  have he : e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
    congrArg (fun α : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ⟶
        _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ↦ α.hom)
      e.hom_inv_id
  rw [he, Category.id_comp, fppfHomogeneousQuotientProjection_comp_toPointsSheaf]

/-- When a representing quotient scheme `Q` carries a `G`-action making the quotient map
equivariant, the isomorphism `Q ≅ X` onto a reduced homogeneous scheme `X` is `G`-equivariant. -/
theorem isModHom_representedQuotientIsoOfOrbitEqUniv_hom [_root_.IsReduced H]
    [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ)
    {Q : Over (Spec (.of k))}
    [ModObj ((hopfSpec (CommRingCat.of k)).obj (op H)).X Q]
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q)
    (hq : μ[((hopfSpec (CommRingCat.of k)).obj (op H)).X] ≫
        quotientMapOfRep H (stabilizerHopfIdeal H x) e =
      ((hopfSpec (CommRingCat.of k)).obj (op H)).X ◁
          quotientMapOfRep H (stabilizerHopfIdeal H x) e ≫
        γ[((hopfSpec (CommRingCat.of k)).obj (op H)).X,Q]) :
    IsModHom ((hopfSpec (CommRingCat.of k)).obj (op H)).X
      (representedQuotientIsoOfOrbitEqUniv H x h e).hom := by
  refine TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_mul_comp
    (quotientMapOfRep H (stabilizerHopfIdeal H x) e) hq
    (representedQuotientIsoOfOrbitEqUniv H x h e).hom ?_
  rw [quotientMapOfRep_comp_representedQuotientIsoOfOrbitEqUniv_hom]
  exact mul_orbitMap _ x

section ProjectiveOrbitComparison

attribute [local instance] Comodule.exteriorPower

private def projectiveOrbitPointsSheafIsoPointsSheaf
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
    (m : M) (hm : Module.IsUnimodular k m) :
    Comodule.projectiveOrbitPointsSheaf (H := H) m hm ≅
      TauCeti.CommAlgCat.pointsSheaf (Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm)) :=
  (fullyFaithfulSheafToPresheaf (TauCeti.CommAlgCat.fppfTopology k) (Type (u + 1))).preimageIso
    (eqToIso (Comodule.projectiveOrbitPointsSheaf_obj (H := H) m hm))

omit [LocallyOfFiniteType X.hom] [CompactSpace X.left] in
private theorem quotientMapOfRep_projectiveOrbit_left
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
    [_root_.IsReduced H] (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A) =
        QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (Comodule.matrixCoefficient (C := H) φ m) =
            c * g.ofConv (Comodule.matrixCoefficient (C := H) φ m)) :
    (quotientMapOfRep H (stabilizerHopfIdeal H x)
        (Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints
            (stabilizerHopfIdeal H x) m hm hcoset ≪≫
          projectiveOrbitPointsSheafIsoPointsSheaf H m hm)).left =
      eqToHom (hopfSpec_obj_X_left k H) ≫ Comodule.toProjectiveOrbit (H := H) m hm := by
  let p : ((hopfSpec (CommRingCat.of k)).obj (op H)).X ⟶
      Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) :=
    Over.homMk (eqToHom (hopfSpec_obj_X_left k H) ≫ Comodule.toProjectiveOrbit (H := H) m hm) (by
      rw [Category.assoc]
      exact (congrArg (eqToHom (hopfSpec_obj_X_left k H) ≫ ·)
        (Comodule.toProjectiveOrbit_projectiveOrbitToSpec (H := H) m hm)).trans
        (hopfSpec_obj_X_hom k H).symm)
  suffices h : quotientMapOfRep H (stabilizerHopfIdeal H x)
      (Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints
          (stabilizerHopfIdeal H x) m hm hcoset ≪≫
        projectiveOrbitPointsSheafIsoPointsSheaf H m hm) = p from congrArg Over.Hom.left h
  apply hopfPointsToPointsSheaf_injective H
  rw [hopfPointsToPointsSheaf_quotientMapOfRep, Iso.trans_hom,
    Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom]
  have hcomp :
      _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H (stabilizerHopfIdeal H x) ≫
          (Comodule.fppfHomogeneousQuotientToProjectiveOrbitPoints
              (stabilizerHopfIdeal H x) m hm hcoset ≫
            (projectiveOrbitPointsSheafIsoPointsSheaf H m hm).hom).hom =
        Comodule.toProjectiveOrbitPoints (H := H) m hm ≫
          (projectiveOrbitPointsSheafIsoPointsSheaf H m hm).hom.hom := by
    rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
      Comodule.fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints]
  rw [hcomp]
  ext A ⟨g⟩
  let g' : HopfAlgebra.points (R := k) (H := H) A.unop.unop := g
  let y : (((algSpec (CommRingCat.of k)).op ⋙
      yoneda.obj (Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm))) ⋙
      uliftFunctor.{u + 1, u}).obj A :=
    ULift.up (Over.homMk
      (Spec.map (CommRingCat.ofHom g'.ofConv.toRingHom) ≫
        Comodule.toProjectiveOrbit (H := H) m hm)
      (Comodule.SpecMap_toProjectiveOrbit_projectiveOrbitToSpec m hm g'.ofConv))
  have hcast :
      (projectiveOrbitPointsSheafIsoPointsSheaf H m hm).hom.hom.app A
          ((Comodule.toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up g')) = y := by
    have hcast_eq :
        ∀ {F G : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)} (h : F = G) (z : G.obj A),
          (eqToHom h).app A (h.symm ▸ z) = z := by
      rintro F _ rfl z
      rfl
    rw [Comodule.toProjectiveOrbitPoints_app_apply]
    have hpre :
        (projectiveOrbitPointsSheafIsoPointsSheaf H m hm).hom.hom =
          eqToHom (Comodule.projectiveOrbitPointsSheaf_obj (H := H) m hm) :=
      (fullyFaithfulSheafToPresheaf (TauCeti.CommAlgCat.fppfTopology k)
        (Type (u + 1))).map_preimage _
    exact (congrArg
      (fun α ↦ α.app A ((Comodule.projectiveOrbitPointsSheaf_obj (H := H) m hm).symm ▸ y))
      hpre).trans (hcast_eq (Comodule.projectiveOrbitPointsSheaf_obj (H := H) m hm) y)
  have hlhs :
      (Comodule.toProjectiveOrbitPoints (H := H) m hm ≫
        (projectiveOrbitPointsSheafIsoPointsSheaf H m hm).hom.hom).app A (ULift.up g') = y := by
    rw [NatTrans.comp_app, types_comp_apply]
    exact hcast
  have hrhs : y = ULift.up (hopfPointMulEquiv H A.unop.unop g' ≫ p) := by
    refine congrArg ULift.up (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hopfPointMulEquiv_left]
    exact congrArg (Spec.map (CommRingCat.ofHom g'.ofConv.toRingHom) ≫ ·)
      (Category.id_comp (Comodule.toProjectiveOrbit (H := H) m hm)).symm
  exact (hlhs.trans hrhs).trans (hopfPointsToPointsSheaf_app_apply H p A g').symm

/-- **Every orbit scheme is isomorphic to Chevalley's projective-orbit quotient model.** For a
reduced finite-type affine group `Spec H` acting on a finite-type scheme over an algebraically
closed field, the orbit scheme `orbitOver (Spec H) x` is isomorphic over `Spec k` to a projective
orbit scheme representing `G / Stab_G(x)`, intertwining `toProjectiveOrbit` and `toOrbit`. -/
theorem exists_projectiveOrbit_iso_orbitOver [_root_.IsReduced H] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅
        orbitOver ((hopfSpec (CommRingCat.of k)).obj (op H)).X x),
      eqToHom (hopfSpec_obj_X_left k H) ≫
          Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left =
        toOrbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x := by
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, m, hm, hcoset⟩ :=
    (stabilizerHopfIdeal H x).exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u,
      u} (IsNoetherian.noetherian (stabilizerHopfIdeal H x).toIdeal)
  let _ : Module.Finite k V := hV
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let isoQ :=
    Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints
        (stabilizerHopfIdeal H x) m hm hcoset ≪≫
      projectiveOrbitPointsSheafIsoPointsSheaf H m hm
  let e := representedQuotientIsoOrbitOver H x isoQ
  refine ⟨⋀[k]^n V, inferInstance, inferInstance, inferInstance, inferInstance, m, hm, e, ?_⟩
  have hcomp := congrArg Over.Hom.left
    (quotientMapOfRep_comp_representedQuotientIsoOrbitOver_hom H x isoQ)
  rw [Over.comp_left, quotientMapOfRep_projectiveOrbit_left H x m hm hcoset,
    Category.assoc, orbitProjection_left] at hcomp
  exact hcomp

/-- **Every reduced homogeneous space is isomorphic to Chevalley's projective-orbit quotient
model.** In particular, every reduced finite-type homogeneous scheme `X` for a reduced finite-type
affine group `Spec H` over an algebraically closed field is isomorphic over `Spec k` to a
projective orbit scheme representing `G / Stab_G(x)`, intertwining `toProjectiveOrbit` and the
orbit morphism `Spec H ⟶ X`. -/
theorem exists_projectiveOrbit_iso_of_orbit_eq_univ [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((hopfSpec (CommRingCat.of k)).obj (op H)).X x = Set.univ) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅ X),
      eqToHom (hopfSpec_obj_X_left k H) ≫
          Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left =
        (orbitMap ((hopfSpec (CommRingCat.of k)).obj (op H)).X x).left := by
  obtain ⟨M, _, _, _, _, m, hm, e, he⟩ := exists_projectiveOrbit_iso_orbitOver H x
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    e ≪≫ orbitInclusionIso _ x h, ?_⟩
  calc
    eqToHom (hopfSpec_obj_X_left k H) ≫
        Comodule.toProjectiveOrbit (H := H) m hm ≫ (e ≪≫ orbitInclusionIso _ x h).hom.left
        = (eqToHom (hopfSpec_obj_X_left k H) ≫
            Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left) ≫
          (orbitInclusionIso _ x h).hom.left := by
            simp only [Iso.trans_hom, Over.comp_left, Category.assoc]
    _ = (orbitMap ((hopfSpec (CommRingCat.of k)).obj (op H)).X x).left := by
          rw [he, orbitInclusionIso_hom, orbitInclusion_left, toOrbit_ι]

end ProjectiveOrbitComparison

end OrbitComparison

end TauCeti.SchemeAction
