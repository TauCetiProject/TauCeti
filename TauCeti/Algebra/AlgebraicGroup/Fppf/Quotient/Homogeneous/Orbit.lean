/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.Category.CommAlgCat.PointsSheaf
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
open TauCeti.CommHopfAlgCat
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

section StabilizerIdeal

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)
  {X : Over (Spec (CommRingCat.of R))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X]
  (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X)

/-- The inclusion of the scheme-theoretic stabilizer of `x` into `Spec H`, bundled as a morphism
of group schemes over `Spec R`. -/
def stabilizerInclGrpHom :
    Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) ⟶
      (hopfSpec (CommRingCat.of R)).obj (op H) :=
  (Grp.homMk (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) :
    Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) ⟶
      Grp.mk ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))))

/-- The underlying `Over`-morphism of `stabilizerInclGrpHom` is `stabilizer.incl`. -/
@[simp]
theorem stabilizerInclGrpHom_hom_hom :
    (stabilizerInclGrpHom H x).hom.hom =
      stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
  (rfl)

variable [IsClosedImmersion x.left]

instance : IsClosedImmersion (stabilizerInclGrpHom H x).hom.hom.left :=
  isClosedImmersion_orbitFiber_incl
    ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x x

/-- The scheme-theoretic stabilizer of `x` as a `ClosedSubgroupScheme` of `Spec H`. -/
def stabilizerClosedSubgroup :
    ClosedSubgroupScheme ((hopfSpec (CommRingCat.of R)).obj (op H)) :=
  ClosedSubgroupScheme.mk (stabilizerInclGrpHom H x)

/-- The unique Hopf ideal of `H` cutting out the scheme-theoretic stabilizer of `x`. -/
def stabilizerHopfIdeal : HopfIdeal R H :=
  OrderDual.ofDual
    ((TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup H).symm
      (stabilizerClosedSubgroup H x))

private theorem subobject_quotientSpecι_eq_stabilizerInclGrpHom :
    Subobject.mk (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x)) =
      Subobject.mk (stabilizerInclGrpHom H x) := by
  calc
    Subobject.mk (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x))
        = (TauCeti.CommHopfAlgCat.quotientClosedSubgroup H (stabilizerHopfIdeal H x)).val :=
          (TauCeti.CommHopfAlgCat.quotientClosedSubgroup_coe H _).symm
    _ = (stabilizerClosedSubgroup H x).val :=
          congrArg Subtype.val
            (TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup_apply_symm_apply H
              (stabilizerClosedSubgroup H x))
    _ = Subobject.mk (stabilizerInclGrpHom H x) :=
          ClosedSubgroupScheme.coe_mk (stabilizerInclGrpHom H x)

/-- The canonical isomorphism of group schemes over `Spec R` identifying the quotient Hopf
spectrum `Spec (H ⧸ stabilizerHopfIdeal H x)` with the scheme-theoretic stabilizer of `x`. -/
def quotientSpecStabilizerHopfIdealIso :
    TauCeti.CommHopfAlgCat.quotientSpec H (stabilizerHopfIdeal H x) ≅
      Grp.mk (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) :=
  Subobject.isoOfMkEqMk _ _ (subobject_quotientSpecι_eq_stabilizerInclGrpHom H x)

/-- The isomorphism `quotientSpecStabilizerHopfIdealIso` intertwines the stabilizer inclusion
with the quotient closed-subgroup immersion. -/
@[reassoc (attr := simp)]
theorem quotientSpecStabilizerHopfIdealIso_hom_comp :
    (quotientSpecStabilizerHopfIdealIso H x).hom ≫ stabilizerInclGrpHom H x =
      TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x) := by
  rw [quotientSpecStabilizerHopfIdealIso, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]

/-- The inverse of `quotientSpecStabilizerHopfIdealIso` intertwines the quotient closed-subgroup
immersion with the stabilizer inclusion. -/
@[reassoc (attr := simp)]
theorem quotientSpecStabilizerHopfIdealIso_inv_comp :
    (quotientSpecStabilizerHopfIdealIso H x).inv ≫
        TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x) =
      stabilizerInclGrpHom H x := by
  rw [← quotientSpecStabilizerHopfIdealIso_hom_comp H x, Iso.inv_hom_id_assoc]

private def quotientSpecιAsOver (I : HopfIdeal R H) :
    (Spec (CommRingCat.of (_root_.CommHopfAlgCat.quotient H I))).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) :=
  (TauCeti.CommHopfAlgCat.quotientSpecι H I).hom.hom

private theorem mapMulEquiv_quotientPointsHom
    (I : HopfIdeal R H) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.quotient H I) A) :
    Spec.mapMulEquiv (quotientPointsHom H I A q) =
      Spec.mapMulEquiv q ≫ quotientSpecιAsOver H I := by
  have h := mapMulEquiv_mapDomain A (_root_.CommHopfAlgCat.mkQuotient H I).hom q
  have hq : quotientPointsHom H I A q =
      BialgHom.mapDomain (_root_.CommHopfAlgCat.mkQuotient H I).hom q :=
    (_root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
      (_root_.CommHopfAlgCat.mkQuotient H I) A q).trans
      (BialgHom.mapDomain_apply (_root_.CommHopfAlgCat.mkQuotient H I).hom q).symm
  rw [hq]
  refine h.trans (congrArg (Spec.mapMulEquiv q ≫ ·) (Over.OverMorphism.ext ?_))
  rw [quotientSpecιAsOver, quotientSpecι_def]
  rfl

/-- **Points of the stabilizer Hopf ideal.** Over every commutative `R`-algebra `A`, an `A`-point
of `Spec H` lies in the subgroup cut out by `stabilizerHopfIdeal H x` if and only if it stabilizes
`x`. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      Spec.mapMulEquiv g ∈
        stabilizerPoints ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x
          ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) := by
  let I := stabilizerHopfIdeal H x
  let e := quotientSpecStabilizerHopfIdealIso H x
  let eHom : (Spec (CommRingCat.of (_root_.CommHopfAlgCat.quotient H I))).asOver
        (Spec (CommRingCat.of R)) ⟶
      stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
    e.hom.hom.hom
  let eInv : stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x ⟶
      (Spec (CommRingCat.of (_root_.CommHopfAlgCat.quotient H I))).asOver
        (Spec (CommRingCat.of R)) :=
    e.inv.hom.hom
  have heHom : eHom ≫
      stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
      quotientSpecιAsOver H I :=
    Over.OverMorphism.ext <| congrArg (fun f ↦ f.hom.hom.left)
      (quotientSpecStabilizerHopfIdealIso_hom_comp H x)
  have heInv : eInv ≫ quotientSpecιAsOver H I =
      stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
    Over.OverMorphism.ext <| congrArg (fun f ↦ f.hom.hom.left)
      (quotientSpecStabilizerHopfIdealIso_inv_comp H x)
  rw [← stabilizer.exists_lift_iff, TauCeti.CommHopfAlgCat.quotientPointsSubgroup,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨Spec.mapMulEquiv q ≫ eHom, ?_⟩
    rw [Category.assoc, heHom, ← mapMulEquiv_quotientPointsHom H I A q]
  · rintro ⟨s, hs⟩
    let q : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.quotient H I) A :=
      Spec.mapMulEquiv.symm (s ≫ eInv)
    refine ⟨q, Spec.mapMulEquiv.injective ?_⟩
    rw [mapMulEquiv_quotientPointsHom H I A q, MulEquiv.apply_symm_apply, Category.assoc,
      heInv, hs]

/-- Over every commutative `R`-algebra `A`, two `A`-points of `Spec H` lie in the same left coset
of `stabilizerHopfIdeal H x` if and only if they have the same image under the orbit morphism. -/
theorem inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
    (A : CommAlgCat.{u} R) (g g' : HopfAlgebra.points (R := R) (H := H) A) :
    g⁻¹ * g' ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      Spec.mapMulEquiv g ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
        Spec.mapMulEquiv g' ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x := by
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff, map_mul, map_inv,
    inv_mul_mem_stabilizerPoints_iff]

/-- Smoothness of the quotient coordinate Hopf algebra `H ⧸ stabilizerHopfIdeal H x` is equivalent
to smoothness of the scheme-theoretic stabilizer `stabilizer (Spec H) x` over `Spec R`. -/
theorem smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff :
    smoothCommHopfAlgProperty R (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)) ↔
      Smooth (stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).hom := by
  rw [algebraSmooth_iff_smooth_hopfSpec, smoothAffineGroupSchemeProperty_iff]
  dsimp only
  let e : ((hopfSpec (CommRingCat.of R)).obj
      (op (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)))).X ≅
      stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
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
    ⟨_root_.CommHopfAlgCat.specPointsHomEquiv H X
        (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x),
      fun A g n ↦ by
        rw [_root_.CommHopfAlgCat.specPointsHomEquiv_apply_app_apply,
          _root_.CommHopfAlgCat.specPointsHomEquiv_apply_app_apply]
        exact congrArg ULift.up <|
          ((inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff H x A.unop.unop
            g (g * n.val)).mp (by simpa only [inv_mul_cancel_left] using n.property)).symm⟩

/-- Restricting the descended orbit map along the quotient projection recovers the orbit map on
convolution points. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toPointsSheaf :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H (stabilizerHopfIdeal H x) ≫
        (fppfHomogeneousQuotientToPointsSheaf H x).hom =
      _root_.CommHopfAlgCat.specPointsHomEquiv H X
        (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) :=
  _root_.CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_symm_apply H _ _ _ _

end StabilizerIdeal

section OrbitComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (.of k))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) X]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

local instance :
    LocallyOfFiniteType ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom :=
  (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance

local instance :
    CompactSpace ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of H)))

local instance :
    IsAffine ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  isAffine_Spec _

local instance [_root_.IsReduced H] :
    IsReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  (affine_isReduced_iff (CommRingCat.of H)).mpr inferInstance

omit [IsAlgClosed k] in
private theorem mapMulEquiv_comp_orbitProjection_eq_iff
    (A : CommAlgCat.{u} k) (g g' : HopfAlgebra.points (R := k) (H := H) A) :
    Spec.mapMulEquiv g ≫
        orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x =
      Spec.mapMulEquiv g' ≫
        orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x ↔
      g⁻¹ * g' ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H
        (stabilizerHopfIdeal H x) A := by
  rw [← cancel_mono (orbitInclusion ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x),
    Category.assoc, Category.assoc, orbitProjection_inclusion,
    inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff]

local instance [_root_.IsReduced H] :
    Sheaf.IsLocallySurjective
      ((TauCeti.CommAlgCat.pointsSheafFunctor k).map
        (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x)) := by
  have : Flat
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left := by
    rw [orbitProjection_left]; infer_instance
  have : Surjective
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left := by
    rw [orbitProjection_left]; infer_instance
  have : LocallyOfFinitePresentation
      (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left := by
    rw [orbitProjection_left]; infer_instance
  exact TauCeti.CommAlgCat.isLocallySurjective_pointsSheafFunctor_map _

/-- **Orbit-map comparison for any orbit.** For a reduced affine group of finite type over an
algebraically closed field acting on a finite-type scheme, the descended orbit projection gives
an isomorphism of fppf sheaves `G / Stab_G(x) ≅ CommAlgCat.pointsSheaf (orbitOver G x)`. -/
def fppfHomogeneousQuotientIsoOrbitPoints [_root_.IsReduced H] :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf
        (orbitOver ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x) :=
  _root_.CommHopfAlgCat.fppfHomogeneousQuotientIsoPointsSheaf H (stabilizerHopfIdeal H x)
    (orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x)
    (fun A g n ↦ ((mapMulEquiv_comp_orbitProjection_eq_iff H x A g (g * n.val)).mpr (by
      simpa only [inv_mul_cancel_left] using n.property)).symm)
    (fun A g g' h ↦ (mapMulEquiv_comp_orbitProjection_eq_iff H x A g g').mp h)

/-- Under `fppfHomogeneousQuotientIsoOrbitPoints`, `representedQuotientProjection` is the orbit
projection `orbitProjection`. -/
@[simp]
theorem representedQuotientProjection_fppfHomogeneousQuotientIsoOrbitPoints
    [_root_.IsReduced H] :
    _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x)
        (fppfHomogeneousQuotientIsoOrbitPoints H x) =
      orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x :=
  _root_.CommHopfAlgCat.representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf
    H (stabilizerHopfIdeal H x) _ _ _

/-- Composing the forward direction of `fppfHomogeneousQuotientIsoOrbitPoints` with the orbit
inclusion recovers the descended orbit morphism into the ambient scheme `X`. -/
@[reassoc]
theorem fppfHomogeneousQuotientIsoOrbitPoints_hom_comp_orbitInclusion [_root_.IsReduced H] :
    (fppfHomogeneousQuotientIsoOrbitPoints H x).hom ≫
        (TauCeti.CommAlgCat.pointsSheafFunctor k).map
          (orbitInclusion ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x) =
      fppfHomogeneousQuotientToPointsSheaf H x := by
  apply _root_.CommHopfAlgCat.fppfHomogeneousQuotient_hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    fppfHomogeneousQuotientIsoOrbitPoints,
    _root_.CommHopfAlgCat.fppfHomogeneousQuotientIsoPointsSheaf_hom,
    _root_.CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_symm_apply,
    fppfHomogeneousQuotientProjection_comp_toPointsSheaf,
    ← _root_.CommHopfAlgCat.specPointsHomEquiv_comp, orbitProjection_inclusion]

/-- **Homogeneous orbit comparison.** When `X` is reduced and `orbit G x = Set.univ`, the
descended orbit map `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf
sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) := by
  have : IsIso (orbitInclusion ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x) :=
    isIso_orbitInclusion_of_orbit_eq_univ _ x h
  rw [← fppfHomogeneousQuotientIsoOrbitPoints_hom_comp_orbitInclusion H x]
  infer_instance

/-- **Homogeneous orbit comparison from rational-point transitivity.** When `X` is reduced and
`G(k)` acts transitively on `X(k)`, the descended orbit map
`G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_forall_exists_smul [_root_.IsReduced H]
    [IsReduced X.left]
    (htrans : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶
          ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))),
        g • x = y) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) :=
  isIso_fppfHomogeneousQuotientToPointsSheaf H x
    ((orbit_eq_univ_iff_forall_exists_smul _ x).mpr htrans)

/-- **Homogeneous orbit comparison for smooth targets.** When `X` is smooth over `Spec k` and
`orbit G x = Set.univ`, the descended orbit map `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is
an isomorphism of fppf sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_smooth [_root_.IsReduced H]
    [Smooth X.hom]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) := by
  have : IsReduced X.left := X.hom.isReduced_of_smooth
  exact isIso_fppfHomogeneousQuotientToPointsSheaf H x h

/-- **The canonical fppf quotient isomorphism for a reduced homogeneous scheme:**
`G / Stab_G(x) ≅ CommAlgCat.pointsSheaf X`. -/
def fppfHomogeneousQuotientIsoPointsSheaf [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf X :=
  have : IsIso (fppfHomogeneousQuotientToPointsSheaf H x) :=
    isIso_fppfHomogeneousQuotientToPointsSheaf H x h
  asIso (fppfHomogeneousQuotientToPointsSheaf H x)

/-- The forward direction of `fppfHomogeneousQuotientIsoPointsSheaf` is
`fppfHomogeneousQuotientToPointsSheaf`. -/
@[simp]
theorem fppfHomogeneousQuotientIsoPointsSheaf_hom [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    (fppfHomogeneousQuotientIsoPointsSheaf H x h).hom =
      fppfHomogeneousQuotientToPointsSheaf H x :=
  (rfl)

/-- For a reduced finite-type affine group acting transitively on a reduced finite-type scheme
`X` over an algebraically closed field, the orbit morphism `Spec H ⟶ X` is smooth if and only if
the coordinate Hopf algebra `H ⧸ stabilizerHopfIdeal H x` of the stabilizer is smooth over `k`. -/
theorem smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal
    [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    Smooth (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left ↔
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
    Q ≅ orbitOver ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x :=
  _root_.CommHopfAlgCat.representedQuotientIso H (stabilizerHopfIdeal H x) e
    (fppfHomogeneousQuotientIsoOrbitPoints H x)

/-- The scheme isomorphism `representedQuotientIsoOrbitOver` intertwines the quotient map
`Spec H ⟶ Q` with the orbit projection `Spec H ⟶ orbitOver (Spec H) x`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_representedQuotientIsoOrbitOver_hom
    [_root_.IsReduced H] {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫
        (representedQuotientIsoOrbitOver H x e).hom =
      orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  rw [representedQuotientIsoOrbitOver, _root_.CommHopfAlgCat.representedQuotientIso_hom,
    _root_.CommHopfAlgCat.representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap,
    representedQuotientProjection_fppfHomogeneousQuotientIsoOrbitPoints]

/-- When a representing quotient scheme `Q` carries a `G`-action making the quotient map
equivariant, the isomorphism `Q ≅ orbitOver G x` is `G`-equivariant. -/
theorem isModHom_representedQuotientIsoOrbitOver_hom [_root_.IsReduced H]
    {Q : Over (Spec (.of k))}
    [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) Q]
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q)
    (hq : μ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))] ≫
        _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e =
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) ◁
          _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫
        γ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)),Q]) :
    IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)))
      (representedQuotientIsoOrbitOver H x e).hom := by
  have : Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology k)
      ((TauCeti.CommAlgCat.pointsSheafFunctor k).map
        (_root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e)).hom :=
    _root_.CommHopfAlgCat.isLocallySurjective_pointsSheafFunctor_map_representedQuotientProjection
      H (stabilizerHopfIdeal H x) e
  refine TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_mul_comp
    (_root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e) hq
    (representedQuotientIsoOrbitOver H x e).hom ?_
  rw [representedQuotientProjection_comp_representedQuotientIsoOrbitOver_hom]
  exact mul_orbitProjection _ x

/-- **Scheme-level homogeneous orbit comparison.** Every scheme `Q` over `Spec k` representing
`G / Stab_G(x)` is canonically isomorphic over `Spec k` to a reduced homogeneous scheme `X`. -/
def representedQuotientIsoOfOrbitEqUniv [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    Q ≅ X :=
  representedQuotientIsoOrbitOver H x e ≪≫
    orbitInclusionIso ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x h

/-- The scheme isomorphism `representedQuotientIsoOfOrbitEqUniv` intertwines the quotient map
`Spec H ⟶ Q` with the orbit morphism `Spec H ⟶ X`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_representedQuotientIsoOfOrbitEqUniv_hom
    [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫
        (representedQuotientIsoOfOrbitEqUniv H x h e).hom =
      orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  rw [representedQuotientIsoOfOrbitEqUniv, Iso.trans_hom, ← Category.assoc,
    representedQuotientProjection_comp_representedQuotientIsoOrbitOver_hom, orbitInclusionIso_hom,
    orbitProjection_inclusion]

/-- When a representing quotient scheme `Q` carries a `G`-action making the quotient map
equivariant, the isomorphism `Q ≅ X` onto a reduced homogeneous scheme `X` is `G`-equivariant. -/
theorem isModHom_representedQuotientIsoOfOrbitEqUniv_hom [_root_.IsReduced H]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Q : Over (Spec (.of k))}
    [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) Q]
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q)
    (hq : μ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))] ≫
        _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e =
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) ◁
          _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫
        γ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)),Q]) :
    IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)))
      (representedQuotientIsoOfOrbitEqUniv H x h e).hom := by
  have : IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)))
      (representedQuotientIsoOrbitOver H x e).hom :=
    isModHom_representedQuotientIsoOrbitOver_hom H x e hq
  rw [representedQuotientIsoOfOrbitEqUniv, Iso.trans_hom]
  infer_instance

section ProjectiveOrbitComparison

/-- **Every orbit scheme is isomorphic to Chevalley's projective-orbit quotient model.** For a
reduced finite-type affine group `Spec H` acting on a finite-type scheme over an algebraically
closed field, the orbit scheme `orbitOver (Spec H) x` is isomorphic over `Spec k` to a projective
orbit scheme representing `G / Stab_G(x)`, intertwining `toProjectiveOrbit` and `toOrbit`. -/
theorem exists_projectiveOrbit_iso_orbitOver [_root_.IsReduced H] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅
        orbitOver ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x),
      Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left =
        toOrbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  obtain ⟨M, _, _, _, _, m, hm, isoQ, hproj⟩ :=
    HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints (stabilizerHopfIdeal H x)
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    representedQuotientIsoOrbitOver H x isoQ, ?_⟩
  have hcomp := congrArg Over.Hom.left
    (representedQuotientProjection_comp_representedQuotientIsoOrbitOver_hom H x isoQ)
  rw [Over.comp_left, congrArg Over.Hom.left hproj, orbitProjection_left] at hcomp
  exact hcomp

/-- **Every reduced homogeneous space is isomorphic to Chevalley's projective-orbit quotient
model.** In particular, every reduced finite-type homogeneous scheme `X` for a reduced finite-type
affine group `Spec H` over an algebraically closed field is isomorphic over `Spec k` to a
projective orbit scheme representing `G / Stab_G(x)`, intertwining `toProjectiveOrbit` and the
orbit morphism `Spec H ⟶ X`. -/
theorem exists_projectiveOrbit_iso_of_orbit_eq_univ [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅ X),
      Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left =
        (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left := by
  obtain ⟨M, _, _, _, _, m, hm, e, he⟩ := exists_projectiveOrbit_iso_orbitOver H x
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    e ≪≫ orbitInclusionIso _ x h, ?_⟩
  rw [Iso.trans_hom, Over.comp_left, ← Category.assoc, he, orbitInclusionIso_hom,
    orbitInclusion_left]
  exact toOrbit_ι _ x

end ProjectiveOrbitComparison

end OrbitComparison

end TauCeti.SchemeAction
