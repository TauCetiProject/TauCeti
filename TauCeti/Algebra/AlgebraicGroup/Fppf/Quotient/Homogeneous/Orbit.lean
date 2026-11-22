/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Stabilizer
public import TauCeti.Algebra.Category.CommAlgCat.PointsSheaf
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Homogeneous

/-!
# Orbit-map comparison for fppf homogeneous quotients

Let `G = Spec H` be an affine algebraic group scheme over a commutative ring `R` acting on a
scheme `X` over `Spec R`, and let `x : Spec R ⟶ X` be a section that is a closed immersion (for
instance, any rational point when `R` is a field).

The scheme-theoretic stabilizer `stabilizer G x` is cut out by `stabilizerHopfIdeal H x`, and the
orbit morphism `orbitMap G x` descends to a morphism of fppf sheaves
`fppfHomogeneousQuotientToPointsSheaf H x` from the fppf homogeneous quotient `G / Stab_G(x)` to
`CommAlgCat.pointsSheaf X`. Whenever `orbitMap G x` is locally surjective on fppf sheaves
of points (for example, faithfully flat and locally of finite presentation), this descended
morphism is an isomorphism of fppf sheaves
(`isIso_fppfHomogeneousQuotientToPointsSheaf_of_isLocallySurjective`).

* When `R = k` is a field and `Spec H` is geometrically reduced and of finite type over `k`, and `X`
  is of finite type over `k`:

* The descended orbit projection `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf (orbitOver G x)` is an
  isomorphism of fppf sheaves, for every orbit (without assuming `X` reduced, separated, or
  homogeneous).
* If moreover `X` is reduced (or smooth) and `orbit G x = Set.univ` (equivalently, when `k` is
  algebraically closed, `G(k)` acts transitively on `X(k)`), then the descended orbit morphism
  `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf sheaves.
* Because `CommAlgCat.pointsSheafFunctor` is fully faithful, any scheme `Q` over `Spec k`
  representing `G / Stab_G(x)` is canonically isomorphic over `Spec k` to `orbitOver G x` (and to
  `X` when `X` is reduced and homogeneous), intertwining the quotient projection with the orbit
  morphism and respecting the `G`-action whenever the quotient projection is equivariant.

## Main declarations

* `TauCeti.SchemeAction.fppfHomogeneousQuotientToPointsSheaf`: descent of `orbitMap (Spec H) x`
  to the fppf homogeneous quotient `G / Stab_G(x)`.
* `TauCeti.SchemeAction.isIso_fppfHomogeneousQuotientToPointsSheaf_of_isLocallySurjective`: general
  fppf-local-surjectivity criterion over an arbitrary commutative ring `R`.
* `TauCeti.SchemeAction.fppfHomogeneousQuotientIsoOrbitPoints`: the fppf sheaf isomorphism
  `G / Stab_G(x) ≅ CommAlgCat.pointsSheaf (orbitOver G x)`.
* `TauCeti.SchemeAction.fppfHomogeneousQuotientIsoPointsSheaf`: for a reduced homogeneous scheme
  `X`, the fppf sheaf isomorphism `G / Stab_G(x) ≅ CommAlgCat.pointsSheaf X`.
* `TauCeti.SchemeAction.representedQuotientIsoOrbitOver` and
  `TauCeti.SchemeAction.representedQuotientIsoOfOrbitEqUniv`: scheme-level comparison with any
  scheme representing `G / Stab_G(x)`, with equivariance descent.

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
  [IsClosedImmersion x.left]

private theorem orbitMap_mul_invariant :
    ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A),
      Spec.mapMulEquiv (g * n.val) ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
        Spec.mapMulEquiv g ≫
          orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
  fun A g n ↦ ((inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff H x A g
    (g * n.val)).mp (by simpa only [inv_mul_cancel_left] using n.property)).symm

/-- The orbit morphism `Spec H ⟶ X` descends to a morphism of fppf sheaves from the fppf
homogeneous quotient `G / Stab_G(x)` to `CommAlgCat.pointsSheaf X`. -/
def fppfHomogeneousQuotientToPointsSheaf :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ⟶
      TauCeti.CommAlgCat.pointsSheaf X :=
  _root_.CommHopfAlgCat.fppfHomogeneousQuotientDesc H (stabilizerHopfIdeal H x)
    (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x)
    (orbitMap_mul_invariant H x)

/-- Restricting the descended orbit map along the quotient projection recovers the orbit map on
convolution points. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toPointsSheaf :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection H (stabilizerHopfIdeal H x) ≫
        (fppfHomogeneousQuotientToPointsSheaf H x).hom =
      _root_.CommHopfAlgCat.specPointsHomEquiv H X
        (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x) :=
  _root_.CommHopfAlgCat.fppfHomogeneousQuotientProjection_comp_desc H _ _ _

/-- **Orbit-map comparison from local surjectivity.** Over an arbitrary commutative ring `R`, if
the orbit morphism `orbitMap (Spec H) x` is locally surjective on fppf sheaves of points, then the
descended orbit map `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf
sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_isLocallySurjective
    [Sheaf.IsLocallySurjective ((TauCeti.CommAlgCat.pointsSheafFunctor R).map
      (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x))] :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) :=
  _root_.CommHopfAlgCat.isIso_fppfHomogeneousQuotientDesc H (stabilizerHopfIdeal H x)
    (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x)
    (orbitMap_mul_invariant H x)
    fun A g g' h ↦ (inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff H x A g g').mpr h

end StabilizerIdeal

section OrbitComparison

variable {k : Type u} [Field k]
  (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (.of k))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) X]
  [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

local instance :
    LocallyOfFiniteType ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom :=
  (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance

local instance :
    CompactSpace ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of H)))

local instance :
    IsAffine ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  isAffine_Spec _

section CompactTarget

variable [CompactSpace X.left]

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

local instance
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom] :
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

/-- **Orbit-map comparison for any orbit.** For a geometrically reduced affine group of finite type
over a field acting on a finite-type scheme, the descended orbit projection gives an isomorphism of
fppf sheaves `G / Stab_G(x) ≅ CommAlgCat.pointsSheaf (orbitOver G x)`. -/
def fppfHomogeneousQuotientIsoOrbitPoints
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom] :
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
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom] :
    _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x)
        (fppfHomogeneousQuotientIsoOrbitPoints H x) =
      orbitProjection ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x :=
  _root_.CommHopfAlgCat.representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf
    H (stabilizerHopfIdeal H x) _ _ _

/-- Composing the forward direction of `fppfHomogeneousQuotientIsoOrbitPoints` with the orbit
inclusion recovers the descended orbit morphism into the ambient scheme `X`. -/
@[reassoc]
theorem fppfHomogeneousQuotientIsoOrbitPoints_hom_comp_orbitInclusion
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom] :
    (fppfHomogeneousQuotientIsoOrbitPoints H x).hom ≫
        (TauCeti.CommAlgCat.pointsSheafFunctor k).map
          (orbitInclusion ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x) =
      fppfHomogeneousQuotientToPointsSheaf H x := by
  apply _root_.CommHopfAlgCat.fppfHomogeneousQuotient_hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    ← _root_.CommHopfAlgCat.specPointsHomEquiv_representedQuotientProjection H
      (stabilizerHopfIdeal H x) (fppfHomogeneousQuotientIsoOrbitPoints H x),
    representedQuotientProjection_fppfHomogeneousQuotientIsoOrbitPoints,
    ← _root_.CommHopfAlgCat.specPointsHomEquiv_comp, orbitProjection_inclusion,
    fppfHomogeneousQuotientProjection_comp_toPointsSheaf]

/-- **Scheme-level comparison for any orbit.** Every scheme `Q` over `Spec k` representing
`G / Stab_G(x)` is canonically isomorphic over `Spec k` to the orbit scheme `orbitOver G x`. -/
def representedQuotientIsoOrbitOver
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
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
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    {Q : Over (Spec (.of k))}
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
theorem isModHom_representedQuotientIsoOrbitOver_hom
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
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
      (representedQuotientIsoOrbitOver H x e).hom :=
  _root_.CommHopfAlgCat.isModHom_representedQuotientIso_hom H (stabilizerHopfIdeal H x) e
    (fppfHomogeneousQuotientIsoOrbitPoints H x) hq (by
      rw [representedQuotientProjection_fppfHomogeneousQuotientIsoOrbitPoints]
      exact mul_orbitProjection _ x)

end CompactTarget

/-- **Homogeneous orbit comparison.** When `X` is reduced and `orbit G x = Set.univ`, the
descended orbit map `G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf
sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) := by
  have : CompactSpace X.left := Function.Surjective.compactSpace (orbitMap _ x).left.continuous
    ((surjective_iff _).mp ((surjective_orbitMap_iff_orbit_eq_univ _ x).mpr h))
  have hid : fppfHomogeneousQuotientToPointsSheaf H x =
      (fppfHomogeneousQuotientIsoOrbitPoints H x).hom ≫
        (TauCeti.CommAlgCat.pointsSheafFunctor k).map (orbitInclusionIso _ x h).hom := by
    rw [orbitInclusionIso_hom, fppfHomogeneousQuotientIsoOrbitPoints_hom_comp_orbitInclusion]
  rw [hid]
  infer_instance

/-- **Homogeneous orbit comparison from rational-point transitivity.** Over an algebraically closed
field, when `X` is reduced and `G(k)` acts transitively on `X(k)`, the descended orbit map
`G / Stab_G(x) ⟶ CommAlgCat.pointsSheaf X` is an isomorphism of fppf sheaves. -/
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_forall_exists_smul
    [IsAlgClosed k]
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
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
theorem isIso_fppfHomogeneousQuotientToPointsSheaf_of_smooth
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [Smooth X.hom]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    IsIso (fppfHomogeneousQuotientToPointsSheaf H x) := by
  have : IsReduced X.left := X.hom.isReduced_of_smooth
  exact isIso_fppfHomogeneousQuotientToPointsSheaf H x h

/-- **The canonical fppf quotient isomorphism for a reduced homogeneous scheme:**
`G / Stab_G(x) ≅ CommAlgCat.pointsSheaf X`. -/
def fppfHomogeneousQuotientIsoPointsSheaf
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf X :=
  have : IsIso (fppfHomogeneousQuotientToPointsSheaf H x) :=
    isIso_fppfHomogeneousQuotientToPointsSheaf H x h
  asIso (fppfHomogeneousQuotientToPointsSheaf H x)

/-- The forward direction of `fppfHomogeneousQuotientIsoPointsSheaf` is
`fppfHomogeneousQuotientToPointsSheaf`. -/
@[simp]
theorem fppfHomogeneousQuotientIsoPointsSheaf_hom
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    (fppfHomogeneousQuotientIsoPointsSheaf H x h).hom =
      fppfHomogeneousQuotientToPointsSheaf H x :=
  (rfl)

/-- Under `fppfHomogeneousQuotientIsoPointsSheaf`, `representedQuotientProjection` is the orbit
morphism `orbitMap`. -/
@[simp]
theorem representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x)
        (fppfHomogeneousQuotientIsoPointsSheaf H x h) =
      orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x :=
  (_root_.CommHopfAlgCat.specPointsHomEquiv H X).injective <| by
    rw [_root_.CommHopfAlgCat.specPointsHomEquiv_representedQuotientProjection,
      fppfHomogeneousQuotientIsoPointsSheaf_hom,
      fppfHomogeneousQuotientProjection_comp_toPointsSheaf]

/-- **Scheme-level homogeneous orbit comparison.** Every scheme `Q` over `Spec k` representing
`G / Stab_G(x)` is canonically isomorphic over `Spec k` to a reduced homogeneous scheme `X`. -/
def representedQuotientIsoOfOrbitEqUniv
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    Q ≅ X :=
  _root_.CommHopfAlgCat.representedQuotientIso H (stabilizerHopfIdeal H x) e
    (fppfHomogeneousQuotientIsoPointsSheaf H x h)

/-- The scheme isomorphism `representedQuotientIsoOfOrbitEqUniv` intertwines the quotient map
`Spec H ⟶ Q` with the orbit morphism `Spec H ⟶ X`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_representedQuotientIsoOfOrbitEqUniv_hom
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ)
    {Q : Over (Spec (.of k))}
    (e : _root_.CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal H x) ≅
      TauCeti.CommAlgCat.pointsSheaf Q) :
    _root_.CommHopfAlgCat.representedQuotientProjection H (stabilizerHopfIdeal H x) e ≫
        (representedQuotientIsoOfOrbitEqUniv H x h e).hom =
      orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  rw [representedQuotientIsoOfOrbitEqUniv, _root_.CommHopfAlgCat.representedQuotientIso_hom,
    _root_.CommHopfAlgCat.representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap,
    representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf]

/-- When a representing quotient scheme `Q` carries a `G`-action making the quotient map
equivariant, the isomorphism `Q ≅ X` onto a reduced homogeneous scheme `X` is `G`-equivariant. -/
theorem isModHom_representedQuotientIsoOfOrbitEqUniv_hom
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
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
      (representedQuotientIsoOfOrbitEqUniv H x h e).hom :=
  _root_.CommHopfAlgCat.isModHom_representedQuotientIso_hom H (stabilizerHopfIdeal H x) e
    (fppfHomogeneousQuotientIsoPointsSheaf H x h) hq (by
      rw [representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf]
      exact mul_orbitMap _ x)

end OrbitComparison

end TauCeti.SchemeAction
