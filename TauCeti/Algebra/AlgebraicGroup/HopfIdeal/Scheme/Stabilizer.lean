/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth
public import TauCeti.AlgebraicGeometry.GroupAction.Stabilizer

/-!
# Stabilizer Hopf ideals of affine group actions

Let `G = Spec H` be an affine group scheme over a commutative ring `R` acting on a scheme `X` over
`Spec R`, and let `x : Spec R ⟶ X` be a section whose scheme-theoretic stabilizer inclusion
`stabilizer G x ⟶ G` is a closed immersion (for example, any closed section `x`, or any rational
point when `R` is a field).

The scheme-theoretic stabilizer `stabilizer G x` is a closed subgroup scheme of `Spec H`, hence is
cut out by a unique Hopf ideal `stabilizerHopfIdeal H x` of `H`. Over every commutative
`R`-algebra `A`, the subgroup of `A`-points cut out by `stabilizerHopfIdeal H x` is precisely the
stabilizer of `x` in `G(A)`, two `A`-points of `Spec H` lie in the same left coset of
`stabilizerHopfIdeal H x` iff they have the same image under `orbitMap G x`, and smoothness of
`H ⧸ stabilizerHopfIdeal H x` over `R` is equivalent to smoothness of `stabilizer G x` over
`Spec R`.

## Main declarations

* `TauCeti.SchemeAction.stabilizerInclGrpHom`: the stabilizer inclusion into `Spec H` as a
  morphism of group schemes over `Spec R`.
* `TauCeti.SchemeAction.stabilizerClosedSubgroup`: the scheme-theoretic stabilizer of `x` as a
  `ClosedSubgroupScheme` of `Spec H`.
* `TauCeti.SchemeAction.stabilizerHopfIdeal`: the defining Hopf ideal of `stabilizer G x`.
* `TauCeti.SchemeAction.quotientSpecStabilizerHopfIdealIso`: the group-scheme isomorphism
  `Spec (H ⧸ stabilizerHopfIdeal H x) ≅ stabilizer G x` over `Spec H`.
* `TauCeti.SchemeAction.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff`: the `A`-points cut
  out by `stabilizerHopfIdeal H x` are precisely the stabilizing `A`-points of `G`.
* `TauCeti.SchemeAction.inv_mul_mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff`: left cosets
  of `stabilizerHopfIdeal H x` on `A`-points detect equality under `orbitMap`.
* `TauCeti.SchemeAction.smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff`: smoothness criterion
  for `H ⧸ stabilizerHopfIdeal H x`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.e, 7.e.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open TauCeti.CommHopfAlgCat
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

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

variable [hclosed : IsClosedImmersion
  (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left]

include hclosed in
instance : IsClosedImmersion (stabilizerInclGrpHom H x).hom.hom.left := by
  rw [stabilizerInclGrpHom_hom_hom]
  exact hclosed

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

private def quotientSpecStabilizerHopfIdealOverIso :
    ((Spec (CommRingCat.of (H.quotient (stabilizerHopfIdeal H x)))).asOver
        (Spec (CommRingCat.of R))) ≅
      stabilizer ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
  (Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso (quotientSpecStabilizerHopfIdealIso H x)

@[reassoc (attr := simp)]
private theorem quotientSpecStabilizerHopfIdealOverIso_hom_incl :
    (quotientSpecStabilizerHopfIdealOverIso H x).hom ≫
        stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x =
      (TauCeti.CommHopfAlgCat.quotientSpecι H (stabilizerHopfIdeal H x)).hom.hom := by
  have h := congrArg (fun f ↦ (Grp.forget (Over (Spec (CommRingCat.of R)))).map f)
    (quotientSpecStabilizerHopfIdealIso_hom_comp H x)
  rw [Functor.map_comp, Grp.forget_map, Grp.forget_map, stabilizerInclGrpHom_hom_hom] at h
  exact h

/-- **Points of the stabilizer Hopf ideal.** Over every commutative `R`-algebra `A`, an `A`-point
of `Spec H` lies in the subgroup cut out by `stabilizerHopfIdeal H x` if and only if it stabilizes
`x`. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal H x) A ↔
      Spec.mapMulEquiv g ∈
        stabilizerPoints ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x
          ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) := by
  set I := stabilizerHopfIdeal H x
  let e := quotientSpecStabilizerHopfIdealOverIso H x
  rw [← stabilizer.exists_lift_iff, TauCeti.CommHopfAlgCat.quotientPointsSubgroup,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨Spec.mapMulEquiv q ≫ e.hom, ?_⟩
    have hq' : TauCeti.CommHopfAlgCat.quotientPointsHom H I A q = g := hq
    rw [← hq', Category.assoc, quotientSpecStabilizerHopfIdealOverIso_hom_incl]
    exact (mapMulEquiv_quotientPointsHom H I A q).symm
  · rintro ⟨s, hs⟩
    refine ⟨Spec.mapMulEquiv.symm (s ≫ e.inv), Spec.mapMulEquiv.injective ?_⟩
    rw [mapMulEquiv_quotientPointsHom, MulEquiv.apply_symm_apply]
    have h1 : e.inv ≫ (quotientSpecι H I).hom.hom =
        stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x :=
      (congrArg (e.inv ≫ ·) (quotientSpecStabilizerHopfIdealOverIso_hom_incl H x).symm).trans
        (Iso.inv_hom_id_assoc e _)
    exact (Category.assoc s e.inv (quotientSpecι H I).hom.hom).trans <|
      (congrArg (s ≫ ·) h1).trans hs

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
  let : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso @Smooth]

end TauCeti.SchemeAction
