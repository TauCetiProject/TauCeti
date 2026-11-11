/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.FullWeight
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The intrinsic weight-torus ideal of the Geck carrier

When the Geck weights span the character lattice, restriction to the weight torus is
surjective. Its kernel defines a closed split torus in the integral carrier and in every
specialization. The quotient is identified with the split-torus coordinate algebra, and its
points are exactly the named Geck weight-torus points over every commutative value algebra.
The intrinsic ideal is compatible with scalar extension from the integral carrier, without
flatness assumptions.

The spanning hypothesis holds for E₈, F₄ and G₂. For other types the Geck representation has
the root lattice rather than the full weight lattice, so the same source torus need not embed.
These are closed-subgroup data for choosing a pinning, not an assertion of maximality or an
identification with an independently pinned simply connected group. The carrier here is the
specialization of the integral carrier, not the subgroup generated over the new base ring.

## Main declarations

* `TauCeti.DynkinType.geckWeightTorusIntegralDefiningIdeal`: the integral torus ideal.
* `TauCeti.DynkinType.geckWeightTorusDefiningIdeal`: the ideal in the specialized carrier.
* `TauCeti.DynkinType.geckWeightTorusCoordinateIso`: the split-torus quotient.
* `TauCeti.DynkinType.map_quotientPointsSubgroup_geckWeightTorusDefiningIdeal`: its points.
* `TauCeti.DynkinType.map_baseChangeHopfIdeal_geckWeightTorusIntegralDefiningIdeal`: scalar
  extension of the intrinsic ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233–3247.
* The quotient, point and scalar-extension constructions adapt
  `TauCeti.Algebra.Lie.E7.Minuscule.WeightTorus` to the Geck carrier.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

universe u v

noncomputable section

variable (t : DynkinType) (ht : t.Valid)
variable (hwt : Submodule.span ℤ (Set.range (t.geckWeight ht)) = ⊤)

include hwt

/-- Full character span makes integral restriction to the Geck weight torus surjective. -/
theorem geckWeightTorusIntegralCoordinateMap_surjective :
    Function.Surjective (t.geckWeightTorusIntegralCoordinateMap ht).hom := by
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) (t.geckWeightFin ht)
    ((t.span_range_geckWeightFin_eq_top_iff ht).mpr hwt)
  rw [← t.mkQuotient_comp_geckWeightTorusIntegralCoordinateMap ht] at h
  exact Function.Surjective.of_comp h

/-- The intrinsic Hopf ideal of the weight torus in the integral Geck carrier. -/
def geckWeightTorusIntegralDefiningIdeal :
    HopfIdeal ℤ (CommHopfAlgCat.quotient
      (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) :=
  HopfIdeal.kerOfSurjective (t.geckWeightTorusIntegralCoordinateMap ht).hom
    (t.geckWeightTorusIntegralCoordinateMap_surjective ht hwt)

/-- An integral carrier coordinate belongs to the torus ideal exactly when restriction vanishes. -/
@[simp↓]
theorem mem_geckWeightTorusIntegralDefiningIdeal
    (x : CommHopfAlgCat.quotient
      (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) :
    x ∈ t.geckWeightTorusIntegralDefiningIdeal ht hwt ↔
      (t.geckWeightTorusIntegralCoordinateMap ht).hom x = 0 := by
  rw [geckWeightTorusIntegralDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

variable (R : Type u) [CommRing R]

/-- Restriction to the full-weight Geck torus remains surjective after any specialization. -/
theorem geckWeightTorusToBaseChangeCoordinateMap_surjective :
    Function.Surjective (t.geckWeightTorusToBaseChangeCoordinateMap ht R).hom := by
  rw [← t.geckBaseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap ht R]
  exact CommHopfAlgCat.baseChangeMap_surjective_of_iso
    (t.geckWeightTorusIntegralCoordinateMap ht)
    (t.geckWeightTorusIntegralCoordinateMap_surjective ht hwt)
    (t.geckBaseChangeCoordinateIso ht R)
    (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.scalarTensorBialgEquiv ℤ R
      (G := SplitTorus.characterGroup (Fin t.rank))))

/-- The intrinsic Hopf ideal of the weight torus in the specialized Geck carrier. -/
def geckWeightTorusDefiningIdeal : HopfIdeal R
    (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R (t.geckDim ht))
      (t.geckBaseChangeDefiningIdeal ht R)) :=
  HopfIdeal.kerOfSurjective (t.geckWeightTorusToBaseChangeCoordinateMap ht R).hom
    (t.geckWeightTorusToBaseChangeCoordinateMap_surjective ht hwt R)

/-- A specialized carrier coordinate lies in the torus ideal exactly when restriction vanishes. -/
@[simp↓]
theorem mem_geckWeightTorusDefiningIdeal
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R (t.geckDim ht))
      (t.geckBaseChangeDefiningIdeal ht R)) :
    x ∈ t.geckWeightTorusDefiningIdeal ht hwt R ↔
      (t.geckWeightTorusToBaseChangeCoordinateMap ht R).hom x = 0 := by
  rw [geckWeightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the intrinsic torus ideal is its rank-`t.rank` split coordinate algebra. -/
def geckWeightTorusCoordinateIso :
    CommHopfAlgCat.quotient _ (t.geckWeightTorusDefiningIdeal ht hwt R) ≅
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin t.rank))).obj :=
  CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso
    (t.geckWeightTorusToBaseChangeCoordinateMap ht R)
    (t.geckWeightTorusToBaseChangeCoordinateMap_surjective ht hwt R)

/-- The quotient identification recovers the original restriction to the weight torus. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_geckWeightTorusCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient _ (t.geckWeightTorusDefiningIdeal ht hwt R) ≫
        (t.geckWeightTorusCoordinateIso ht hwt R).hom =
      t.geckWeightTorusToBaseChangeCoordinateMap ht R :=
  CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- The subgroup cut out by the intrinsic ideal is a split torus over any commutative ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_geckWeightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht R),
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (t.geckWeightTorusDefiningIdeal ht hwt R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let e : Multiplicative (Fin t.rank →₀ ℤ) ≃*
      Multiplicative (ULift.{u} (Fin t.rank) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  exact ⟨t.rank, ⟨(ObjectProperty.isoMk _ (t.geckWeightTorusCoordinateIso ht hwt R) ≪≫
    ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk
      (MonoidAlgebra.domCongrBialgEquiv R R e))).symm⟩⟩

omit hwt in
/-- The torus point map gives the original Geck weight-torus matrices over all value algebras. -/
@[simp↓]
theorem geckBaseChangePointsMulEquiv_mapPointsFunctor_weightTorus
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (Fin t.rank))).obj) A) :
    t.geckBaseChangePointsMulEquiv ht R A
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (t.geckWeightTorusToBaseChangeCoordinateMap ht R)).app A q) =
      t.geckWeightTorusPoints ht A (SplitTorus.pointsMulEquiv q) := by
  apply Subtype.ext
  rw [coe_geckWeightTorusPoints]
  have he := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (t.geckBaseChangeDefiningIdeal ht R) (t.geckWeightTorusToBaseChangeCoordinateMap ht R)
    (t.geckWeightTorusBaseChangeCoordinateMap ht R)
    (t.mkQuotient_comp_geckWeightTorusToBaseChangeCoordinateMap ht R) A q
  refine (t.coe_geckBaseChangePointsMulEquiv_apply ht R A _).trans
    ((congrArg (GeneralLinear.pointsMulEquiv (t.geckDim ht)) he.symm).trans ?_)
  rw [geckWeightTorusBaseChangeCoordinateMap_def,
    GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusBaseChangeCoordinateMap,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]

/-- The intrinsic torus ideal cuts out exactly the named Geck weight-torus points, including
points over nonreduced value algebras. -/
theorem map_quotientPointsSubgroup_geckWeightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup _ (t.geckWeightTorusDefiningIdeal ht hwt R) A).map
        (t.geckBaseChangePointsMulEquiv ht R A).toMonoidHom =
      (t.geckWeightTorusPoints ht A).range := by
  rw [geckWeightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q,
      (t.geckBaseChangePointsMulEquiv_mapPointsFunctor_weightTorus ht R A q).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom,
      geckBaseChangePointsMulEquiv_mapPointsFunctor_weightTorus, MulEquiv.apply_symm_apply]

/-- Scalar extension of the integral torus ideal is the intrinsic torus ideal of the specialized
carrier. No flatness or reducedness hypothesis is needed. -/
@[simp↓]
theorem map_baseChangeHopfIdeal_geckWeightTorusIntegralDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := R)
        (t.geckWeightTorusIntegralDefiningIdeal ht hwt)).map
        (t.geckBaseChangeCoordinateIso ht R).inv.hom =
      t.geckWeightTorusDefiningIdeal ht hwt R := by
  rw [geckWeightTorusIntegralDefiningIdeal, geckWeightTorusDefiningIdeal]
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (t.geckBaseChangeCoordinateIso ht R).symm
    (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.scalarTensorBialgEquiv ℤ R
      (G := SplitTorus.characterGroup (Fin t.rank))))
    (t.geckWeightTorusIntegralCoordinateMap_surjective ht hwt)
    (t.geckWeightTorusToBaseChangeCoordinateMap_surjective ht hwt R) ?_
  simpa only [Iso.symm_inv, _root_.CommHopfAlgCat.isoMk_hom] using
    t.geckBaseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap ht R

end

end TauCeti.DynkinType
