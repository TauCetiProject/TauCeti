/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Datum
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr

/-!
# Realization of the doubled minuscule Chevalley datum

The Chevalley datum on the pinned rational E₆ Lie algebra and the represented doubled
minuscule carrier define the same closed subgroup scheme of `GL₅₄` over `ℤ`. Their Lie-algebra
inputs differ, but the twelve represented simple root operators on the integral coordinate
lattice agree. Consequently their root-subgroup coordinate maps, and hence their defining
Hopf ideals, agree. The torus uses the same full weight lattice in both constructions.

`chevalleyDatumPointsEquiv` identifies their points over every commutative ring without
changing any matrix. It matches both signs of the simple root subgroups and the entire torus,
is natural in the value ring, and intertwines the independently defined Frobenius maps.
This is a realization of this particular datum, not an identification with the direct sum
of all fundamental modules or an assertion of generation of all points by root subgroups.

The construction uses `E6DoubledMinuscule.chevalleyDatum`, its pinned generator equations,
and the represented carrier's Kostant toral closure. The point-interface organization follows
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Geck.Realization`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Corollary 5 to Theorem 4′.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

open scoped Matrix
open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

open DynkinType _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v v'

private theorem rootAction_eq (i : Fin DynkinType.E6.rank ⊕ Fin DynkinType.E6.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).rootGenerator i)) =
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (serreRootGenerator (CartanMatrix.E 6)ᵀ i)) := by
  apply LinearMap.ext
  intro v
  cases i with
  | inl i =>
      rw [LieAlgebra.Basis.rootGenerator_inl, pinnedRepresentation_e_apply]
      -- The represented Serre system uses the numerical rank six.
      erw [serreRootGenerator_inl]
      exact (rep_ι_apply _ v).trans (congrArg (fun X => X *ᵥ v)
        (rationalSerreRepresentation_serreE i)) |>.symm
  | inr i =>
      rw [LieAlgebra.Basis.rootGenerator_inr, pinnedRepresentation_f_apply]
      -- The represented Serre system uses the numerical rank six.
      erw [serreRootGenerator_inr]
      exact (rep_ι_apply _ v).trans (congrArg (fun X => X *ᵥ v)
        (rationalSerreRepresentation_serreF i)) |>.symm

/-- The pinned doubled minuscule datum and the represented carrier have the same integral
Hopf ideal in `GL₅₄`. -/
theorem kostantToralDefiningIdeal_chevalleyDatum :
    kostantToralDefiningIdeal (DynkinType.E6.lieBasis valid_E6).rootGenerator
      (DynkinType.E6.lieBasis valid_E6).h chevalleyDatum.representation chevalleyDatum.lattice
      chevalleyDatum.representation_mem_lattice
      chevalleyDatum.isNilpotent_representation_rootGenerator chevalleyDatum.basis
      chevalleyDatum.coordinateWeight = definingIdeal := by
  -- State the intermediate equality in the numerical coordinate lattice, so that dependent
  -- datum fields and the finite-rank instances are not rewritten one at a time.
  suffices h :
      kostantToralDefiningIdeal (DynkinType.E6.lieBasis valid_E6).rootGenerator
        (DynkinType.E6.lieBasis valid_E6).h pinnedRepresentation lattice.toAddSubgroup
        pinnedRepresentation_kostantForm_mem_lattice
        chevalleyDatum.isNilpotent_representation_rootGenerator matrixBasis matrixWeight =
        definingIdeal by
    rw [chevalleyDatum_coordinateWeight]
    dsimp only [chevalleyDatum]
    exact h
  rw [definingIdeal_def]
  exact kostantToralDefiningIdeal_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ rootAction_eq

/-- The group scheme of the pinned doubled minuscule datum is the existing represented
carrier over `ℤ`. -/
theorem chevalleyDatum_groupScheme : chevalleyDatum.groupScheme = groupScheme := by
  rw [ChevalleyDatum.groupScheme, kostantToralGroupScheme, kostantToralDefiningIdeal_chevalleyDatum,
    groupScheme_def]
  -- Both quotient presentations use the same dimension, the datum's fifty-four coordinates.
  rfl

/-- Transporting the datum scheme to the represented carrier preserves its ambient inclusion. -/
@[simp↓]
theorem eqToHom_chevalleyDatum_groupScheme_comp_carrierι :
    eqToHom chevalleyDatum_groupScheme ≫ carrierι = chevalleyDatum.groupSchemeι := by
  rw [carrierι_def, ChevalleyDatum.groupSchemeι_def,
    kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def, ← Category.assoc]
  have hideal := kostantToralDefiningIdeal_chevalleyDatum
  rw [definingIdeal_def] at hideal
  -- The quotient transport has the same endpoints after reading the datum dimension.
  exact congrArg (fun f => f ≫ eqToHom (GeneralLinear.groupScheme_def ℤ 54).symm)
    (CommHopfAlgCat.eqToHom_comp_quotientSpecι _ hideal)

/-- Scheme realization identifies the full torus in the same fundamental-weight coordinates. -/
@[simp↓]
theorem chevalleyDatum_torus_comp_eqToHom_groupScheme :
    chevalleyDatum.torus ≫ eqToHom chevalleyDatum_groupScheme = weightTorus := by
  apply (cancel_mono carrierι).1
  rw [Category.assoc, eqToHom_chevalleyDatum_groupScheme_comp_carrierι]
  -- The ambient dimensions are definitionally equal after reading the datum's fields.
  erw [ChevalleyDatum.torus_comp_groupSchemeι, weightTorus_comp_carrierι,
    chevalleyDatum_coordinateWeight]
  rfl

/-- Scheme realization matches the positive simple root subgroups. -/
@[simp↓]
theorem chevalleyDatum_rootSubgroup_simpleIndex_comp_eqToHom_groupScheme
    (i : Fin DynkinType.E6.rank) :
    chevalleyDatum.rootSubgroup (DynkinType.E6.simpleIndex valid_E6 i) ≫
      eqToHom chevalleyDatum_groupScheme = rootSubgroup (.inl i) := by
  apply (cancel_mono carrierι).1
  rw [Category.assoc, eqToHom_chevalleyDatum_groupScheme_comp_carrierι]
  erw [ChevalleyDatum.rootSubgroup_simpleIndex_comp_groupSchemeι, rootSubgroup_comp_carrierι]
  exact kostantRootSubgroup_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rootAction_eq (.inl i))

/-- Scheme realization matches the negative simple root subgroups with their pinned signs. -/
@[simp↓]
theorem chevalleyDatum_rootSubgroup_neg_simpleIndex_comp_eqToHom_groupScheme
    (i : Fin DynkinType.E6.rank) :
    chevalleyDatum.rootSubgroup
        ((DynkinType.E6.simplyConnectedRootDatum valid_E6).reflectionPerm
          (DynkinType.E6.simpleIndex valid_E6 i) (DynkinType.E6.simpleIndex valid_E6 i)) ≫
      eqToHom chevalleyDatum_groupScheme = rootSubgroup (.inr i) := by
  apply (cancel_mono carrierι).1
  rw [Category.assoc, eqToHom_chevalleyDatum_groupScheme_comp_carrierι]
  erw [ChevalleyDatum.rootSubgroup_reflectionPerm_simpleIndex_comp_groupSchemeι,
    rootSubgroup_comp_carrierι]
  exact kostantRootSubgroup_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rootAction_eq (.inr i))

/-- The datum and the represented doubled minuscule carrier cut out the same matrix subgroup
over every commutative ring, including nonreduced rings. -/
theorem chevalleyDatum_points (A : Type v) [CommRing A] :
    chevalleyDatum.points A = points A := by
  rw [ChevalleyDatum.points_def, kostantToralDefiningIdeal_chevalleyDatum, points_def]
  -- The only remaining difference is the dimension read through the datum.
  rfl

/-- The matrix-preserving realization of the doubled minuscule Chevalley datum. -/
def chevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    chevalleyDatum.points A ≃* points A :=
  MulEquiv.subgroupCongr (chevalleyDatum_points A)

/-- Realization preserves the underlying matrix. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : chevalleyDatum.points A) :
    (chevalleyDatumPointsEquiv A g : Matrix.GeneralLinearGroup (Fin 54) A) =
      (g : Matrix.GeneralLinearGroup (Fin chevalleyDatum.dim) A) := (rfl)

/-- Inverse realization preserves the underlying matrix. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A] (g : points A) :
    ((chevalleyDatumPointsEquiv A).symm g : Matrix.GeneralLinearGroup (Fin chevalleyDatum.dim) A) =
      (g : Matrix.GeneralLinearGroup (Fin 54) A) := (rfl)

/-- Realization matches the positive simple root elements with their original additive
parameters. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex
    (i : Fin DynkinType.E6.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv A
      (chevalleyDatum.rootSubgroupPoints (DynkinType.E6.simpleIndex valid_E6 i) A u) =
      rootSubgroupPoints (.inl i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, ChevalleyDatum.coe_rootSubgroupPoints_simpleIndex,
    coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rootAction_eq (.inl i)) _

/-- Realization matches the negative simple root elements, including the signs of the
contragredient block. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex
    (i : Fin DynkinType.E6.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv A
      (chevalleyDatum.rootSubgroupPoints
        ((DynkinType.E6.simplyConnectedRootDatum valid_E6).reflectionPerm
          (DynkinType.E6.simpleIndex valid_E6 i) (DynkinType.E6.simpleIndex valid_E6 i)) A u) =
      rootSubgroupPoints (.inr i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    ChevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex, coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rootAction_eq (.inr i)) _

/-- Inverse realization recovers the positive simple root element with unchanged parameter. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl
    (i : Fin DynkinType.E6.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (rootSubgroupPoints (.inl i) A u) =
      chevalleyDatum.rootSubgroupPoints (DynkinType.E6.simpleIndex valid_E6 i) A u := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

/-- Inverse realization recovers the negative simple root element with unchanged parameter. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr
    (i : Fin DynkinType.E6.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (rootSubgroupPoints (.inr i) A u) =
      chevalleyDatum.rootSubgroupPoints
        ((DynkinType.E6.simplyConnectedRootDatum valid_E6).reflectionPerm
          (DynkinType.E6.simpleIndex valid_E6 i) (DynkinType.E6.simpleIndex valid_E6 i)) A u := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

/-- The whole torus is matched in the same fundamental-weight coordinates. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin DynkinType.E6.rank → Aˣ) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.torusPoints A s) = weightTorusPoints A s := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, ChevalleyDatum.coe_torusPoints,
    chevalleyDatum_coordinateWeight]
  -- The represented matrix uses the numerical rank rather than the datum's rank.
  erw [coe_weightTorusPoints]
  rfl

/-- Inverse realization preserves the full torus parameter. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_symm_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin DynkinType.E6.rank → Aˣ) :
    (chevalleyDatumPointsEquiv A).symm (weightTorusPoints A s) =
      chevalleyDatum.torusPoints A s := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

/-- Realization is natural under arbitrary changes of the value ring. -/
theorem chevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv B
      ((chevalleyDatum.pointsPresentation A).map (chevalleyDatum.pointsPresentation B) f g) =
      (pointsPresentation A).map (pointsPresentation B) f (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map, coe_chevalleyDatumPointsEquiv]
  -- The matrix-map dimensions are the datum dimension and its value fifty-four.
  rfl

/-- Inverse realization is natural under arbitrary changes of the value ring. -/
theorem chevalleyDatumPointsEquiv_symm_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : points A) :
    (chevalleyDatumPointsEquiv B).symm ((pointsPresentation A).map (pointsPresentation B) f g) =
      (chevalleyDatum.pointsPresentation A).map (chevalleyDatum.pointsPresentation B) f
        ((chevalleyDatumPointsEquiv A).symm g) := by
  apply (chevalleyDatumPointsEquiv B).injective
  rw [MulEquiv.apply_symm_apply, chevalleyDatumPointsEquiv_map, MulEquiv.apply_symm_apply]

/-- Realization intertwines the datum Frobenius with the independently defined represented
Frobenius on the whole point groups. -/
@[simp]
theorem chevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.frobenius p k A g) =
      frobenius p k A (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, ChevalleyDatum.coe_frobenius, coe_frobenius,
    coe_chevalleyDatumPointsEquiv]
  -- The matrix-map dimensions are the datum dimension and its value fifty-four.
  rfl

/-- Inverse realization also intertwines Frobenius on the whole point groups. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (g : points A) :
    (chevalleyDatumPointsEquiv A).symm (frobenius p k A g) =
      chevalleyDatum.frobenius p k A ((chevalleyDatumPointsEquiv A).symm g) := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

end

end TauCeti.E6DoubledMinuscule
