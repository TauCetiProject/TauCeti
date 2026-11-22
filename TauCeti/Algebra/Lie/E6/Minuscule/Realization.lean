/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Datum
public import TauCeti.Algebra.Lie.E6.Minuscule.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr

/-!
# Realization of the minuscule Chevalley datum of E₆

The full-weight Chevalley datum `TauCeti.E6Minuscule.chevalleyDatum` on the pinned rational
E₆ Lie algebra and the represented twenty-seven-dimensional minuscule carrier
`TauCeti.E6Minuscule.groupScheme` define the same closed subgroup scheme of `GL₂₇` over `ℤ`.
Their Lie-algebra inputs differ: the datum acts through the pinned Lie algebra and
`TauCeti.DynkinType.serreLiftEquiv`, the carrier through the Serre presentation of the minuscule
weight table. Their twelve signed simple root operators on the integral coordinate lattice agree,
so their root-subgroup coordinate maps, and hence their defining Hopf ideals, agree. The torus
uses the same minuscule weights, in the same fundamental-weight coordinates, in both
constructions.

`TauCeti.E6Minuscule.chevalleyDatumPointsEquiv` identifies their points over every commutative
ring without changing any matrix. It matches both signs of the simple root subgroups with the
same node and parameter and the entire torus with the same parameter, is natural in the value
ring, and intertwines the independently defined Frobenius maps. Every root subgroup of the datum,
at all seventy-two roots, is injective over every commutative ring. This is a realization of this
particular datum; it does not compare the datum with the simply connected datum
`TauCeti.DynkinType.scChevalleyDatum`, and it asserts no generation of all points by root
subgroups.

## Main definitions

* `TauCeti.E6Minuscule.chevalleyDatumPointsEquiv`: the matrix-preserving isomorphism between
  the points of the datum and of the carrier over every commutative ring.

## Main results

* `TauCeti.E6Minuscule.kostantToralDefiningIdeal_chevalleyDatum`,
  `TauCeti.E6Minuscule.chevalleyDatum_groupScheme` and
  `TauCeti.E6Minuscule.chevalleyDatum_points`: equality of the integral defining Hopf ideals, of
  the group schemes over `ℤ` and of the matrix point subgroups over every commutative ring.
* `TauCeti.E6Minuscule.chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex`,
  `TauCeti.E6Minuscule.chevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex` and
  `TauCeti.E6Minuscule.chevalleyDatumPointsEquiv_torusPoints`, with their inverse forms: the
  transport equations on simple root subgroups and torus points.
* `TauCeti.E6Minuscule.chevalleyDatumPointsEquiv_map` and
  `TauCeti.E6Minuscule.chevalleyDatumPointsEquiv_frobenius`: naturality in the value ring and
  intertwining of the Frobenius maps.
* `TauCeti.E6Minuscule.chevalleyDatum_rootSubgroupPoints_injective`: injectivity of every root
  subgroup of the datum.

The organization follows `TauCeti.Algebra.Lie.E6.DoubledMinuscule.Realization`, the realization
of the doubled E₆ datum, and `TauCeti.Algebra.AlgebraicGroup.Chevalley.Geck.Realization`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Corollary 5 to Theorem 4′.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

open scoped Matrix
open CategoryTheory

namespace TauCeti.E6Minuscule

open DynkinType _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v v'

/-- The datum and represented actions of each signed simple root generator agree. -/
private theorem rootAction_eq (k : Fin DynkinType.E6.rank ⊕ Fin DynkinType.E6.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).rootGenerator k)) =
    weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (serreRootGenerator weightTable.cartanMatrix k)) := by
  rw [chevalleyDatum_representation]
  -- `Fin.cast rank_E6` is the identity on each summand, up to structure eta.
  cases k <;> exact pinnedRepresentation_ι_rootGenerator _

/-- The pinned minuscule datum and the represented carrier have the same integral Hopf ideal in
`GL₂₇`. -/
theorem kostantToralDefiningIdeal_chevalleyDatum :
    kostantToralDefiningIdeal (DynkinType.E6.lieBasis valid_E6).rootGenerator
      (DynkinType.E6.lieBasis valid_E6).h chevalleyDatum.representation chevalleyDatum.lattice
      chevalleyDatum.representation_mem_lattice
      chevalleyDatum.isNilpotent_representation_rootGenerator chevalleyDatum.basis
      chevalleyDatum.coordinateWeight = definingIdeal := by
  rw [chevalleyDatum_coordinateWeight, ← weightTable_weight, definingIdeal_def]
  exact kostantToralDefiningIdeal_eq_of_operator_eq (κ := Fin 6) _ _ _ _ _ _ _ _ _ _ _ _ _
    rootAction_eq

/-- The group scheme of the pinned minuscule datum is the represented carrier over `ℤ`. -/
theorem chevalleyDatum_groupScheme : chevalleyDatum.groupScheme = groupScheme := by
  rw [ChevalleyDatum.groupScheme, kostantToralGroupScheme, kostantToralDefiningIdeal_chevalleyDatum,
    groupScheme_def]
  -- Both quotient presentations use the same dimension, the datum's twenty-seven coordinates.
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
  exact congrArg (fun f => f ≫ eqToHom (GeneralLinear.groupScheme_def ℤ 27).symm)
    (CommHopfAlgCat.eqToHom_comp_quotientSpecι _ hideal)

/-- Scheme realization identifies the full torus in the same fundamental-weight coordinates. -/
@[simp↓]
theorem chevalleyDatum_torus_comp_eqToHom_groupScheme :
    chevalleyDatum.torus ≫ eqToHom chevalleyDatum_groupScheme = weightTorus := by
  apply (cancel_mono carrierι).1
  rw [Category.assoc, eqToHom_chevalleyDatum_groupScheme_comp_carrierι]
  -- The ambient dimensions are definitionally equal after reading the datum's fields.
  erw [ChevalleyDatum.torus_comp_groupSchemeι, weightTorus_comp_carrierι,
    chevalleyDatum_coordinateWeight, weightTable_weight]
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

/-- Scheme realization matches the negative simple root subgroups. -/
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

/-- The datum and the represented minuscule carrier cut out the same matrix subgroup over every
commutative ring, including nonreduced rings. -/
theorem chevalleyDatum_points (A : Type v) [CommRing A] :
    chevalleyDatum.points A = points A := by
  rw [ChevalleyDatum.points_def, kostantToralDefiningIdeal_chevalleyDatum, points_def]
  -- The only remaining difference is the dimension read through the datum.
  rfl

/-- The matrix-preserving realization of the minuscule Chevalley datum of E₆. -/
def chevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    chevalleyDatum.points A ≃* points A :=
  MulEquiv.subgroupCongr (chevalleyDatum_points A)

/-- Realization preserves the underlying matrix. -/
-- Here and below, `simp↓` matches before `chevalleyDatum_dim` rewrites the implicit matrix size.
@[simp↓]
theorem coe_chevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : chevalleyDatum.points A) :
    (chevalleyDatumPointsEquiv A g : Matrix.GeneralLinearGroup (Fin 27) A) =
      (g : Matrix.GeneralLinearGroup (Fin chevalleyDatum.dim) A) := (rfl)

/-- Inverse realization preserves the underlying matrix. -/
@[simp↓]
theorem coe_chevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A] (g : points A) :
    ((chevalleyDatumPointsEquiv A).symm g : Matrix.GeneralLinearGroup (Fin chevalleyDatum.dim) A) =
      (g : Matrix.GeneralLinearGroup (Fin 27) A) := (rfl)

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

/-- Realization matches the negative simple root elements with their original additive
parameters. -/
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
@[simp↓]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl
    (i : Fin DynkinType.E6.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (rootSubgroupPoints (.inl i) A u) =
      chevalleyDatum.rootSubgroupPoints (DynkinType.E6.simpleIndex valid_E6 i) A u := by
  rw [MulEquiv.symm_apply_eq, chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex]

/-- Inverse realization recovers the negative simple root element with unchanged parameter. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr
    (i : Fin DynkinType.E6.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (rootSubgroupPoints (.inr i) A u) =
      chevalleyDatum.rootSubgroupPoints
        ((DynkinType.E6.simplyConnectedRootDatum valid_E6).reflectionPerm
          (DynkinType.E6.simpleIndex valid_E6 i) (DynkinType.E6.simpleIndex valid_E6 i)) A u := by
  rw [MulEquiv.symm_apply_eq, chevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex]

/-- The whole torus is matched in the same fundamental-weight coordinates. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin DynkinType.E6.rank → Aˣ) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.torusPoints A s) = weightTorusPoints A s := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, ChevalleyDatum.coe_torusPoints,
    chevalleyDatum_coordinateWeight]
  -- The represented matrix uses the numerical rank rather than the datum's rank.
  erw [coe_weightTorusPoints, weightTable_weight]
  rfl

/-- Inverse realization preserves the full torus parameter. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_symm_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin DynkinType.E6.rank → Aˣ) :
    (chevalleyDatumPointsEquiv A).symm (weightTorusPoints A s) =
      chevalleyDatum.torusPoints A s := by
  rw [MulEquiv.symm_apply_eq, chevalleyDatumPointsEquiv_torusPoints]

/-- Realization is natural under arbitrary changes of the value ring. -/
theorem chevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv B
      ((chevalleyDatum.pointsPresentation A).map (chevalleyDatum.pointsPresentation B) f g) =
      (pointsPresentation A).map (pointsPresentation B) f (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map, coe_chevalleyDatumPointsEquiv]
  -- The matrix-map dimensions are the datum dimension and its value twenty-seven.
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
@[simp↓]
theorem chevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.frobenius p k A g) =
      frobenius p k A (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, ChevalleyDatum.coe_frobenius, coe_frobenius,
    coe_chevalleyDatumPointsEquiv]
  -- The matrix-map dimensions are the datum dimension and its value twenty-seven.
  rfl

/-- Inverse realization also intertwines Frobenius on the whole point groups. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (g : points A) :
    (chevalleyDatumPointsEquiv A).symm (frobenius p k A g) =
      chevalleyDatum.frobenius p k A ((chevalleyDatumPointsEquiv A).symm g) := by
  rw [MulEquiv.symm_apply_eq, chevalleyDatumPointsEquiv_frobenius, MulEquiv.apply_symm_apply]

/-- **Every root subgroup of the minuscule datum is injective**, at all seventy-two roots of `E₆`
and over every commutative ring, including nonreduced rings. -/
theorem chevalleyDatum_rootSubgroupPoints_injective (γ : Fin DynkinType.E6.numRoots)
    (A : Type v) [CommRing A] :
    Function.Injective (chevalleyDatum.rootSubgroupPoints γ A) := by
  refine chevalleyDatum.rootSubgroupPoints_injective_of_simple A (fun i u v huv => ?_) γ
  exact rootSubgroupPoints_injective (.inl i) A (by
    simpa only [chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex] using
      congrArg (chevalleyDatumPointsEquiv A) huv)

end

end TauCeti.E6Minuscule
