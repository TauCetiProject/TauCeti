/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Datum
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.Lie.F4.ShortRoot.Frobenius
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Comparison

/-!
# Integral realization of the short-root F₄ Chevalley datum

The pinned Chevalley datum on the twenty-six-dimensional short-root module defines the same
integral closed subgroup of `GL₂₆` as the represented short-root carrier. Their defining Hopf
ideals agree because both signs of every simple root act by the same rational endomorphism
on the same admissible coordinate lattice, and their weight-torus coordinates agree.

The resulting identification of point groups preserves every matrix and the actual torus,
including over nonreduced coefficient rings. This compares the datum with its represented
carrier, not with the full-weight fundamental-module construction of the simply connected
group. In particular it makes no specialization or point-generation assertion for the
prime-field generated carrier.

The proof uses `F4ShortRoot.pinnedRepresentation_ι_rootGenerator`, the common-kernel
construction of `kostantToralDefiningIdeal`, and its independence from the presentation of
the root-vector action. The point equivalence follows the matrix-preserving realization
pattern of `DynkinType.geckChevalleyDatumPointsEquiv`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plate VIII.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open CategoryTheory DynkinType _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

private theorem rootCoordinateMap_eq (k : Fin DynkinType.F4.rank ⊕ Fin DynkinType.F4.rank) :
    kostantRootSubgroupCoordinateMap (DynkinType.lieBasis .F4 valid_F4).rootGenerator
      (DynkinType.lieBasis .F4 valid_F4).h chevalleyDatum.representation chevalleyDatum.lattice
      chevalleyDatum.representation_mem_lattice k
      (chevalleyDatum.isNilpotent_representation_rootGenerator k) chevalleyDatum.basis =
    kostantRootSubgroupCoordinateMap (serreRootGenerator CartanMatrix.F₄ᵀ)
      (serreH ℚ CartanMatrix.F₄ᵀ) rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
      (k.map (Fin.cast rank_F4) (Fin.cast rank_F4))
      (isNilpotent_rep_serreRootGenerator _) latticeBasis := by
  apply kostantRootSubgroupCoordinateMap_eq_of_action_eq
  rw [chevalleyDatum_representation_rootGenerator, rep_ι,
    rationalSerreRepresentation_serreRootGenerator]

private theorem toralDefiningIdeal_eq :
    kostantToralDefiningIdeal (DynkinType.lieBasis .F4 valid_F4).rootGenerator
      (DynkinType.lieBasis .F4 valid_F4).h chevalleyDatum.representation chevalleyDatum.lattice
      chevalleyDatum.representation_mem_lattice
      chevalleyDatum.isNilpotent_representation_rootGenerator chevalleyDatum.basis
      chevalleyDatum.coordinateWeight = definingIdeal := by
  let e := (finCongr rank_F4).sumCongr (finCongr rank_F4)
  have htorus : RingHom.ker
      (GeneralLinear.weightTorusCoordinateMap
        chevalleyDatum.coordinateWeight).hom.toAlgHom.toRingHom =
      RingHom.ker (GeneralLinear.weightTorusCoordinateMap (R := ℤ)
        f4ShortRootWeight).hom.toAlgHom.toRingHom := by
    rw [chevalleyDatum_coordinateWeight]
    exact GeneralLinear.ker_weightTorusCoordinateMap_linearMap
      (LinearEquiv.funCongrLeft ℤ ℤ (finCongr rank_F4)).injective f4ShortRootWeight
  have htest (J : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 26)) :
      J ≤ kostantToralDefiningIdeal (DynkinType.lieBasis .F4 valid_F4).rootGenerator
        (DynkinType.lieBasis .F4 valid_F4).h chevalleyDatum.representation chevalleyDatum.lattice
        chevalleyDatum.representation_mem_lattice
        chevalleyDatum.isNilpotent_representation_rootGenerator chevalleyDatum.basis
        chevalleyDatum.coordinateWeight ↔ J ≤ definingIdeal := by
    rw [definingIdeal_def, le_kostantToralDefiningIdeal_iff, le_kostantToralDefiningIdeal_iff]
    rw [htorus]
    constructor
    · rintro ⟨hr, hT⟩
      refine ⟨?_, hT⟩
      intro k
      obtain ⟨i, rfl⟩ := e.surjective k
      have he : e i = i.map (Fin.cast rank_F4) (Fin.cast rank_F4) := by cases i <;> rfl
      rw [he, ← rootCoordinateMap_eq]
      exact hr i
    · rintro ⟨hr, hT⟩
      refine ⟨?_, hT⟩
      intro i
      rw [rootCoordinateMap_eq]
      exact hr _
  exact le_antisymm ((htest _).mp le_rfl) ((htest _).mpr le_rfl)

/-- The short-root Chevalley datum and the represented integral short-root carrier define the
same group scheme inside `GL₂₆`. -/
theorem chevalleyDatum_groupScheme : chevalleyDatum.groupScheme = groupScheme := by
  rw [DynkinType.ChevalleyDatum.groupScheme, kostantToralGroupScheme, groupScheme_def,
    toralDefiningIdeal_eq]

/-- The integral identification respects the specified inclusions into `GL₂₆`. -/
@[simp↓] theorem eqToHom_chevalleyDatum_groupScheme_comp_carrierι :
    eqToHom chevalleyDatum_groupScheme ≫ carrierι = chevalleyDatum.groupSchemeι := by
  rw [carrierι_def, DynkinType.ChevalleyDatum.groupSchemeι_def,
    kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def, ← Category.assoc]
  -- The quotient transport is stated at the datum dimension, definitionally 26.
  erw [CommHopfAlgCat.eqToHom_comp_quotientSpecι _
    (toralDefiningIdeal_eq.trans definingIdeal_def)]

/-- The datum and the represented carrier have exactly the same matrix-valued points over
every commutative ring. -/
theorem chevalleyDatum_points (A : Type*) [CommRing A] :
    chevalleyDatum.points A = points A := by
  rw [chevalleyDatum.points_eq_kostantToralPointsSubgroup,
    kostantToralPointsSubgroup_def, points_def, toralDefiningIdeal_eq]

/-- The matrix-preserving realization of the pinned short-root datum on the represented
integral carrier. -/
def chevalleyDatumPointsEquiv (A : Type*) [CommRing A] :
    chevalleyDatum.points A ≃* points A :=
  MulEquiv.subgroupCongr (chevalleyDatum_points A)

/-- Realization leaves the matrix unchanged. -/
@[simp] theorem coe_chevalleyDatumPointsEquiv (A : Type*) [CommRing A]
    (g : chevalleyDatum.points A) :
    (chevalleyDatumPointsEquiv A g : Matrix.GeneralLinearGroup (Fin 26) A) = g :=
  (rfl)

/-- Inverse realization leaves the matrix unchanged. -/
@[simp] theorem coe_chevalleyDatumPointsEquiv_symm (A : Type*) [CommRing A] (g : points A) :
    ((chevalleyDatumPointsEquiv A).symm g : Matrix.GeneralLinearGroup (Fin 26) A) = g :=
  (rfl)

/-- Realization matches the positive simple-root maps, with the native Bourbaki node adapter
and unchanged additive parameter. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex
    (i : Fin DynkinType.F4.rank) (A : Type*) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv A
        (chevalleyDatum.rootSubgroupPoints (DynkinType.F4.simpleIndex valid_F4 i) A u) =
      rootSubgroupPoints (.inl (Fin.cast rank_F4 i)) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_simpleIndex, coe_rootSubgroupPoints]
  apply kostantRootSubgroupMatrix_eq_of_action_eq
  rw [chevalleyDatum_representation_rootGenerator_inl, rep_ι,
    rationalSerreRepresentation_serreRootGenerator, rootMatrixRat_inl]

/-- Realization also matches the negative simple-root maps, with no sign change. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex
    (i : Fin DynkinType.F4.rank) (A : Type*) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv A
        (chevalleyDatum.rootSubgroupPoints
          ((DynkinType.F4.simplyConnectedRootDatum valid_F4).reflectionPerm
            (DynkinType.F4.simpleIndex valid_F4 i) (DynkinType.F4.simpleIndex valid_F4 i)) A u) =
      rootSubgroupPoints (.inr (Fin.cast rank_F4 i)) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex,
    coe_rootSubgroupPoints]
  apply kostantRootSubgroupMatrix_eq_of_action_eq
  rw [chevalleyDatum_representation_rootGenerator_inr, rep_ι,
    rationalSerreRepresentation_serreRootGenerator, rootMatrixRat_inr]

/-- Inverse realization recovers a positive simple-root element with unchanged parameter. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl
    (i : Fin 4) (A : Type*) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (rootSubgroupPoints (.inl i) A u) =
      chevalleyDatum.rootSubgroupPoints
        (DynkinType.F4.simpleIndex valid_F4 (Fin.cast rank_F4.symm i)) A u := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

/-- Inverse realization recovers a negative simple-root element without a sign change. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr
    (i : Fin 4) (A : Type*) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (rootSubgroupPoints (.inr i) A u) =
      chevalleyDatum.rootSubgroupPoints
        ((DynkinType.F4.simplyConnectedRootDatum valid_F4).reflectionPerm
          (DynkinType.F4.simpleIndex valid_F4 (Fin.cast rank_F4.symm i))
          (DynkinType.F4.simpleIndex valid_F4 (Fin.cast rank_F4.symm i))) A u := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

/-- The actual weight torus matches the represented fundamental-weight torus. The tuple
adapter only changes `Fin F4.rank` to `Fin 4`. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_torusPoints
    (A : Type*) [CommRing A] (s : Fin 4 → Aˣ) :
    chevalleyDatumPointsEquiv A
        (chevalleyDatum.torusPoints A (s ∘ Fin.cast rank_F4)) = weightTorusPoints A s := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, DynkinType.ChevalleyDatum.coe_torusPoints,
    coe_weightTorusPoints, kostantTorusMatrix_apply, kostantTorusMatrix_apply]
  congr 1
  funext a
  rw [chevalleyDatum_coordinateWeight, torusCharacter_def, torusCharacter_def]
  exact Fintype.prod_equiv (finCongr rank_F4) _ _ (fun _ => rfl)

/-- Inverse realization recovers the actual torus point in fundamental-weight coordinates. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_symm_weightTorusPoints
    (A : Type*) [CommRing A] (s : Fin 4 → Aˣ) :
    (chevalleyDatumPointsEquiv A).symm (weightTorusPoints A s) =
      chevalleyDatum.torusPoints A (s ∘ Fin.cast rank_F4) := by
  apply (chevalleyDatumPointsEquiv A).injective
  simp

/-- Realization commutes with changing the coefficient ring, including maps between different
universes and noninjective maps. -/
theorem chevalleyDatumPointsEquiv_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv B
        ((chevalleyDatum.pointsPresentation A).map (chevalleyDatum.pointsPresentation B) f g) =
      (pointsPresentation A).map (pointsPresentation B) f (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv]
  -- The presented-point maps use the datum dimension rather than the displayed dimension 26.
  erw [GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map]
  rfl

/-- Realization intertwines the two independently defined whole-point Frobenius maps. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type*) [CommRing A]
    [ExpChar A p] (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.frobenius p k A g) =
      frobenius p k A (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, DynkinType.ChevalleyDatum.coe_frobenius,
    coe_frobenius, coe_chevalleyDatumPointsEquiv]

/-- Inverse realization intertwines Frobenius as well. -/
@[simp↓] theorem chevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type*) [CommRing A]
    [ExpChar A p] (g : points A) :
    (chevalleyDatumPointsEquiv A).symm (frobenius p k A g) =
      chevalleyDatum.frobenius p k A ((chevalleyDatumPointsEquiv A).symm g) := by
  apply (chevalleyDatumPointsEquiv A).injective
  rw [MulEquiv.apply_symm_apply, chevalleyDatumPointsEquiv_frobenius,
    MulEquiv.apply_symm_apply]

end

end TauCeti.F4ShortRoot
