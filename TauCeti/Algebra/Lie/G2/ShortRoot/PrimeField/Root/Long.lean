/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Positive
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Positive long root spaces of the short-root G₂ carrier

In characteristic three, iterated Lie brackets of the two simple positive root vectors do not
reach the nonsimple long roots. Conjugation by a short-root group element retains the divided
cubic term that these brackets lose. This file uses that action to construct the root line at
`3α₁ + α₂`, and its bracket with the second simple root vector gives the line at `3α₁ + 2α₂`.
Both lines lie in the Lie algebra of the positive subgroup, so the two characters are intrinsic
positive roots. This supplies the long-root part of the carrier's root-space identification;
no comparison with an independently pinned group scheme is asserted.

## Main declarations

* `longRootVector` and `highestLongRootVector`: nonzero tangent vectors at the two roots.
* `adjointWeightSpace_long_eq_span` and `adjointWeightSpace_highestLong_eq_span`: the entire root
  spaces are the corresponding lines, with characters in the actual integral weight lattice.
* `isPositiveRoot_long` and `isPositiveRoot_highestLong`: intrinsic positivity of both roots.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The matrix and cross-product calculations use the conventions of
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Simple`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

local notation "F" => ZMod 3
local notation "P" => Positive.coordinateHopfAlgebra
local notation "D" => Derivation F P (Bialgebra.CounitAlgebra F P F)

private def positiveRootDerivation (i : Fin 2) : D :=
  derivationComp (B := F) (CommHopfAlgCat.commonKernelLift Positive.generator (.inl i)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := F) (B := F)).symm 1)

private def positiveRootPoint (u : F) : WithConv (P →ₐ[F] F) :=
  BialgHom.mapDomain (CommHopfAlgCat.commonKernelLift Positive.generator (.inl 0)).hom
    ((AdditiveGroup.gaPointsMulEquiv (R := F) (A := F)).symm (Multiplicative.ofAdd u))

private def includePositiveTangent (d : D) :
    Module.Dual F (Bialgebra.CotangentSpace F carrierAlgebra) :=
  (Derivation.cotangentLinearEquiv (B := F)).symm
    (derivationComp (B := F) positiveRestriction.hom d)

private theorem includePositiveTangent_mem (d : D) :
    Derivation.cotangentLinearEquiv (B := F) (includePositiveTangent d) ∈
      positiveDefiningIdeal.lieSubalgebra := by
  rw [includePositiveTangent, LinearEquiv.apply_symm_apply, HopfIdeal.mem_lieSubalgebra_iff]
  intro x hx
  have hz := (mem_positiveDefiningIdeal x).mp hx
  apply (Bialgebra.CounitAlgebra.algEquivSelf F carrierAlgebra F).injective
  rw [algEquivSelf_derivationComp_apply]
  simpa only [map_zero, BialgHom.coe_toAlgHom] using congrArg
    (fun z => Bialgebra.CounitAlgebra.algEquivSelf F P F (d z)) hz

private theorem positiveRestriction_comp_root (i : Fin 2) :
    positiveRestriction ≫ CommHopfAlgCat.commonKernelLift Positive.generator (.inl i) =
      CommHopfAlgCat.commonKernelLift generator (.inl (.inl i)) := by
  apply (cancel_epi (CommHopfAlgCat.mkQuotient _ _)).1
  rw [CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift, Positive.generator_inl]

private theorem includePositiveTangent_root (i : Fin 2) :
    includePositiveTangent (positiveRootDerivation i) = rootVector (.inl i) := by
  apply (Derivation.cotangentLinearEquiv (B := F)).injective
  rw [cotangentLinearEquiv_rootVector, includePositiveTangent, LinearEquiv.apply_symm_apply]
  ext x
  apply (Bialgebra.CounitAlgebra.algEquivSelf F carrierAlgebra F).injective
  have h := congrArg (fun f => f.hom x) (positiveRestriction_comp_root i)
  simpa only [positiveRootDerivation, algEquivSelf_derivationComp_apply,
    BialgHom.coe_toAlgHom, CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using congrArg
      (fun y => Bialgebra.CounitAlgebra.algEquivSelf F
        (AdditiveGroup.coordinateHopfAlgebra F) F
          (((AdditiveGroup.gaTangentLinearEquiv (R := F) (B := F)).symm 1) y)) h

private theorem tangentMatrix_includePositiveTangent (d : D) :
    tangentMatrix (includePositiveTangent d) =
      GeneralLinear.tangentMatrix 7 (HopfIdeal.quotientLieHom Positive.definingIdeal d) := by
  rw [tangentMatrix_apply, includePositiveTangent, LinearEquiv.apply_symm_apply]
  apply congrArg (GeneralLinear.tangentMatrix 7)
  ext x
  apply (Bialgebra.CounitAlgebra.algEquivSelf F
    (GeneralLinear.coordinateHopfAlgebra F 7) F).injective
  have h := congrArg (fun f => f.hom x)
    (CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe _ Positive.carrierDefiningIdeal_le)
  simpa only [HopfIdeal.quotientLieHom_apply, algEquivSelf_derivationComp_apply,
    BialgHom.coe_toAlgHom, CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    CommHopfAlgCat.hom_mkQuotient] using congrArg
      (fun y => Bialgebra.CounitAlgebra.algEquivSelf F P F (d y)) h

private theorem ambient_positiveRootPoint (u : F) :
    GeneralLinear.counitPointsMulEquiv 7
      (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra F
          (GeneralLinear.coordinateHopfAlgebra F 7) F)
        (Bialgebra.Quotient.mkBialgHom Positive.definingIdeal.toIdeal)
        (Derivation.pointInCounitAlgebra F (positiveRootPoint u))) =
      (rootSubgroupPoints (.inl 0) F (Multiplicative.ofAdd u) :
        Matrix.GeneralLinearGroup (Fin 7) F) := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := F) (A := F)).symm
    (Multiplicative.ofAdd u)
  have heq : BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom Positive.definingIdeal.toIdeal)
      (positiveRootPoint u) =
      (CommHopfAlgCat.Hom.mapPointsFunctor (generator (.inl (.inl 0)))).app
        (CommAlgCat.of F F) q := by
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
    apply WithConv.ofConv_injective
    ext x
    have h := congrArg (fun f => f.hom x)
      (CommHopfAlgCat.mkQuotient_comp_commonKernelLift Positive.generator (.inl 0))
    simpa only [positiveRootPoint, BialgHom.mapDomain_apply_apply, CommHopfAlgCat.hom_comp,
      BialgHom.comp_apply, CommHopfAlgCat.hom_mkQuotient,
      Bialgebra.Quotient.mkBialgHom_apply, Positive.generator_inl, Positive.definingIdeal,
      AlgHom.comp_apply, BialgHom.coe_toAlgHom, q] using congrArg q.ofConv h
  have hcounit := Derivation.pointInCounitAlgebra_comp F
    (Bialgebra.Quotient.mkBialgHom Positive.definingIdeal.toIdeal)
    (positiveRootPoint u).ofConv
  rw [← hcounit, GeneralLinear.counitPointsMulEquiv_eq_pointsMulEquiv]
  have hpoint : AlgHom.mapValue
      (Bialgebra.CounitAlgebra.algEquivSelf F
        (GeneralLinear.coordinateHopfAlgebra F 7) F).toAlgHom
      (Derivation.pointInCounitAlgebra F
        (toConv ((positiveRootPoint u).ofConv.comp
          (Bialgebra.Quotient.mkBialgHom Positive.definingIdeal.toIdeal).toAlgHom))) =
      BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom Positive.definingIdeal.toIdeal)
        (positiveRootPoint u) := by
    apply WithConv.ofConv_injective
    ext x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Derivation.pointInCounitAlgebra_apply, BialgHom.mapDomain_apply,
      AlgEquiv.coe_toAlgHom]
    exact Bialgebra.CounitAlgebra.algEquivSelf_apply F
      (GeneralLinear.coordinateHopfAlgebra F 7) F _
  rw [hpoint, heq, ← coe_rootSubgroupPoints_gaPointsMulEquiv]
  simp [q]

private theorem tangentMatrix_positiveAd (u : F) (d : D) :
    tangentMatrix (includePositiveTangent
      (Derivation.adDerivation F (Derivation.pointInCounitAlgebra F (positiveRootPoint u)) d)) =
      ((rootSubgroupPoints (.inl 0) F (Multiplicative.ofAdd u) :
          Matrix.GeneralLinearGroup (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) *
        tangentMatrix (includePositiveTangent d) *
      ((rootSubgroupPoints (.inl 0) F (Multiplicative.ofAdd (-u)) :
          Matrix.GeneralLinearGroup (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) := by
  rw [tangentMatrix_includePositiveTangent, HopfIdeal.quotientLieHom_adDerivation,
    GeneralLinear.tangentMatrix_adDerivation, ambient_positiveRootPoint,
    ← tangentMatrix_includePositiveTangent]
  congr 2
  exact congrArg (fun g : points F => (g : Matrix.GeneralLinearGroup (Fin 7) F))
    ((map_inv (rootSubgroupPoints (.inl 0) F) (Multiplicative.ofAdd u)).symm)

private def positiveLongDerivation : D :=
  Derivation.adDerivation F (Derivation.pointInCounitAlgebra F (positiveRootPoint 1))
      (positiveRootDerivation 1) - positiveRootDerivation 1 -
    ⁅positiveRootDerivation 0, positiveRootDerivation 1⁆ +
    ⁅positiveRootDerivation 0, ⁅positiveRootDerivation 0, positiveRootDerivation 1⁆⁆

/-- The positive tangent vector at `3α₁ + α₂` obtained from conjugation by `x_{α₁}(1)` after
subtracting the terms of short-root string degrees zero, one and two. -/
def longRootVector : Module.Dual F (Bialgebra.CotangentSpace F carrierAlgebra) :=
  includePositiveTangent positiveLongDerivation

/-- The positive tangent vector at the highest root `3α₁ + 2α₂`, normalized as the negative
bracket of the second simple root vector with `longRootVector`. -/
def highestLongRootVector : Module.Dual F (Bialgebra.CotangentSpace F carrierAlgebra) :=
  includePositiveTangent (-⁅positiveRootDerivation 1, positiveLongDerivation⁆)

/-- The highest-root normalization agrees with the bracket of the corresponding carrier
vectors, not only with their ambient matrices. -/
theorem cotangentLinearEquiv_highestLongRootVector :
    Derivation.cotangentLinearEquiv (B := F) highestLongRootVector =
      -⁅Derivation.cotangentLinearEquiv (B := F) (rootVector (.inl 1)),
        Derivation.cotangentLinearEquiv (B := F) longRootVector⁆ := by
  have he := congrArg (Derivation.cotangentLinearEquiv (B := F)) (includePositiveTangent_root 1)
  simp only [includePositiveTangent, LinearEquiv.apply_symm_apply] at he
  rw [highestLongRootVector, longRootVector, includePositiveTangent, includePositiveTangent,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_neg]
  rw [← derivationCompLieHom_apply, LieHom.map_lie, derivationCompLieHom_apply,
    derivationCompLieHom_apply, he]

/-- The matrix of the nonsimple positive long-root vector. -/
@[simp↓]
theorem tangentMatrix_longRootVector :
    tangentMatrix longRootVector =
      !![0, 0, 0, 0, 1, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 2;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  rw [longRootVector, positiveLongDerivation, tangentMatrix_includePositiveTangent]
  simp only [map_add, map_sub, LieHom.map_lie, GeneralLinear.tangentMatrix_lie]
  simp only [← tangentMatrix_includePositiveTangent]
  rw [tangentMatrix_positiveAd]
  simp only [includePositiveTangent_root]
  rw [tangentMatrix_rootVector, tangentMatrix_rootVector]
  simp only [rootMatrix_inl, coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints_inl_zero, Ring.lie_def]
  decide

/-- The matrix of the highest positive root vector. -/
@[simp↓]
theorem tangentMatrix_highestLongRootVector :
    tangentMatrix highestLongRootVector =
      !![0, 0, 0, 0, 0, 1, 0;
        0, 0, 0, 0, 0, 0, 1;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  rw [highestLongRootVector, tangentMatrix_includePositiveTangent]
  simp only [map_neg, LieHom.map_lie, GeneralLinear.tangentMatrix_lie,
    ← tangentMatrix_includePositiveTangent]
  rw [includePositiveTangent_root, ← longRootVector, tangentMatrix_longRootVector,
    tangentMatrix_rootVector, rootMatrix_inl, Ring.lie_def]
  decide

/-- The vector at `3α₁ + α₂` lies in the tangent Lie algebra of the positive subgroup. -/
theorem cotangentLinearEquiv_longRootVector_mem :
    Derivation.cotangentLinearEquiv (B := F) longRootVector ∈
      positiveDefiningIdeal.lieSubalgebra :=
  includePositiveTangent_mem _

/-- The highest-root vector lies in the tangent Lie algebra of the positive subgroup. -/
theorem cotangentLinearEquiv_highestLongRootVector_mem :
    Derivation.cotangentLinearEquiv (B := F) highestLongRootVector ∈
      positiveDefiningIdeal.lieSubalgebra :=
  includePositiveTangent_mem _

/-- The long-root vector is nonzero, as witnessed by its `(0, 4)` matrix entry. -/
@[simp]
theorem longRootVector_ne_zero : longRootVector ≠ 0 := by
  intro h
  have he := congrFun (congrFun (congrArg tangentMatrix h) 0) 4
  rw [tangentMatrix_longRootVector, map_zero] at he
  exact absurd he (by decide)

/-- The highest-root vector is nonzero, as witnessed by its `(0, 5)` matrix entry. -/
@[simp]
theorem highestLongRootVector_ne_zero : highestLongRootVector ≠ 0 := by
  intro h
  have he := congrFun (congrFun (congrArg tangentMatrix h) 0) 5
  rw [tangentMatrix_highestLongRootVector, map_zero] at he
  exact absurd he (by decide)

/- Normalization of a cross-product derivation equation, following the simple-root calculation. -/
local macro "cross_entry_norm" : tactic =>
  `(tactic| (simp [Matrix.mul_apply, Fin.sum_univ_succ,
    ConstantMultiplication.imageStructureMatrix_def, crossOperator_def]; ring_nf; reduce_mod_char))

private theorem long_space_upper_bound (b : Bool)
    (X : Matrix (Fin 7) (Fin 7) F)
    (hX : ∀ c, X * crossOperatorPrime c =
      ConstantMultiplication.imageStructureMatrix F 7 crossOperatorPrime X c +
        crossOperatorPrime c * X)
    (hsupp : ∀ i j, weight i - weight j ≠ (if b then ![0, 1] else ![3, -1]) → X i j = 0) :
    X = (if b then X 0 5 else X 0 4) •
      tangentMatrix (if b then highestLongRootVector else longRootVector) := by
  cases b
  · have he : X = !![0, 0, 0, 0, X 0 4, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, X 2 6;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
    rw [he] at hX
    have h26 : X 2 6 = 2 * X 0 4 := by
      linear_combination (norm := cross_entry_norm) congrFun (congrFun (hX 1) 0) 6
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [tangentMatrix_longRootVector]
    conv_lhs => rw [he]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h26, mul_comm]
  · have he : X = !![0, 0, 0, 0, 0, X 0 5, 0;
        0, 0, 0, 0, 0, 0, X 1 6;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
    rw [he] at hX
    have h16 : X 1 6 = X 0 5 := by
      linear_combination (norm := cross_entry_norm) 2 * congrFun (congrFun (hX 2) 0) 6
    simp only [↓reduceIte]
    rw [tangentMatrix_highestLongRootVector]
    conv_lhs => rw [he]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h16]

private theorem long_space_eq_span (b : Bool) :
    Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
        (SplitTorus.weightCharacter (if b then ![0, 1] else ![3, -1])) =
      F ∙ (if b then highestLongRootVector else longRootVector) := by
  apply le_antisymm
  · intro x hx
    have hsupp : ∀ i j, weight i - weight j ≠ (if b then ![0, 1] else ![3, -1]) →
        tangentMatrix x i j = 0 := by
      intro i j h
      apply (mem_adjointWeightSpace_iff _ x).mp hx i j
      intro he
      apply h
      funext l
      simpa only [SplitTorus.toAdd_weightCharacter, Pi.sub_apply] using
        congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) => Multiplicative.toAdd χ l) he
    refine Submodule.mem_span_singleton.mpr
      ⟨(if b then tangentMatrix x 0 5 else tangentMatrix x 0 4), tangentMatrix_injective ?_⟩
    rw [map_smul]
    exact (long_space_upper_bound b _ (tangentMatrix_mul_crossOperatorPrime x) hsupp).symm
  · rw [Submodule.span_singleton_le_iff_mem, mem_adjointWeightSpace_iff]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      intro i j h
      contrapose! h
      apply congrArg SplitTorus.weightCharacter
      first | rw [tangentMatrix_longRootVector] at h |
        rw [tangentMatrix_highestLongRootVector] at h
      revert h
      fin_cases i <;> fin_cases j <;> decide

private theorem long_character_coordinates (b : Bool) :
    Multiplicative.ofAdd (3 • simpleRootCharacter 0 +
        (if b then 2 else 1) • simpleRootCharacter 1) =
      SplitTorus.weightCharacter (fun l : ULift.{0} (Fin 2) =>
        (if b then ![0, 1] else ![3, -1]) l.down) := by
  apply Multiplicative.toAdd.injective
  ext ⟨j⟩
  cases b <;> fin_cases j <;>
    norm_num [SplitTorus.toAdd_weightCharacter, simpleRootCharacter_apply]
  -- The uniform Dynkin datum has rank and root-count wrappers; `erw` matches the concrete table.
  all_goals erw [DynkinType.g2Root_apply, DynkinType.g2Root_apply]; norm_num

private theorem long_space_split_eq_span (b : Bool) :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd (3 • simpleRootCharacter 0 +
          (if b then 2 else 1) • simpleRootCharacter 1)) =
      F ∙ (if b then highestLongRootVector else longRootVector) := by
  -- The torus character-group carrier is a bundled copy of the integral finitely supported lattice.
  erw [long_character_coordinates b]
  rw [adjointWeightSpace_splitMaximalTorus_weightCharacter_eq_weightTorus, long_space_eq_span]

/-- The root space of `3α₁ + α₂` in the chosen split maximal torus is the constructed line. -/
theorem adjointWeightSpace_long_eq_span :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd (3 • simpleRootCharacter 0 + simpleRootCharacter 1)) =
      F ∙ longRootVector := by
  simpa only [Bool.false_eq_true, ↓reduceIte, one_smul] using long_space_split_eq_span false

/-- The root space of the highest root `3α₁ + 2α₂` is the constructed line. -/
theorem adjointWeightSpace_highestLong_eq_span :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd (3 • simpleRootCharacter 0 + 2 • simpleRootCharacter 1)) =
      F ∙ highestLongRootVector :=
  long_space_split_eq_span true

private theorem isPositiveRoot_long_character (b : Bool) :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal
      (3 • simpleRootCharacter 0 + (if b then 2 else 1) • simpleRootCharacter 1) := by
  rw [SplitMaximalTorus.isPositiveRoot_iff, Derivation.mem_nontrivialAdjointWeights]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    rw [long_character_coordinates] at h
    have he := congrArg (fun χ : Multiplicative (ULift.{0} (Fin 2) →₀ ℤ) =>
      Multiplicative.toAdd χ (ULift.up 1)) h
    cases b <;> norm_num [SplitTorus.toAdd_weightCharacter] at he
  · apply (Submodule.ne_bot_iff _).mpr
    refine ⟨_, (long_space_split_eq_span b).symm ▸
      Submodule.mem_span_singleton_self _, ?_⟩
    cases b
    · exact longRootVector_ne_zero
    · exact highestLongRootVector_ne_zero
  · intro x hx
    rw [long_space_split_eq_span b] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    apply positiveDefiningIdeal.lieSubalgebra.smul_mem c
    cases b
    · exact cotangentLinearEquiv_longRootVector_mem
    · exact cotangentLinearEquiv_highestLongRootVector_mem

/-- The nonsimple long root `3α₁ + α₂` is an intrinsic positive root of the carrier. -/
theorem isPositiveRoot_long :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal
      (3 • simpleRootCharacter 0 + simpleRootCharacter 1) := by
  simpa only [Bool.false_eq_true, ↓reduceIte, one_smul] using isPositiveRoot_long_character false

/-- The highest root `3α₁ + 2α₂` is an intrinsic positive root of the carrier. -/
theorem isPositiveRoot_highestLong :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal
      (3 • simpleRootCharacter 0 + 2 • simpleRootCharacter 1) :=
  isPositiveRoot_long_character true

end

end TauCeti.G2ShortRoot.PrimeField
