/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Algebra
public import TauCeti.RingTheory.Ideal.Extended
public import Mathlib.RingTheory.AdicCompletion.Basic

import Mathlib.RingTheory.AdicCompletion.Completeness

import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Completion along an extended ideal

For a possibly noncommutative `R`-algebra `A`, completion of the powers of the ideal extended
from `I : Ideal R` has the same underlying `R`-module as `AdicCompletion I A`. When `I` is
finitely generated, its finite reductions are the corresponding reductions of `A`.

The motivating example is the integral completion of a universal enveloping algebra.
-/

noncomputable section

public section

namespace AdicCompletion

open TauCeti.ModuleTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (I : Ideal R)

/-- The module quotient by `I ^ n • A` is the quotient by the `n`-th extended ideal power. -/
def extendedIdealQuotientEquiv (n : ℕ) :
    (A ⧸ (I ^ n • (⊤ : Submodule R A))) ≃ₗ[R]
      A ⧸ (I.map (algebraMap R A)) ^ n :=
  Submodule.quotEquivOfEqRestrictScalars _ _
    (I.pow_smul_top_eq_restrictScalars_map_pow n)

/-- The quotient comparison sends each representative to its class in the ideal quotient. -/
@[simp]
theorem extendedIdealQuotientEquiv_mk (n : ℕ) (a : A) :
    extendedIdealQuotientEquiv (A := A) I n (Submodule.Quotient.mk a) =
      Ideal.Quotient.mk _ a := by
  rw [extendedIdealQuotientEquiv, Submodule.quotEquivOfEqRestrictScalars_mk,
    Ideal.Quotient.mk_eq_mk]

/-- The inverse quotient comparison sends a representative class to the module quotient. -/
@[simp]
theorem extendedIdealQuotientEquiv_symm_mk (n : ℕ) (a : A) :
    (extendedIdealQuotientEquiv (A := A) I n).symm (Ideal.Quotient.mk _ a) =
      Submodule.Quotient.mk a := by
  rw [extendedIdealQuotientEquiv, ← Ideal.Quotient.mk_eq_mk,
    Submodule.quotEquivOfEqRestrictScalars_symm_mk]

private def reductionQuotientEquiv (n : ℕ) :
    (reduction I A).obj (Opposite.op n) ≃ₗ[R]
      A ⧸ (I.map (algebraMap R A)).algFiltration.ideal (n + 1) :=
  (quotientsObjEquiv _ (I.pow_succ_smul_top_antitone A) n).trans
    ((extendedIdealQuotientEquiv I (n + 1)).trans
      (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (n + 1))).symm.toLinearEquiv)

private theorem reductionQuotientEquiv_π (n : ℕ) (a : A) :
    reductionQuotientEquiv I n (reductionπ I A n a) = Ideal.Quotient.mk _ a := by
  simp only [reductionQuotientEquiv, LinearEquiv.trans_apply, quotientsObjEquiv_quotientsπ,
    extendedIdealQuotientEquiv_mk, AlgEquiv.toLinearEquiv_apply,
    Ideal.quotientEquivAlgOfEq_symm, Ideal.quotientEquivAlgOfEq_mk]

private theorem factor_reductionQuotientEquiv {m n : ℕ} (h : m ≤ n)
    (x : (reduction I A).obj (Opposite.op n)) :
    Ideal.Quotient.factor ((I.map (algebraMap R A)).algFiltration.antitone
        (Nat.add_le_add_right h 1)) (reductionQuotientEquiv I n x) =
      reductionQuotientEquiv I m ((reduction I A).transitionOfLE h x) := by
  obtain ⟨a, rfl⟩ := quotientsπ_surjective _ _ n x
  rw [transitionOfLE_quotientsπ, reductionQuotientEquiv_π, reductionQuotientEquiv_π,
    Ideal.Quotient.factor_mk]

private theorem projection_smul (n : ℕ) (r : R)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    (I.map (algebraMap R A)).algFiltration.projection n (r • x) =
      r • (I.map (algebraMap R A)).algFiltration.projection n x := by
  simpa only [TauCeti.AlgFiltration.projectionₐ_apply] using
    map_smul ((I.map (algebraMap R A)).algFiltration.projectionₐ (R := R) n) r x

private def toExtendedIdealCompletion :
    (reduction I A).lim →ₗ[R] (I.map (algebraMap R A)).algFiltration.completion where
  toFun x := ⟨fun k => reductionQuotientEquiv I k.unop ((reduction I A).limπ k.unop x), by
    apply (I.map (algebraMap R A)).algFiltration.mem_completion_iff _ |>.mpr
    intro k l h
    rw [factor_reductionQuotientEquiv I h, ← LinearMap.comp_apply,
      transitionOfLE_comp_limπ]⟩
  map_add' x y := by
    apply (I.map (algebraMap R A)).algFiltration.completion_ext
    intro k
    simp only [TauCeti.AlgFiltration.projection_apply, map_add]
  map_smul' r x := by
    apply (I.map (algebraMap R A)).algFiltration.completion_ext
    intro k
    rw [projection_smul]
    simp only [TauCeti.AlgFiltration.projection_apply, map_smul, RingHom.id_apply]

private theorem projection_toExtendedIdealCompletion (k : ℕ) (x : (reduction I A).lim) :
    (I.map (algebraMap R A)).algFiltration.projection k (toExtendedIdealCompletion I x) =
      reductionQuotientEquiv I k ((reduction I A).limπ k x) := by
  rw [TauCeti.AlgFiltration.projection_apply]
  rfl

private def ofExtendedIdealCompletion :
    (I.map (algebraMap R A)).algFiltration.completion →ₗ[R] (reduction I A).lim :=
  (reduction I A).limLift (fun n => (reductionQuotientEquiv I n).symm.toLinearMap.comp
    ((I.map (algebraMap R A)).algFiltration.projectionₐ (R := R) n).toLinearMap) (by
      intro n
      ext x
      apply (reductionQuotientEquiv I n).injective
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
        TauCeti.AlgFiltration.projectionₐ_apply, LinearEquiv.apply_symm_apply]
      rw [← transitionOfLE_succ, ← factor_reductionQuotientEquiv I n.le_succ,
        LinearEquiv.apply_symm_apply,
        TauCeti.AlgFiltration.factor_projection _ n.le_succ x])

private theorem limπ_ofExtendedIdealCompletion (k : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    (reduction I A).limπ k (ofExtendedIdealCompletion I x) =
      (reductionQuotientEquiv I k).symm
        ((I.map (algebraMap R A)).algFiltration.projection k x) := by
  rw [ofExtendedIdealCompletion, ← LinearMap.comp_apply, limπ_comp_limLift]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    TauCeti.AlgFiltration.projectionₐ_apply]

private def reductionCompletionEquiv :
    (reduction I A).lim ≃ₗ[R] (I.map (algebraMap R A)).algFiltration.completion where
  __ := toExtendedIdealCompletion I
  invFun := ofExtendedIdealCompletion I
  left_inv x := by
    apply (reduction I A).lim_ext
    intro k
    change (reduction I A).limπ k
      (ofExtendedIdealCompletion I (toExtendedIdealCompletion I x)) = _
    rw [limπ_ofExtendedIdealCompletion, projection_toExtendedIdealCompletion,
      (reductionQuotientEquiv I k).symm_apply_apply]
  right_inv x := by
    apply (I.map (algebraMap R A)).algFiltration.completion_ext
    intro k
    change (I.map (algebraMap R A)).algFiltration.projection k
      (toExtendedIdealCompletion I (ofExtendedIdealCompletion I x)) = _
    rw [projection_toExtendedIdealCompletion, limπ_ofExtendedIdealCompletion,
      (reductionQuotientEquiv I k).apply_symm_apply]

/-- The completion of the extended ideal filtration agrees, as an `R`-module, with the
module-adic completion. No commutativity of `A` is needed. -/
def extendedIdealCompletionEquiv :
    AdicCompletion I A ≃ₗ[R] (I.map (algebraMap R A)).algFiltration.completion :=
  (limReductionEquiv I A).symm.trans (reductionCompletionEquiv I)

/-- After the canonical identification of quotient ideals, the completion comparison preserves
all positive-order projections. -/
@[simp]
theorem extendedIdealCompletionEquiv_projection (k : ℕ) (x : AdicCompletion I A) :
    Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
      ((I.map (algebraMap R A)).algFiltration.projection k
        (extendedIdealCompletionEquiv I x)) =
      extendedIdealQuotientEquiv I (k + 1) (eval I A (k + 1) x) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (eval I A (k + 1) x)
  have hval : x.val (k + 1) = Submodule.Quotient.mk a := by
    simpa only [eval_apply] using ha.symm
  rw [extendedIdealCompletionEquiv, LinearEquiv.trans_apply]
  change Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
    ((I.map (algebraMap R A)).algFiltration.projection k
      (toExtendedIdealCompletion I ((limReductionEquiv I A).symm x))) = _
  rw [projection_toExtendedIdealCompletion, limπ_limReductionEquiv_symm_apply I A hval,
    reductionQuotientEquiv_π, Ideal.quotientEquivAlgOfEq_mk, ← ha,
    extendedIdealQuotientEquiv_mk]

/-- The comparison preserves the canonical image of the uncompleted algebra. -/
@[simp]
theorem extendedIdealCompletionEquiv_of (a : A) :
    extendedIdealCompletionEquiv I (of I A a) =
      (I.map (algebraMap R A)).algFiltration.toCompletion a := by
  apply (I.map (algebraMap R A)).algFiltration.completion_ext
  intro k
  apply (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).injective
  rw [extendedIdealCompletionEquiv_projection, eval_of, Submodule.mkQ_apply,
    extendedIdealQuotientEquiv_mk, TauCeti.AlgFiltration.projection_toCompletion,
    Ideal.quotientEquivAlgOfEq_mk]

/-- The inverse comparison has the prescribed positive-order module projections. -/
@[simp]
theorem extendedIdealCompletionEquiv_symm_eval (k : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    extendedIdealQuotientEquiv I (k + 1)
      (((extendedIdealCompletionEquiv I).symm x).val (k + 1)) =
      Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
        ((I.map (algebraMap R A)).algFiltration.projection k x) := by
  simpa only [coe_eval, LinearEquiv.apply_symm_apply] using
    (extendedIdealCompletionEquiv_projection I k ((extendedIdealCompletionEquiv I).symm x)).symm

/-- For a finitely generated base ideal, a finite projection kills precisely the corresponding
power of the ideal extended to the completed algebra. -/
theorem extendedIdealCompletion_ker_projection (hI : I.FG) (k : ℕ) :
    RingHom.ker ((I.map (algebraMap R A)).algFiltration.projection k) =
      (I.map (algebraMap R (I.map (algebraMap R A)).algFiltration.completion)) ^ (k + 1) := by
  let e := extendedIdealCompletionEquiv (A := A) I
  have h := congrArg (fun N : Submodule R (AdicCompletion I A) => N.map e.toLinearMap)
    (pow_smul_top_eq_ker_eval (M := A) (n := k + 1) hI)
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at h
  rw [Ideal.pow_smul_top_eq_restrictScalars_map_pow] at h
  ext x
  rw [RingHom.mem_ker]
  rw [← Submodule.restrictScalars_mem R, h]
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (extendedIdealQuotientEquiv I (k + 1)).injective
    simp only [e, coe_eval, extendedIdealCompletionEquiv_symm_eval, hx, _root_.map_zero]
  · rintro ⟨y, hy, rfl⟩
    apply (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).injective
    simp only [e, extendedIdealCompletionEquiv_projection, hy, _root_.map_zero]

/-- The finite-order projection with target expressed as a power of the extended ideal. -/
def extendedIdealCompletionProjection (k : ℕ) :
    (I.map (algebraMap R A)).algFiltration.completion →ₐ[R]
      A ⧸ (I.map (algebraMap R A)) ^ (k + 1) :=
  (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).toAlgHom.comp
    ((I.map (algebraMap R A)).algFiltration.projectionₐ (R := R) k)

/-- The concrete extended-ideal projection is the filtration projection followed by the
canonical identification of its quotient ideal. -/
theorem extendedIdealCompletionProjection_apply (k : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    extendedIdealCompletionProjection I k x =
      Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
      ((I.map (algebraMap R A)).algFiltration.projection k x) := by
  simp only [extendedIdealCompletionProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    TauCeti.AlgFiltration.projectionₐ_apply]

private theorem reduction_ker (hI : I.FG) (k : ℕ) :
    RingHom.ker (extendedIdealCompletionProjection (A := A) I k) =
      (I.map (algebraMap R (I.map (algebraMap R A)).algFiltration.completion)) ^ (k + 1) := by
  rw [← extendedIdealCompletion_ker_projection I hI k]
  let e := Ideal.quotientEquivAlgOfEq R
    (Ideal.algFiltration_ideal (I.map (algebraMap R A)) (k + 1))
  change RingHom.ker (e.toRingEquiv.toRingHom.comp
    (((I.map (algebraMap R A)).algFiltration.projectionₐ (R := R) k).toRingHom)) = _
  have he : Function.Injective e.toRingEquiv.toRingHom := e.injective
  rw [RingHom.ker_comp_of_injective _ he]
  exact congrArg RingHom.ker (TauCeti.AlgFiltration.coe_projectionₐ
    (R := R) (I.map (algebraMap R A)).algFiltration k)

private theorem reduction_surjective (k : ℕ) :
    Function.Surjective (extendedIdealCompletionProjection (A := A) I k) := by
  intro y
  obtain ⟨x, hx⟩ := eval_surjective I A (k + 1)
    ((extendedIdealQuotientEquiv I (k + 1)).symm y)
  refine ⟨extendedIdealCompletionEquiv I x, ?_⟩
  rw [extendedIdealCompletionProjection_apply, extendedIdealCompletionEquiv_projection,
    hx, LinearEquiv.apply_symm_apply]

/-- Reduction of the completed algebra by an extended ideal power is the same as reduction of
the original algebra by that power. -/
def extendedIdealCompletionQuotientEquiv (hI : I.FG) (k : ℕ) :
    ((I.map (algebraMap R A)).algFiltration.completion ⧸
      (I.map (algebraMap R (I.map (algebraMap R A)).algFiltration.completion)) ^ (k + 1)) ≃ₐ[R]
        A ⧸ (I.map (algebraMap R A)) ^ (k + 1) :=
  (Ideal.quotientEquivAlgOfEq R (reduction_ker (A := A) I hI k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (reduction_surjective (A := A) I k))

/-- Reduction of a completed element is its corresponding finite projection. -/
@[simp]
theorem extendedIdealCompletionQuotientEquiv_mk (hI : I.FG) (k : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    extendedIdealCompletionQuotientEquiv (A := A) I hI k (Ideal.Quotient.mk _ x) =
      Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
        ((I.map (algebraMap R A)).algFiltration.projection k x) := by
  rw [extendedIdealCompletionQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk,
    extendedIdealCompletionProjection_apply]

end AdicCompletion
