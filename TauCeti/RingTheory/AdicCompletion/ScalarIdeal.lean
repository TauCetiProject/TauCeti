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

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (I : Ideal R)

/-- The module quotient by `I ^ n • A` is the quotient by the `n`-th extended ideal power. -/
def extendedIdealQuotientEquiv (n : ℕ) :
    (A ⧸ (I ^ n • (⊤ : Submodule R A))) ≃ₗ[R]
      A ⧸ (I.map (algebraMap R A)) ^ n :=
  Submodule.quotEquivOfEqRestrictScalars _ _
    (I.pow_smul_top_eq_restrictScalars_map_pow n)

@[simp]
theorem extendedIdealQuotientEquiv_mk (n : ℕ) (a : A) :
    extendedIdealQuotientEquiv (A := A) I n (Submodule.Quotient.mk a) =
      Ideal.Quotient.mk _ a := by
  simp [extendedIdealQuotientEquiv]

@[simp]
theorem extendedIdealQuotientEquiv_symm_mk (n : ℕ) (a : A) :
    (extendedIdealQuotientEquiv (A := A) I n).symm (Ideal.Quotient.mk _ a) =
      Submodule.Quotient.mk a := by
  rw [LinearEquiv.symm_apply_eq, extendedIdealQuotientEquiv_mk]

private def filtrationQuotientEquiv (n : ℕ) :
    (A ⧸ (I ^ n • (⊤ : Submodule R A))) ≃ₗ[R]
      A ⧸ (I.map (algebraMap R A)).algFiltration.ideal n :=
  (extendedIdealQuotientEquiv I n).trans
    (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ n)).symm.toLinearEquiv

private theorem filtrationQuotientEquiv_mk (n : ℕ) (a : A) :
    filtrationQuotientEquiv I n (Submodule.Quotient.mk a) =
      Ideal.Quotient.mk _ a := by
  simp [filtrationQuotientEquiv, Ideal.quotientEquivAlgOfEq_symm]

private theorem filtrationQuotientEquiv_symm_mk (n : ℕ) (a : A) :
    (filtrationQuotientEquiv I n).symm (Ideal.Quotient.mk _ a) =
      Submodule.Quotient.mk a := by
  rw [LinearEquiv.symm_apply_eq, filtrationQuotientEquiv_mk]

private theorem factor_filtrationQuotientEquiv {m n : ℕ} (h : m ≤ n)
    (x : A ⧸ (I ^ n • (⊤ : Submodule R A))) :
    Ideal.Quotient.factor ((I.map (algebraMap R A)).algFiltration.antitone h)
        (filtrationQuotientEquiv I n x) =
      filtrationQuotientEquiv I m (transitionMap I A h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ a => simp [filtrationQuotientEquiv_mk]

private theorem transitionMap_filtrationQuotientEquiv_symm {m n : ℕ} (h : m ≤ n)
    (x : A ⧸ (I.map (algebraMap R A)).algFiltration.ideal n) :
    transitionMap I A h ((filtrationQuotientEquiv I n).symm x) =
      (filtrationQuotientEquiv I m).symm
        (Ideal.Quotient.factor ((I.map (algebraMap R A)).algFiltration.antitone h) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [filtrationQuotientEquiv_symm_mk]

private theorem projection_smul (n : ℕ) (r : R)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    (I.map (algebraMap R A)).algFiltration.projection n (r • x) =
      r • (I.map (algebraMap R A)).algFiltration.projection n x := by
  simpa only [TauCeti.AlgFiltration.projectionₐ_apply] using
    map_smul ((I.map (algebraMap R A)).algFiltration.projectionₐ (R := R) n) r x

private def toExtendedIdealCompletion :
    AdicCompletion I A →ₗ[R] (I.map (algebraMap R A)).algFiltration.completion where
  toFun x := ⟨fun k => filtrationQuotientEquiv I (k.unop + 1) (eval I A _ x), by
    apply (I.map (algebraMap R A)).algFiltration.mem_completion_iff _ |>.mpr
    intro k l h
    rw [factor_filtrationQuotientEquiv I (Nat.add_le_add_right h 1)]
    exact congrArg (filtrationQuotientEquiv I (k + 1))
      (transitionMap_comp_eval_apply I A (Nat.add_le_add_right h 1) x)⟩
  map_add' x y := by
    apply (I.map (algebraMap R A)).algFiltration.completion_ext
    intro k
    simp only [TauCeti.AlgFiltration.projection_apply, map_add]
  map_smul' r x := by
    apply (I.map (algebraMap R A)).algFiltration.completion_ext
    intro k
    rw [projection_smul]
    simp only [TauCeti.AlgFiltration.projection_apply, map_smul, RingHom.id_apply]

private def ofExtendedIdealCompletion :
    (I.map (algebraMap R A)).algFiltration.completion →ₗ[R] AdicCompletion I A where
  toFun x := ⟨fun n => transitionMap I A (Nat.le_succ n)
    ((filtrationQuotientEquiv I (n + 1)).symm
      ((I.map (algebraMap R A)).algFiltration.projection n x)), by
    intro m n h
    dsimp only
    rw [← (I.map (algebraMap R A)).algFiltration.factor_projection h x]
    rw [← transitionMap_filtrationQuotientEquiv_symm I (Nat.add_le_add_right h 1)]
    simp only [transitionMap, Submodule.factor_comp_apply]⟩
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    -- The coordinate of this compatible-family subtype is the displayed quotient class.
    change transitionMap I A (Nat.le_succ n)
      ((filtrationQuotientEquiv I (n + 1)).symm
        ((I.map (algebraMap R A)).algFiltration.projection n (x + y))) = _
    simp only [map_add]
    rfl
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    -- The coordinate of this compatible-family subtype is the displayed quotient class.
    change transitionMap I A (Nat.le_succ n)
      ((filtrationQuotientEquiv I (n + 1)).symm
        ((I.map (algebraMap R A)).algFiltration.projection n (r • x))) = _
    simp only [projection_smul, map_smul, RingHom.id_apply]
    rfl

private theorem projection_toExtendedIdealCompletion (k : ℕ) (x : AdicCompletion I A) :
    (I.map (algebraMap R A)).algFiltration.projection k (toExtendedIdealCompletion I x) =
      filtrationQuotientEquiv I (k + 1) (eval I A (k + 1) x) := by
  rw [TauCeti.AlgFiltration.projection_apply]
  rfl

private theorem eval_ofExtendedIdealCompletion (n : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    eval I A n (ofExtendedIdealCompletion I x) =
      transitionMap I A (Nat.le_succ n) ((filtrationQuotientEquiv I (n + 1)).symm
        ((I.map (algebraMap R A)).algFiltration.projection n x)) := rfl

/-- The completion of the extended ideal filtration agrees, as an `R`-module, with the
module-adic completion. No commutativity of `A` is needed. -/
def extendedIdealCompletionEquiv :
    AdicCompletion I A ≃ₗ[R] (I.map (algebraMap R A)).algFiltration.completion where
  __ := toExtendedIdealCompletion I
  invFun := ofExtendedIdealCompletion I
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    -- Extract the coordinate on the module-adic side of the two compatible families.
    change eval I A n (ofExtendedIdealCompletion I (toExtendedIdealCompletion I x)) = _
    rw [eval_ofExtendedIdealCompletion, projection_toExtendedIdealCompletion,
      LinearEquiv.symm_apply_apply]
    exact transitionMap_comp_eval_apply I A (Nat.le_succ n) x
  right_inv x := by
    apply (I.map (algebraMap R A)).algFiltration.completion_ext
    intro k
    -- The underlying linear map of the equivalence is the constructed family map.
    change (I.map (algebraMap R A)).algFiltration.projection k
      (toExtendedIdealCompletion I (ofExtendedIdealCompletion I x)) = _
    rw [projection_toExtendedIdealCompletion, eval_ofExtendedIdealCompletion,
      transitionMap_filtrationQuotientEquiv_symm, LinearEquiv.apply_symm_apply]
    exact (I.map (algebraMap R A)).algFiltration.factor_projection (Nat.le_succ k) x

/-- After the canonical identification of quotient ideals, the completion comparison preserves
all positive-order projections. -/
@[simp]
theorem extendedIdealCompletionEquiv_projection (k : ℕ) (x : AdicCompletion I A) :
    Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
      ((I.map (algebraMap R A)).algFiltration.projection k
        (extendedIdealCompletionEquiv I x)) =
      extendedIdealQuotientEquiv I (k + 1) (eval I A (k + 1) x) := by
  -- Read the comparison through its underlying linear map.
  change Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))
    ((I.map (algebraMap R A)).algFiltration.projection k
      (toExtendedIdealCompletion I x)) = _
  rw [projection_toExtendedIdealCompletion]
  simp only [filtrationQuotientEquiv, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The comparison preserves the canonical image of the uncompleted algebra. -/
@[simp]
theorem extendedIdealCompletionEquiv_of (a : A) :
    extendedIdealCompletionEquiv I (of I A a) =
      (I.map (algebraMap R A)).algFiltration.toCompletion a := by
  apply (I.map (algebraMap R A)).algFiltration.completion_ext
  intro k
  apply (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).injective
  rw [extendedIdealCompletionEquiv_projection, eval_of, Submodule.mkQ_apply,
    extendedIdealQuotientEquiv_mk,
    TauCeti.AlgFiltration.projection_toCompletion, Ideal.quotientEquivAlgOfEq_mk]

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
  ext x
  simp only [RingHom.mem_ker, extendedIdealCompletionProjection_apply,
    map_eq_zero_iff _
      (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).injective]

private theorem reduction_surjective (k : ℕ) :
    Function.Surjective (extendedIdealCompletionProjection (A := A) I k) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(I.map (algebraMap R A)).algFiltration.toCompletion a, ?_⟩
  rw [extendedIdealCompletionProjection_apply, TauCeti.AlgFiltration.projection_toCompletion,
    Ideal.quotientEquivAlgOfEq_mk]

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
