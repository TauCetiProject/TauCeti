/-
Copyright (c) 2026 Mei contributors and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Algebra
public import TauCeti.RingTheory.Ideal.Extended
public import Mathlib.RingTheory.AdicCompletion.Algebra

import TauCeti.RingTheory.AdicCompletion.AlgHom
import Mathlib.RingTheory.AdicCompletion.Completeness
import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Ideal-adic and filtered completions

For an ideal `I` of a commutative ring `A`, Mathlib's adic completion `AdicCompletion I A` and the
completion of the ideal-power filtration `I.algFiltration` agree. The filtered completion records
only the quotients by `I ^ (k + 1)`, while the adic completion also records the trivial quotient by
`I ^ 0`; the comparison forgets this redundant coordinate. It commutes with the projections and
with the canonical maps from `A`.

For a possibly noncommutative `R`-algebra `A`, completion of the powers of the ideal extended
from `I : Ideal R` has the same underlying `R`-module as `AdicCompletion I A`. When `I` is
finitely generated, its finite reductions are the corresponding reductions of `A`.
The motivating example is the integral completion of a universal enveloping algebra.

## Main results

* `AdicCompletion.algFiltrationCompletionEquiv` identifies the adic and filtered ring completions.
* `TauCeti.extendedIdealCompletionProjection` and its canonical-image, transition, extensionality,
  kernel, and surjectivity theorems describe the finite-order projections.
* `AdicCompletion.extendedIdealCompletionEquiv` compares the completion with the module-adic
  completion and computes in both directions on canonical images and projections.
* `TauCeti.extendedIdealToCompletionₐ_injective_of_isHausdorff` embeds every separated algebra.
* `TauCeti.extendedIdealCompletionQuotientEquiv` identifies finite reductions when `I` is finitely
  generated, with representative equations for the equivalence and its inverse.

The commutative comparison is adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/RingTheory/AdicCompletion/Filtered.lean` (Apache 2.0).
-/

public section

/-! ## Ideal-adic ring completions -/

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)

-- The order-`k` quotient of the filtered completion, identified with `A ⧸ I ^ (k + 1)`.
local notation "Q" k => Ideal.quotEquivOfEq (Ideal.algFiltration_ideal I (k + 1))

/-- The order-`k` component of the comparison map: evaluation at `I ^ (k + 1)`. -/
private noncomputable def toAlgFiltrationQuotient (k : ℕ) :
    AdicCompletion I A →+* A ⧸ I.algFiltration.ideal (k + 1) :=
  (Q k).symm.toRingHom.comp (evalₐ I (k + 1)).toRingHom

private theorem toAlgFiltrationQuotient_apply (k : ℕ) (x : AdicCompletion I A) :
    toAlgFiltrationQuotient I k x = (Q k).symm (evalₐ I (k + 1) x) := (rfl)

/-- The ring map from the adic completion to the filtered completion of the ideal-power
filtration. -/
private noncomputable def toAlgFiltrationCompletion :
    AdicCompletion I A →+* I.algFiltration.completion :=
  I.algFiltration.lift (toAlgFiltrationQuotient I)
    (by
      intro k l h
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, toAlgFiltrationQuotient_apply, toAlgFiltrationQuotient_apply]
      rw [← factor_evalₐ (Nat.add_le_add_right h 1) x]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I (l + 1) x)
      rw [← ha]
      simp)

private theorem projection_toAlgFiltrationCompletion (k : ℕ) (x : AdicCompletion I A) :
    I.algFiltration.projection k (toAlgFiltrationCompletion I x) =
      (Q k).symm (evalₐ I (k + 1) x) := by
  simp [toAlgFiltrationCompletion, toAlgFiltrationQuotient_apply]

/-- The order-`n` component of the inverse comparison: the order-`n - 1` projection, followed by
the identification with `A ⧸ I ^ n`. -/
private noncomputable def ofAlgFiltrationQuotient (n : ℕ) :
    I.algFiltration.completion →+* A ⧸ I ^ n :=
  (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp
    ((Q n).toRingHom.comp (I.algFiltration.projection n))

private theorem factorPow_comp_ofAlgFiltrationQuotient {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (ofAlgFiltrationQuotient I n) =
      ofAlgFiltrationQuotient I m := by
  refine RingHom.ext fun x => ?_
  simp only [ofAlgFiltrationQuotient, RingHom.comp_apply]
  rw [← I.algFiltration.factor_projection h x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I.algFiltration.projection n x)
  rw [← ha]
  simp

/-- The ring map from the filtered completion of the ideal-power filtration to the adic
completion. -/
private noncomputable def ofAlgFiltrationCompletion :
    I.algFiltration.completion →+* AdicCompletion I A :=
  liftRingHom I (ofAlgFiltrationQuotient I) (factorPow_comp_ofAlgFiltrationQuotient I)

private theorem evalₐ_ofAlgFiltrationCompletion (n : ℕ) (x : I.algFiltration.completion) :
    evalₐ I (n + 1) (ofAlgFiltrationCompletion I x) = (Q n) (I.algFiltration.projection n x) := by
  rw [ofAlgFiltrationCompletion, evalₐ_liftRingHom]
  simp only [ofAlgFiltrationQuotient, RingHom.comp_apply]
  rw [← I.algFiltration.factor_projection (Nat.le_succ n) x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I.algFiltration.projection (n + 1) x)
  rw [← ha]
  simp

/-- The adic completion is the completion of the ideal-power filtration, with its redundant
order-zero quotient omitted. -/
noncomputable def algFiltrationCompletionEquiv :
    AdicCompletion I A ≃+* I.algFiltration.completion where
  toFun := toAlgFiltrationCompletion I
  invFun := ofAlgFiltrationCompletion I
  left_inv x := by
    refine ext_evalₐ fun n => ?_
    rw [← factor_evalₐ (Nat.le_succ n) x,
      ← factor_evalₐ (Nat.le_succ n) (ofAlgFiltrationCompletion I _),
      evalₐ_ofAlgFiltrationCompletion, projection_toAlgFiltrationCompletion,
      RingEquiv.apply_symm_apply]
  right_inv x := by
    refine I.algFiltration.completion_ext fun k => ?_
    rw [projection_toAlgFiltrationCompletion, evalₐ_ofAlgFiltrationCompletion,
      RingEquiv.symm_apply_apply]
  map_mul' := (toAlgFiltrationCompletion I).map_mul
  map_add' := (toAlgFiltrationCompletion I).map_add

/-- The comparison sends the adic projection to `I ^ (k + 1)` to the order-`k` projection. -/
@[simp]
theorem projection_algFiltrationCompletionEquiv (k : ℕ) (x : AdicCompletion I A) :
    I.algFiltration.projection k (algFiltrationCompletionEquiv I x) =
      (Q k).symm (evalₐ I (k + 1) x) :=
  projection_toAlgFiltrationCompletion I k x

/-- The inverse comparison recovers every positive-order adic projection. -/
@[simp]
theorem evalₐ_algFiltrationCompletionEquiv_symm (k : ℕ) (x : I.algFiltration.completion) :
    evalₐ I (k + 1) ((algFiltrationCompletionEquiv I).symm x) =
      (Q k) (I.algFiltration.projection k x) :=
  evalₐ_ofAlgFiltrationCompletion I k x

/-- The comparison preserves the canonical image of the original ring. -/
@[simp]
theorem algFiltrationCompletionEquiv_of (a : A) :
    algFiltrationCompletionEquiv I (of I A a) = I.algFiltration.toCompletion a := by
  refine I.algFiltration.completion_ext fun k => ?_
  simp

end AdicCompletion

/-! ## Completion along an extended scalar ideal -/

noncomputable section

namespace TauCeti

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

/-- The canonical map computes to the ordinary quotient map at each finite order. -/
@[simp]
theorem extendedIdealCompletionProjection_toCompletion (k : ℕ) (a : A) :
    extendedIdealCompletionProjection I k
      ((I.map (algebraMap R A)).algFiltration.toCompletion a) =
      Ideal.Quotient.mk _ a := by
  rw [extendedIdealCompletionProjection_apply, AlgFiltration.projection_toCompletion,
    Ideal.quotientEquivAlgOfEq_mk]

/-- Finite-order projections commute with reduction to a smaller order. -/
@[simp]
theorem factor_extendedIdealCompletionProjection {k l : ℕ} (h : k ≤ l)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
      (extendedIdealCompletionProjection I l x) = extendedIdealCompletionProjection I k x := by
  rw [extendedIdealCompletionProjection_apply, extendedIdealCompletionProjection_apply,
    ← AlgFiltration.factor_projection _ h x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((I.map (algebraMap R A)).algFiltration.projection l x)
  rw [← ha, Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factor_mk, Ideal.quotientEquivAlgOfEq_mk]

/-- All finite-order projections determine an element of the extended-ideal completion. -/
@[ext]
theorem extendedIdealCompletion_ext
    {x y : (I.map (algebraMap R A)).algFiltration.completion}
    (h : ∀ k, extendedIdealCompletionProjection I k x =
      extendedIdealCompletionProjection I k y) : x = y := by
  apply (I.map (algebraMap R A)).algFiltration.completion_ext
  intro k
  apply (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).injective
  simpa only [extendedIdealCompletionProjection_apply] using h k

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
    rw [AlgFiltration.projection_smul]
    simp only [TauCeti.AlgFiltration.projection_apply, map_smul, RingHom.id_apply]

private theorem projection_toExtendedIdealCompletion (k : ℕ) (x : (reduction I A).lim) :
    (I.map (algebraMap R A)).algFiltration.projection k (toExtendedIdealCompletion I x) =
      reductionQuotientEquiv I k ((reduction I A).limπ k x) := by
  simp only [TauCeti.AlgFiltration.projection_apply, toExtendedIdealCompletion,
    LinearMap.coe_mk, AddHom.coe_mk]

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
    (reduction I A).lim ≃ₗ[R] (I.map (algebraMap R A)).algFiltration.completion :=
  LinearEquiv.ofLinearMap (toExtendedIdealCompletion I) (ofExtendedIdealCompletion I)
    (by
      apply LinearMap.ext
      intro x
      apply (I.map (algebraMap R A)).algFiltration.completion_ext
      intro k
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [projection_toExtendedIdealCompletion, limπ_ofExtendedIdealCompletion,
        (reductionQuotientEquiv I k).apply_symm_apply])
    (by
      apply LinearMap.ext
      intro x
      apply (reduction I A).lim_ext
      intro k
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [limπ_ofExtendedIdealCompletion, projection_toExtendedIdealCompletion,
        (reductionQuotientEquiv I k).symm_apply_apply])

private theorem reductionCompletionEquiv_apply (x : (reduction I A).lim) :
    reductionCompletionEquiv I x = toExtendedIdealCompletion I x := by
  simp only [reductionCompletionEquiv, LinearEquiv.coe_ofLinearMap]

end TauCeti

namespace AdicCompletion

open TauCeti TauCeti.ModuleTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (I : Ideal R)

/-- The completion of the extended ideal filtration agrees, as an `R`-module, with the
module-adic completion. No commutativity of `A` is needed. -/
def extendedIdealCompletionEquiv :
    AdicCompletion I A ≃ₗ[R] (I.map (algebraMap R A)).algFiltration.completion :=
  (limReductionEquiv I A).symm.trans (reductionCompletionEquiv I)

/-- After the canonical identification of quotient ideals, the completion comparison preserves
all positive-order projections. -/
@[simp]
theorem projection_extendedIdealCompletionEquiv (k : ℕ) (x : AdicCompletion I A) :
    extendedIdealCompletionProjection I k (extendedIdealCompletionEquiv I x) =
      extendedIdealQuotientEquiv I (k + 1) (eval I A (k + 1) x) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (eval I A (k + 1) x)
  have hval : x.val (k + 1) = Submodule.Quotient.mk a := by
    simpa only [eval_apply] using ha.symm
  rw [extendedIdealCompletionProjection_apply, extendedIdealCompletionEquiv,
    LinearEquiv.trans_apply, reductionCompletionEquiv_apply,
    projection_toExtendedIdealCompletion, limπ_limReductionEquiv_symm_apply I A hval,
    reductionQuotientEquiv_π, Ideal.quotientEquivAlgOfEq_mk, ← ha,
    extendedIdealQuotientEquiv_mk]

/-- The comparison preserves the canonical image of the uncompleted algebra. -/
@[simp]
theorem extendedIdealCompletionEquiv_of (a : A) :
    extendedIdealCompletionEquiv I (of I A a) =
      (I.map (algebraMap R A)).algFiltration.toCompletion a := by
  apply extendedIdealCompletion_ext I
  intro k
  rw [projection_extendedIdealCompletionEquiv, eval_of, Submodule.mkQ_apply,
    extendedIdealQuotientEquiv_mk, extendedIdealCompletionProjection_toCompletion]

/-- The inverse comparison has the prescribed positive-order module projections. -/
@[simp]
theorem eval_extendedIdealCompletionEquiv_symm (k : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    extendedIdealQuotientEquiv I (k + 1)
      (((extendedIdealCompletionEquiv I).symm x).val (k + 1)) =
      extendedIdealCompletionProjection I k x := by
  simpa only [coe_eval, LinearEquiv.apply_symm_apply] using
    (projection_extendedIdealCompletionEquiv I k ((extendedIdealCompletionEquiv I).symm x)).symm

/-- The inverse comparison preserves the canonical image of the uncompleted algebra. -/
@[simp]
theorem extendedIdealCompletionEquiv_symm_toCompletion (a : A) :
    (extendedIdealCompletionEquiv I).symm
      ((I.map (algebraMap R A)).algFiltration.toCompletion a) = of I A a := by
  apply (extendedIdealCompletionEquiv I).injective
  rw [LinearEquiv.apply_symm_apply, extendedIdealCompletionEquiv_of]

end AdicCompletion

namespace TauCeti

open AdicCompletion

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (I : Ideal R)

/-- A separated algebra embeds into its extended-ideal completion. -/
theorem extendedIdealToCompletionₐ_injective_of_isHausdorff [IsHausdorff I A] :
    Function.Injective ((I.map (algebraMap R A)).algFiltration.toCompletionₐ (R := R)) := by
  intro x y h
  apply AdicCompletion.of_injective I A
  apply (extendedIdealCompletionEquiv (A := A) I).injective
  simpa only [extendedIdealCompletionEquiv_of, AlgFiltration.toCompletionₐ_apply] using h

/-- For a finitely generated base ideal, a finite projection kills precisely the corresponding
power of the ideal extended to the completed algebra. -/
theorem ker_projection_extendedIdeal (hI : I.FG) (k : ℕ) :
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
    simp only [e, coe_eval, eval_extendedIdealCompletionEquiv_symm,
      extendedIdealCompletionProjection_apply, hx, _root_.map_zero]
  · rintro ⟨y, hy, rfl⟩
    apply (Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal _ (k + 1))).injective
    have hz : extendedIdealCompletionProjection I k (e y) = 0 := by
      simp only [e, projection_extendedIdealCompletionEquiv, hy, _root_.map_zero]
    simpa only [extendedIdealCompletionProjection_apply, _root_.map_zero] using hz

/-- The finite-order projection kills exactly the extended ideal power in the completion. -/
theorem ker_extendedIdealCompletionProjection (hI : I.FG) (k : ℕ) :
    RingHom.ker (extendedIdealCompletionProjection (A := A) I k) =
      (I.map (algebraMap R (I.map (algebraMap R A)).algFiltration.completion)) ^ (k + 1) := by
  let F := (I.map (algebraMap R A)).algFiltration
  let e := Ideal.quotientEquivAlgOfEq R
    (Ideal.algFiltration_ideal (I.map (algebraMap R A)) (k + 1))
  have hcomp : (extendedIdealCompletionProjection (A := A) I k).toRingHom =
      e.toRingEquiv.toRingHom.comp (F.projection k) := by
    apply RingHom.ext
    intro x
    exact extendedIdealCompletionProjection_apply I k x
  have he : Function.Injective e.toRingEquiv.toRingHom := e.injective
  exact (congrArg RingHom.ker hcomp).trans <|
    (RingHom.ker_comp_of_injective _ he).trans (ker_projection_extendedIdeal I hI k)

/-- Every finite-order class is the projection of a completed element. -/
theorem extendedIdealCompletionProjection_surjective (k : ℕ) :
    Function.Surjective (extendedIdealCompletionProjection (A := A) I k) := by
  intro y
  obtain ⟨x, hx⟩ := eval_surjective I A (k + 1)
    ((extendedIdealQuotientEquiv I (k + 1)).symm y)
  refine ⟨extendedIdealCompletionEquiv I x, ?_⟩
  rw [projection_extendedIdealCompletionEquiv, hx, LinearEquiv.apply_symm_apply]

/-- Reduction of the completed algebra by an extended ideal power is the same as reduction of
the original algebra by that power. -/
def extendedIdealCompletionQuotientEquiv (hI : I.FG) (k : ℕ) :
    ((I.map (algebraMap R A)).algFiltration.completion ⧸
      (I.map (algebraMap R (I.map (algebraMap R A)).algFiltration.completion)) ^ (k + 1)) ≃ₐ[R]
        A ⧸ (I.map (algebraMap R A)) ^ (k + 1) :=
  (Ideal.quotientEquivAlgOfEq R (ker_extendedIdealCompletionProjection (A := A) I hI k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (extendedIdealCompletionProjection_surjective (A := A) I k))

/-- Reduction of a completed element is its corresponding finite projection. -/
@[simp]
theorem extendedIdealCompletionQuotientEquiv_mk (hI : I.FG) (k : ℕ)
    (x : (I.map (algebraMap R A)).algFiltration.completion) :
    extendedIdealCompletionQuotientEquiv (A := A) I hI k (Ideal.Quotient.mk _ x) =
      extendedIdealCompletionProjection I k x := by
  rw [extendedIdealCompletionQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The inverse finite quotient comparison sends an ordinary class to the class of its
canonical image in the completion. -/
@[simp]
theorem extendedIdealCompletionQuotientEquiv_symm_mk (hI : I.FG) (k : ℕ) (a : A) :
    (extendedIdealCompletionQuotientEquiv (A := A) I hI k).symm (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ((I.map (algebraMap R A)).algFiltration.toCompletion a) := by
  apply (extendedIdealCompletionQuotientEquiv (A := A) I hI k).injective
  rw [AlgEquiv.apply_symm_apply, extendedIdealCompletionQuotientEquiv_mk,
    extendedIdealCompletionProjection_toCompletion]

end TauCeti
