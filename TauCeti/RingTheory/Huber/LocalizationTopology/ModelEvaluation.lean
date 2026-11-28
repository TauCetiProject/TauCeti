/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion

/-!
# Evaluating `A⟨X₁, …, Xₖ⟩` into models of `A⟨T/s⟩`

Given a complete Hausdorff topological ring `A`, a pair of definition `P`, a finite set `T`
generating an open ideal, a denominator `s`, and `e : ratLoc P T s _ ≃ₐ[A] B` onto a model `B`
of `A⟨T/s⟩`, this file constructs `TauCeti.Huber.modelEvalHom : A⟨X₁, …, Xₖ⟩ →+* B` together
with its continuity, application formula, and values on constants and variables.

## Main definitions

* `TauCeti.Huber.modelEvalHom`: evaluation `A⟨X₁, …, Xₖ⟩ →+* B` into a model of `A⟨T/s⟩`.

## Main results

* `TauCeti.Huber.continuous_modelEvalHom`, `TauCeti.Huber.modelEvalHom_apply`,
  `TauCeti.Huber.modelEvalHom_weightedC`, `TauCeti.Huber.modelEvalHom_weightedX`,
  `TauCeti.Huber.modelEvalHom_X_eq_algebraMap_of_mul`, and
  `TauCeti.Huber.algebraMap_mul_modelEvalHom_X_of_eq_one`.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section ModelEval

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] (P : PairOfDefinition A) {T : Finset A} {s : A}
  (hT : IsOpen (Ideal.span (T : Set A) : Set A)) {B : Type*} [CommRing B] [Algebra A B]
  (e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- Evaluation `A⟨X₁, …, Xₖ⟩ →+* B` from the uncompleted restricted power series ring into a
model `B` of `A⟨T/s⟩`. -/
noncomputable def modelEvalHom : letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B :=
  letI := P.toNonarchimedeanRing; e.toRingHom.comp ((P.rationalEvalHom T s (Localization.Away s)
    (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht).comp
      (restrictedMvPowerSeriesCompletionEquiv k A).symm.toRingHom)

/-- `modelEvalHom` is continuous whenever the model isomorphism `e` is continuous. -/
theorem continuous_modelEvalHom [TopologicalSpace B] (he : Continuous e) :
    letI := P.toNonarchimedeanRing; Continuous (modelEvalHom P hT e t ht) :=
  letI := P.toNonarchimedeanRing; he.comp ((P.continuous_rationalEvalHom T s _ _ t ht).comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm.continuous)

/-- Explicit formula for `modelEvalHom` in terms of `PairOfDefinition.rationalEvalHom`. -/
theorem modelEvalHom_apply (x : letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht x = e (P.rationalEvalHom T s (Localization.Away s)
      (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht
      ((restrictedMvPowerSeriesCompletionEquiv k A).symm x)) := by
  let _ := P.toNonarchimedeanRing; rfl

/-- `modelEvalHom` sends a constant series to its image under `algebraMap A B`. -/
@[simp] theorem modelEvalHom_weightedC (a : A) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedC _ isWeightFamily_one_weight a) = algebraMap A B a := by
  let _ := P.toNonarchimedeanRing; rw [modelEvalHom_apply,
    restrictedMvPowerSeriesCompletionEquiv_symm_apply, P.rationalEvalHom_coe_weightedC,
    ← algebraMap_ratLoc, e.commutes]

/-- `modelEvalHom` sends the variable `Xᵢ` to the image of `t i / s` under the model's
localization map `Localization.Away s →+* B`. -/
@[simp] theorem modelEvalHom_weightedX (i : Fin k) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) =
      IsLocalization.Away.lift s (show IsUnit (algebraMap A B s) from by
          rw [← e.commutes s]; exact (isUnit_algebraMap_ratLoc P T s _).map e.toRingHom)
        (divBy (t i) s : Localization.Away s) := by
  let _ := P.toNonarchimedeanRing
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedX, algEquiv_coe_eq_lift e _ (divBy (t i) s)]

/-- When `t i = s * a`, `modelEvalHom` sends the variable `Xᵢ` to `algebraMap A B a`. -/
theorem modelEvalHom_X_eq_algebraMap_of_mul (i : Fin k) {a : A} (hti : t i = s * a) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) = algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  rw [modelEvalHom_weightedX, hti, divBy_mul_cancel_left a s, IsLocalization.Away.lift_eq]

/-- When `t i = 1`, `modelEvalHom` sends `Xᵢ` to an inverse of `algebraMap A B s`. -/
theorem algebraMap_mul_modelEvalHom_X_of_eq_one (i : Fin k) (hti : t i = 1) :
    letI := P.toNonarchimedeanRing
    algebraMap A B s * modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) = 1 := by
  let _ := P.toNonarchimedeanRing
  have hu : IsUnit (algebraMap A B s) := by
    rw [← e.commutes s]; exact (isUnit_algebraMap_ratLoc P T s _).map e.toRingHom
  rw [modelEvalHom_weightedX, hti, divBy_one]
  conv_lhs => arg 1; rw [← IsLocalization.Away.lift_eq (S := Localization.Away s) s hu s]
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
end ModelEval

end TauCeti.Huber

end
