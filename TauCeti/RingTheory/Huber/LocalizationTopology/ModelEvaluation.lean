/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete

/-!
# Evaluating `A⟨X₁, …, Xₖ⟩` into models of `A⟨T/s⟩`

Given a complete Hausdorff topological ring `A`, a pair of definition `P`, a finite set of
numerators `T` generating an open ideal, a denominator `s`, and an `A`-algebra equivalence
`e : ratLoc P T s _ ≃ₐ[A] B` onto a model `B` of `A⟨T/s⟩`, this file constructs the evaluation map
`TauCeti.Huber.modelEvalHom` from the uncompleted restricted power series subring
`A⟨X₁, …, Xₖ⟩` (for `k` numerators drawn from `T`) into `B`, together with its continuity,
application formula, and evaluation rules on constants and coordinate variables.

## Main definitions

* `TauCeti.Huber.modelEvalHom`: evaluation `A⟨X₁, …, Xₖ⟩ →+* B` into a model of `A⟨T/s⟩`.

## Main results

* `TauCeti.Huber.continuous_modelEvalHom`: continuity of `modelEvalHom` when `e` is continuous.
* `TauCeti.Huber.modelEvalHom_apply`: explicit formula for `modelEvalHom` in terms of
  `PairOfDefinition.rationalEvalHom`.
* `TauCeti.Huber.modelEvalHom_weightedC`, `TauCeti.Huber.modelEvalHom_X_eq_algebraMap_of_mul`,
  and `TauCeti.Huber.modelEvalHom_X_mul_inv`: values of `modelEvalHom` on constants and variables.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section ModelEval

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A]
  (P : PairOfDefinition A) {T : Finset A} {s : A}
  (hT : IsOpen (Ideal.span (T : Set A) : Set A))
  {B : Type*} [CommRing B] [Algebra A B]
  (e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- Evaluation `A⟨X₁, …, Xₖ⟩ →+* B` from the uncompleted restricted power series ring into a model
`B` of `A⟨T/s⟩`. -/
noncomputable def modelEvalHom :
    letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B :=
  letI := P.toNonarchimedeanRing
  e.toRingHom.comp ((P.rationalEvalHom T s (Localization.Away s)
    (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht).comp
      (restrictedMvPowerSeriesCompletionEquiv k A).symm.toRingHom)

/-- `modelEvalHom` is continuous whenever the model isomorphism `e` is continuous. -/
theorem continuous_modelEvalHom [TopologicalSpace B] (he : Continuous e) :
    letI := P.toNonarchimedeanRing; Continuous (modelEvalHom P hT e t ht) :=
  letI := P.toNonarchimedeanRing
  he.comp ((P.continuous_rationalEvalHom T s _ _ t ht).comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm.continuous)

/-- Explicit formula for `modelEvalHom` in terms of `PairOfDefinition.rationalEvalHom`. -/
theorem modelEvalHom_apply (x : letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht x = e (P.rationalEvalHom T s (Localization.Away s)
      (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht
      ((restrictedMvPowerSeriesCompletionEquiv k A).symm x)) :=
  let _ := P.toNonarchimedeanRing
  rfl

/-- `modelEvalHom` sends a constant series to its image under `algebraMap A B`. -/
@[simp]
theorem modelEvalHom_weightedC (a : A) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedC _ isWeightFamily_one_weight a) = algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedC, ← algebraMap_ratLoc, e.commutes]

/-- When `t i = s * a`, `modelEvalHom` sends the variable `Xᵢ` to `algebraMap A B a`. -/
theorem modelEvalHom_X_eq_algebraMap_of_mul (i : Fin k) {a : A} (hti : t i = s * a) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) = algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedX, hti, divBy_mul_cancel_left a s, ← P.toCompletionLoc_apply,
    ← algebraMap_ratLoc, e.commutes]

/-- When `t i = 1`, `modelEvalHom` sends the variable `Xᵢ` to an inverse of `algebraMap A B s`. -/
theorem modelEvalHom_X_mul_inv (i : Fin k) (hti : t i = 1) :
    letI := P.toNonarchimedeanRing
    algebraMap A B s * modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) = 1 := by
  let _ := P.toNonarchimedeanRing
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := P.locUniformSpace _ s _ hden
  have _ := P.isUniformAddGroup_locUniformSpace _ s _ hden
  have _ := P.isTopologicalRing_locUniformSpace _ s _ hden
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedX, ← e.commutes s, ← map_mul, algebraMap_ratLoc,
    P.toCompletionLoc_apply, ← Completion.coe_mul, hti, divBy_one,
    IsLocalization.Away.mul_invSelf]
  exact map_one e

end ModelEval

end TauCeti.Huber

end
