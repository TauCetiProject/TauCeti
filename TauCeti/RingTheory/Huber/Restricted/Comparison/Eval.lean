/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval

/-!
# Norm-bounded evaluation under the unit-radius Gauss comparison

This file compares Huber's topological evaluation homomorphisms `TauCeti.Huber.weightedEvalHom` and
`TauCeti.Huber.weightedEvalHomCompletion` (at unit weights) with bounded normed evaluation
`RingHom.restrictedEval₂OfBound` across the unit-radius Gauss comparisons
`TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv` and
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`.

From this identification, we transfer the coefficient-map norm bound and the ultrametric
argument-perturbation bound to `weightedEvalHom` and `weightedEvalHomCompletion` without pulling in
adic ideal reduction or noetherianity infrastructure.

## Main results

* `TauCeti.Huber.weightedEvalHom_eq_restrictedEval₂OfBound` and
  `TauCeti.Huber.weightedEvalHomCompletion_eq_restrictedEval₂OfBound`: Huber evaluation and bounded
  normed evaluation agree under the uncompleted and completed Gauss comparisons.
* `TauCeti.Huber.norm_weightedEvalHom_le` and
  `TauCeti.Huber.norm_weightedEvalHomCompletion_le`: Huber evaluation obeys the coefficient-map
  norm bound, measured in the Gauss norm.
* `TauCeti.Huber.norm_weightedEvalHom_sub_le`: ultrametric perturbation bound for `weightedEvalHom`
  in its evaluation point.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries Topology

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}

section Evaluation

variable [CompleteSpace S] {a : Fin k → S}
  (hφc : ContinuousAt φ 0) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
  (ha : ∀ i, ‖a i‖ ≤ 1)
  (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) a)

/-- Huber evaluation and bounded normed evaluation agree under the Gauss comparison. The
power-boundedness witness may be any witness, not just the one supplied by the norm bounds. -/
theorem weightedEvalHom_eq_restrictedEval₂OfBound
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [coe_weightedEvalHom, RingHom.restrictedEval₂OfBound_apply,
    coe_restrictedMvPowerSeriesGaussEquiv]

include hφ ha in
/-- Huber evaluation obeys the coefficient-map bound, measured in the Gauss norm. -/
theorem norm_weightedEvalHom_le
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    ‖weightedEvalHom isWeightFamily_one_weight hφc hb f‖ ≤
      C * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [weightedEvalHom_eq_restrictedEval₂OfBound hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

variable [CompleteSpace R]

/-- Evaluation on the completed Huber algebra is normed evaluation through the completed Gauss
comparison. This identifies the extensions on every element, not just on polynomials. -/
theorem weightedEvalHomCompletion_eq_restrictedEval₂OfBound
    (f : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((φ.continuous_restrictedEval₂OfBound a hφ ha).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro g
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedEval₂OfBound hφc hφ ha hb]

include hφ ha in
/-- Completed Huber evaluation has the coefficient homomorphism's bound in the Gauss norm
transported by the completed comparison. -/
theorem norm_weightedEvalHomCompletion_le (f : restrictedMvPowerSeriesCompletion k R) :
    ‖weightedEvalHomCompletion isWeightFamily_one_weight hφc hb f‖ ≤
      C * ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ := by
  rw [weightedEvalHomCompletion_eq_restrictedEval₂OfBound hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

end Evaluation

section EvaluationPerturbation

variable [CompleteSpace S]

/-- **Ultrametric perturbation bound for Huber evaluation.** If `a` and `b` satisfy
`‖a i‖ ≤ 1`, `‖b i‖ ≤ 1`, and `‖a i - b i‖ ≤ δ` for every `i`, then
`‖f(a) - f(b)‖ ≤ δ * C * ‖f‖`. -/
theorem norm_weightedEvalHom_sub_le
    (hφc : ContinuousAt φ 0) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {a b : Fin k → S} (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    (ha_bd : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) a)
    (hb_bd : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) b)
    {δ : ℝ} (hδ : 0 ≤ δ) (hab : ∀ i, ‖a i - b i‖ ≤ δ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    ‖weightedEvalHom isWeightFamily_one_weight hφc ha_bd f -
      weightedEvalHom isWeightFamily_one_weight hφc hb_bd f‖ ≤
      δ * C * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [weightedEvalHom_eq_restrictedEval₂OfBound hφc hφ ha ha_bd f,
    weightedEvalHom_eq_restrictedEval₂OfBound hφc hφ hb hb_bd f]
  have heq (x : Fin k → S) (hx : ∀ i, ‖x i‖ ≤ 1) :
      φ.restrictedEval₂OfBound x hφ hx (restrictedMvPowerSeriesGaussEquiv f) =
        MvPowerSeries.restrictedEval₂ (RingHom.id S) x (fun _ ↦ le_rfl) hx
          (TauCeti.MvPowerSeries.restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f)) := by
    simp only [RingHom.restrictedEval₂OfBound_apply, MvPowerSeries.restrictedEval₂_apply,
      weightedEval_def, weightedEvalTerm_def, TauCeti.MvPowerSeries.coe_restrictedMap,
      MvPowerSeries.coeff_map, RingHom.id_apply]
  rw [heq a ha, heq b hb]
  have hsub := MvPowerSeries.norm_restrictedEval₂_sub_le (RingHom.id S) (fun _ ↦ le_rfl) ha hb hδ
    (fun i ↦ by simpa using hab i)
    (TauCeti.MvPowerSeries.restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f))
  have hmap : ‖TauCeti.MvPowerSeries.restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f)‖ ≤
      C * ‖restrictedMvPowerSeriesGaussEquiv f‖ :=
    TauCeti.MvPowerSeries.norm_restrictedMap_le φ hφ _
  calc ‖MvPowerSeries.restrictedEval₂ (RingHom.id S) a (fun _ ↦ le_rfl) ha
          (TauCeti.MvPowerSeries.restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f)) -
        MvPowerSeries.restrictedEval₂ (RingHom.id S) b (fun _ ↦ le_rfl) hb
          (TauCeti.MvPowerSeries.restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f))‖
      ≤ δ * ‖TauCeti.MvPowerSeries.restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f)‖ :=
        hsub
    _ ≤ δ * (C * ‖restrictedMvPowerSeriesGaussEquiv f‖) := mul_le_mul_of_nonneg_left hmap hδ
    _ = δ * C * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by ring

end EvaluationPerturbation

end TauCeti.Huber
