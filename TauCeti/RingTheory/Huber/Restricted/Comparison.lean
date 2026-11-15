/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

/-!
# Coefficient maps and evaluation under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers.
This file proves that their coefficient maps and evaluations agree, both before and after
completion (for open-ideal polynomial reductions under the Gauss comparison, see
`Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesGaussEquiv` and
`Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv` in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Adic`).

In particular, evaluation into a complete ultrametric normed target at points of norm at most one
satisfies the same bound as the coefficient homomorphism, measured using the Gauss norm on the
compared carrier, while evaluation into a general complete Hausdorff nonarchimedean or linearly
topologised target agrees with `restrictedLift`, `restrictedLiftOfIsLinearTopology`, and
`restrictedLiftAlgHomOfIsLinearTopology`. Completeness of the source coefficient ring `R`
(`[CompleteSpace R]`) is required only for comparisons involving the completed source
`restrictedMvPowerSeriesCompletion k R`.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `weightedEvalHom_eq_restrictedEval₂OfBound` and
  `weightedEvalHomCompletion_eq_restrictedEval₂OfBound`: topological evaluation is normed
  evaluation at points of norm at most one, with bound `norm_weightedEvalHomCompletion_le`.
* `weightedEvalHom_eq_restrictedLift` and `weightedEvalHomCompletion_eq_restrictedLift`: Huber
  evaluation into general complete Hausdorff nonarchimedean targets agrees with `restrictedLift`.
* `weightedEvalHom_eq_restrictedLiftOfIsLinearTopology`,
  `weightedEvalHomCompletionOfIsLinearTopology_eq_restrictedLiftOfIsLinearTopology`, and
  `weightedEvalAlgHomCompletionOfIsLinearTopology_eq_restrictedLiftAlgHomOfIsLinearTopology_comp`:
  Huber evaluation into complete Hausdorff linearly topologised rings and `R`-algebras agrees with
  `restrictedLiftOfIsLinearTopology` and `restrictedLiftAlgHomOfIsLinearTopology`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}

section Coefficients

variable (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

/-- The Gauss comparison commutes with bounded coefficient maps. -/
theorem restrictedMvPowerSeriesGaussEquiv_weightedMap
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesGaussEquiv
        (weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f) := by
  apply Subtype.ext
  simp only [coe_restrictedMvPowerSeriesGaussEquiv, coe_weightedMap, coe_restrictedMap]

variable [CompleteSpace R] [CompleteSpace S]

/-- The completed Gauss comparison commutes with the continuous coefficient map on completions.
Thus completing the topological coefficient map does not change the normed coefficient map. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion
    (f : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f) =
      restrictedMap φ hφ (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_restrictedMvPowerSeriesCompletionGaussEquiv.comp
      (continuous_weightedMapCompletion _ _ _ _))
    ((continuous_restrictedMap φ hφ).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro g
  simp only [weightedMapCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ]

include hφ in
/-- A bounded coefficient map on Huber completions has the same bound in the compared Gauss
norms. No norm on the topological completion is chosen independently of the comparison. -/
theorem norm_restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_le
    (f : restrictedMvPowerSeriesCompletion k R) :
    ‖restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f)‖ ≤
      C * ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ]
  exact norm_restrictedMap_le φ hφ _

end Coefficients

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

section TopologicalEvaluation

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
  {ψ : R →+* T} {b : Fin k → T}

/-- Huber topological evaluation into a complete Hausdorff nonarchimedean ring agrees with
`restrictedLift` across `restrictedMvPowerSeriesGaussEquiv`. -/
theorem weightedEvalHom_eq_restrictedLift [NonarchimedeanRing T] [CompleteSpace T] [T3Space T]
    (hψ : Continuous ψ) (hb : ∀ i, IsPowerBounded (b i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt
        ((isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mpr hb) f =
      restrictedLift hψ hb (restrictedMvPowerSeriesGaussEquiv f) := by
  simp [restrictedLift_apply]

/-- Uncompleted Huber evaluation into a complete Hausdorff linearly topologised ring at arbitrary
variable images agrees with `restrictedLiftOfIsLinearTopology` across
`restrictedMvPowerSeriesGaussEquiv`, without assuming `R` complete. -/
theorem weightedEvalHom_eq_restrictedLiftOfIsLinearTopology [IsLinearTopology T T]
    [CompleteSpace T] [T2Space T] (hψ : Continuous ψ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (letI := IsLinearTopology.isTopologicalRing (R := T)
     letI := IsLinearTopology.nonarchimedeanRing T
     weightedEvalHom isWeightFamily_one_weight hψ.continuousAt
       (isWeightBounded_of_isLinearTopology ψ _ b) f) =
      restrictedLiftOfIsLinearTopology hψ b (restrictedMvPowerSeriesGaussEquiv f) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  rw [restrictedLiftOfIsLinearTopology_eq_restrictedLift]
  exact weightedEvalHom_eq_restrictedLift hψ (fun _ ↦ isPowerBounded_of_isLinearTopology _) f

/-- Over a complete base `R`, completed Huber evaluation into a complete Hausdorff nonarchimedean
ring agrees with `restrictedLift` across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [CompleteSpace R] [NonarchimedeanRing T]
    [CompleteSpace T] [T3Space T] (hψ : Continuous ψ) (hb : ∀ i, IsPowerBounded (b i))
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt
        ((isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mpr hb) x =
      restrictedLift hψ hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((continuous_restrictedLift hψ hb).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro f
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedLift hψ hb]

/-- Over a complete base `R`, completed Huber evaluation into a complete Hausdorff linearly
topologised ring at arbitrary variable images agrees with `restrictedLiftOfIsLinearTopology` across
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem weightedEvalHomCompletionOfIsLinearTopology_eq_restrictedLiftOfIsLinearTopology
    [CompleteSpace R] [IsLinearTopology T T] [CompleteSpace T] [T2Space T] (hψ : Continuous ψ)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletionOfIsLinearTopology hψ b x =
      restrictedLiftOfIsLinearTopology hψ b (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  rw [weightedEvalHomCompletionOfIsLinearTopology_eq_weightedEvalHomCompletion,
    restrictedLiftOfIsLinearTopology_eq_restrictedLift]
  exact weightedEvalHomCompletion_eq_restrictedLift hψ
    (fun _ ↦ isPowerBounded_of_isLinearTopology _) x

/-- Over a complete base `R`, `weightedEvalAlgHomCompletionOfIsLinearTopology` into a complete
Hausdorff linearly topologised `R`-algebra agrees as an `R`-algebra map with
`restrictedLiftAlgHomOfIsLinearTopology` composed with
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`. -/
theorem
  weightedEvalAlgHomCompletionOfIsLinearTopology_eq_restrictedLiftAlgHomOfIsLinearTopology_comp
    [CompleteSpace R] [IsLinearTopology T T] [CompleteSpace T] [T2Space T] [Algebra R T]
    (hψ : Continuous (algebraMap R T)) :
    weightedEvalAlgHomCompletionOfIsLinearTopology hψ b =
      (restrictedLiftAlgHomOfIsLinearTopology hψ b).comp
        (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).toAlgHom := by
  ext x
  simp [weightedEvalHomCompletionOfIsLinearTopology_eq_restrictedLiftOfIsLinearTopology]

end TopologicalEvaluation

end TauCeti.Huber
