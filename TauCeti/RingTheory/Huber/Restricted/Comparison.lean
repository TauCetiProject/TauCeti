/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Adic

/-!
# Coefficient maps, reductions, and evaluation under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers.
This file proves that their coefficient maps, open-ideal polynomial reductions, adic polynomial
quotient equivalences, and topological evaluations agree, both before and after completion. In
particular, evaluation on the completed Huber carrier into a normed target satisfies the same bound
as the coefficient homomorphism, measured using the Gauss norm on the compared carrier, while
evaluation into a general complete Hausdorff nonarchimedean or linearly topologised target agrees
with `restrictedLift` and `restrictedLiftOfIsLinearTopology`.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `weightedEvalHom_eq_restrictedEval₂OfBound` and
  `weightedEvalHomCompletion_eq_restrictedEval₂OfBound`: topological evaluation is normed
  evaluation at points of norm at most one, with bound `norm_weightedEvalHomCompletion_le`.
* `quotientRestrictedPowEquivMvPolynomialQuotient_eq_gauss_trans` and
  `quotientRestrictedCompletionPowEquivMvPolynomialQuotient_eq_gauss_trans`: the Huber and
  Gauss-normed polynomial quotient algebra isomorphisms modulo `Iᵐ` agree before and after
  completion.
* `weightedEvalHom_eq_restrictedLift`, `weightedEvalHomCompletion_eq_restrictedLift`, and
  `weightedEvalHomCompletion_eq_restrictedLiftOfIsLinearTopology`: Huber evaluation into general
  complete Hausdorff nonarchimedean or linearly topologised targets agrees with `restrictedLift`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.3.
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

section Reduction

/-- The polynomial quotient isomorphism on Huber restricted series agrees with transporting
`quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` along
`restrictedMvPowerSeriesGaussAlgEquiv`. -/
theorem quotientRestrictedPowEquivMvPolynomialQuotient_eq_gauss_trans {I : Ideal R}
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m) :
    quotientRestrictedPowEquivMvPolynomialQuotient (k := k) hI hfg hm =
      (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
        rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map,
          ← algebraMap_weightedRestrictedSubring]
        exact congrArg (Ideal.map · (I ^ m))
          (restrictedMvPowerSeriesGaussAlgEquiv (n := k)
            (R := R)).toAlgHom.comp_algebraMap.symm)).trans
        (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm) := by
  ext x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Over a complete ultrametric normed ring `R`, the completed polynomial quotient isomorphism
modulo `(I · R⟨X⟩)ᵐ` agrees with transporting
`quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` along
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`. -/
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_eq_gauss_trans [CompleteSpace R]
    {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m) :
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg hm =
      (Ideal.quotientEquivAlg _ _
        (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)) (by
          rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map]
          exact congrArg (Ideal.map · (I ^ m))
            (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k)
              (R := R)).toAlgHom.comp_algebraMap.symm)).trans
        (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm) := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

end Reduction

section TopologicalEvaluation

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
  {ψ : R →+* T} {b : Fin k → T}

/-- Huber topological evaluation into a complete Hausdorff nonarchimedean ring agrees with
`restrictedLift` across `restrictedMvPowerSeriesGaussEquiv`. -/
theorem weightedEvalHom_eq_restrictedLift [NonarchimedeanRing T] [CompleteSpace T] [T3Space T]
    (hψ : Continuous ψ) (hb : ∀ i, IsPowerBounded (b i))
    (hwb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hwb f =
      restrictedLift hψ hb (restrictedMvPowerSeriesGaussEquiv f) := by
  have h := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hwb)
    (g := (restrictedLift hψ hb).comp
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom)
    (continuous_weightedEvalHom _ _ _)
    ((continuous_restrictedLift hψ hb).comp continuous_restrictedMvPowerSeriesGaussEquiv)
    (fun r ↦ by simp)
    (fun i ↦ by simp)
  exact congr($h f)

/-- Over a complete base `R`, completed Huber evaluation into a complete Hausdorff nonarchimedean
ring agrees with `restrictedLift` across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [CompleteSpace R] [NonarchimedeanRing T]
    [CompleteSpace T] [T3Space T] (hψ : Continuous ψ) (hb : ∀ i, IsPowerBounded (b i))
    (hwb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt hwb x =
      restrictedLift hψ hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((continuous_restrictedLift hψ hb).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro f
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedLift hψ hb hwb]

/-- Over a complete base `R`, completed Huber evaluation into a complete Hausdorff linearly
topologised ring at arbitrary variable images agrees with `restrictedLiftOfIsLinearTopology` across
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem weightedEvalHomCompletion_eq_restrictedLiftOfIsLinearTopology [CompleteSpace R]
    [IsLinearTopology T T] [CompleteSpace T] [T2Space T] (hψ : Continuous ψ)
    (x : restrictedMvPowerSeriesCompletion k R) :
    (letI := IsLinearTopology.isTopologicalRing (R := T)
     letI := IsLinearTopology.nonarchimedeanRing T
     weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt
       (isWeightBounded_of_isLinearTopology ψ _ b) x) =
      restrictedLiftOfIsLinearTopology hψ b (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  have h := completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt
      (isWeightBounded_of_isLinearTopology ψ _ b))
    (g := (restrictedLiftOfIsLinearTopology hψ b).comp
      (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom)
    (continuous_weightedEvalHomCompletion _ _ _)
    ((continuous_restrictedLiftOfIsLinearTopology hψ b).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)
    (fun r ↦ by simp)
    (fun i ↦ by simp)
  exact congr($h x)

end TopologicalEvaluation

end TauCeti.Huber
