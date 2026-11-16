/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

/-!
# Coefficient maps, reductions, and universal properties under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers.
This file proves that their coefficient maps, open-ideal polynomial reductions, adic polynomial
quotients, and evaluations agree before and after completion, and compares the three evaluation
regimes:

1. **Normed evaluation** (`RingHom.restrictedEval₂OfBound`): bounded coefficient map
   `‖φ r‖ ≤ C * ‖r‖` into a complete ultrametric normed ring and `‖a i‖ ≤ 1`, giving the operator
   bound `‖·‖ ≤ C * ‖·‖` (`norm_weightedEvalHomCompletion_le`).
2. **Topological power-bounded evaluation** (`TauCeti.MvPowerSeries.restrictedLift`): continuous
   coefficient map into a complete Hausdorff nonarchimedean ring and `IsPowerBounded (b i)` (where
   `‖b i‖` may exceed `1`); agrees with `weightedEvalHom` and `weightedEvalHomCompletion`.
3. **Linearly topologised evaluation**
   (`TauCeti.MvPowerSeries.restrictedLiftAlgHomOfIsLinearTopology`): into a complete Hausdorff
   linearly topologised `R`-algebra with continuous structure map, open-ideal neighbourhoods make
   every element power-bounded (`isBounded_of_isLinearTopology`), so arbitrary `b : Fin k → T`
   extend uniquely and agree with `weightedEvalAlgHomOfIsLinearTopology` and
   `weightedEvalCompletionAlgHomOfIsLinearTopology`.

## Main definitions and results

* `TauCeti.MvPowerSeries.quotientIsRestrictedPowEquivMvPolynomialQuotient`,
  `TauCeti.MvPowerSeries.quotientIsRestrictedEquivMvPolynomialQuotient`, and
  `TauCeti.MvPowerSeries.liftIsRestrictedReductionPowSucc`: polynomial quotients modulo
  `(I · R⟨X⟩) ^ m` and `I · R⟨X⟩` and inverse-limit lifts on `R⟨X₁, …, Xₖ⟩`.
* `restrictedMvPowerSeriesGaussEquiv_weightedMap`,
  `isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv`, and their completed counterparts.
* `TauCeti.MvPowerSeries.isAdic_map_algebraMap_isRestricted_subring`,
  `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_isAdic`, and
  `TauCeti.MvPowerSeries.existsUnique_isRestrictedReduction_pow_succ_eq`.
* `weightedEvalHom_eq_restrictedEval₂OfBound`, `weightedEvalHom_eq_restrictedLift`, and
  `weightedEvalAlgHomOfIsLinearTopology_eq_restrictedLiftAlgHomOfIsLinearTopology` (and their
  completed counterparts).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
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

section Reduction

/-- **The uncompleted Gauss comparison commutes with open-ideal polynomial reduction.** -/
@[simp]
theorem isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv {J : Ideal R}
    (hJ : IsOpen (J : Set R))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    J.isRestrictedReduction hJ (restrictedMvPowerSeriesGaussEquiv f) =
      J.restrictedReduction hJ f := by
  ext ν; simp

/-- Applying `restrictedReduction` after the inverse Gauss comparison agrees with
`isRestrictedReduction`. -/
@[simp]
theorem restrictedReduction_restrictedMvPowerSeriesGaussEquiv_symm {J : Ideal R}
    (hJ : IsOpen (J : Set R)) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    J.restrictedReduction hJ (restrictedMvPowerSeriesGaussEquiv.symm f) =
      J.isRestrictedReduction hJ f := by
  simpa using (isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv hJ
    (restrictedMvPowerSeriesGaussEquiv.symm f)).symm

section CompleteReduction

variable [CompleteSpace R]

/-- **The completed Gauss comparison commutes with open-ideal polynomial reduction.** -/
@[simp]
theorem isRestrictedReduction_restrictedMvPowerSeriesCompletionGaussEquiv {J : Ideal R}
    (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
    J.isRestrictedReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) =
      J.restrictedCompletionReduction hJ x := by
  let : TopologicalSpace (MvPolynomial (Fin k) (R ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (R ⧸ J)) := ⟨rfl⟩
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((J.continuous_comp_isRestrictedReduction hJ id).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)
    (J.continuous_comp_restrictedCompletionReduction hJ id)) fun f ↦ by simp

/-- Applying `restrictedCompletionReduction` after the inverse completed Gauss comparison agrees
with `isRestrictedReduction`. -/
theorem restrictedCompletionReduction_restrictedMvPowerSeriesCompletionGaussEquiv_symm
    {J : Ideal R} (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    J.restrictedCompletionReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv.symm f) =
      J.isRestrictedReduction hJ f := by
  simp

end CompleteReduction

end Reduction

section PowerBoundedEvaluation

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T] [CompleteSpace T]
  [T2Space T]

/-- **Comparison of power-bounded evaluations.** For continuous `φ : R →+* T` into a complete
Hausdorff nonarchimedean ring and power-bounded `b : Fin k → T` (without requiring `‖b i‖ ≤ 1`),
`weightedEvalHom` agrees with `restrictedLift` across the Gauss comparison. -/
theorem weightedEvalHom_eq_restrictedLift [NonarchimedeanRing T] {φ : R →+* T}
    (hφ : Continuous φ) {b : Fin k → T} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hφ.continuousAt hb' f =
      restrictedLift hφ hb (restrictedMvPowerSeriesGaussEquiv f) :=
  RingHom.congr_fun (weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (g := (restrictedLift hφ hb).comp
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom)
    (continuous_weightedEvalHom _ _ _)
    ((continuous_restrictedLift hφ hb).comp continuous_restrictedMvPowerSeriesGaussEquiv)
    (fun r ↦ by simp) fun i ↦ by simp) f

/-- **Comparison of linearly topologised evaluations** before completion. -/
theorem weightedEvalAlgHomOfIsLinearTopology_eq_restrictedLiftAlgHomOfIsLinearTopology
    [IsLinearTopology T T] [Algebra R T] (hR : Continuous (algebraMap R T)) (b : Fin k → T)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalAlgHomOfIsLinearTopology isWeightFamily_one_weight hR.continuousAt b f =
      restrictedLiftAlgHomOfIsLinearTopology hR b (restrictedMvPowerSeriesGaussAlgEquiv f) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  rw [coe_restrictedMvPowerSeriesGaussAlgEquiv,
    ← RingHom.coe_coe (weightedEvalAlgHomOfIsLinearTopology _ hR.continuousAt b),
    coe_weightedEvalAlgHomOfIsLinearTopology,
    ← RingHom.coe_coe (restrictedLiftAlgHomOfIsLinearTopology hR b),
    coe_restrictedLiftAlgHomOfIsLinearTopology]
  exact weightedEvalHom_eq_restrictedLift hR
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _))
    (isWeightBounded_of_isLinearTopology (algebraMap R T) _ b) f

section CompletePowerBoundedEvaluation

variable [CompleteSpace R]

/-- **Completed power-bounded evaluation agrees with `restrictedLift`** across the completed Gauss
comparison. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [NonarchimedeanRing T] {φ : R →+* T}
    (hφ : Continuous φ) {b : Fin k → T} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hφ.continuousAt hb' x =
      restrictedLift hφ hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((continuous_restrictedLift hφ hb).comp continuous_restrictedMvPowerSeriesCompletionGaussEquiv))
    fun f ↦ by simp [weightedEvalHom_eq_restrictedLift hφ hb hb' f]

/-- **Completed linearly topologised evaluation agrees with
`restrictedLiftAlgHomOfIsLinearTopology`** across the completed Gauss comparison. -/
theorem weightedEvalCompletionAlgHomOfIsLinearTopology_eq_restrictedLiftAlgHomOfIsLinearTopology
    [IsLinearTopology T T] [Algebra R T] (hR : Continuous (algebraMap R T)) (b : Fin k → T)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalCompletionAlgHomOfIsLinearTopology isWeightFamily_one_weight hR.continuousAt b x =
      restrictedLiftAlgHomOfIsLinearTopology hR b
        (restrictedMvPowerSeriesCompletionGaussAlgEquiv x) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  rw [coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    ← RingHom.coe_coe (weightedEvalCompletionAlgHomOfIsLinearTopology _ hR.continuousAt b),
    coe_weightedEvalCompletionAlgHomOfIsLinearTopology,
    ← RingHom.coe_coe (restrictedLiftAlgHomOfIsLinearTopology hR b),
    coe_restrictedLiftAlgHomOfIsLinearTopology]
  exact weightedEvalHomCompletion_eq_restrictedLift hR
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _))
    (isWeightBounded_of_isLinearTopology (algebraMap R T) _ b) x

end CompletePowerBoundedEvaluation

end PowerBoundedEvaluation

end TauCeti.Huber

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

section Adic

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- **Adic topology of Gauss-normed restricted series.** When the norm topology of `R` is defined
by a finitely generated ideal `I`, the Gauss norm topology on `R⟨X₁, …, Xₖ⟩` is the adic topology
of `I · R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestricted_subring (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let er := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have h := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap er.symm
    (Homeomorph.mk er.symm.toEquiv continuous_restrictedMvPowerSeriesGaussEquiv_symm
      (by simpa [er] using continuous_restrictedMvPowerSeriesGaussEquiv)).isInducing
  have hcomap : (I.map (algebraMap R _)).comap er.symm =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
    rw [← Ideal.map_comap_of_equiv, ← RingEquiv.toRingHom_eq_coe, Ideal.map_map]
    exact congrArg (I.map ·)
      (RingHom.ext fun r ↦ by simp [er, algebraMap_weightedRestrictedSubring])
  rwa [hcomap] at h

/-- Reduction modulo `I ^ m` on `R⟨X₁, …, Xₖ⟩` has kernel `(I · R⟨X₁, …, Xₖ⟩) ^ m` for every
finitely generated ideal of definition `I` and `m : ℕ`. -/
theorem ker_isRestrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker ((I ^ m).isRestrictedReduction (σ := Fin k) (hI.isOpen_pow m)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m := by
  let e := restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)
  have hker : RingHom.ker ((I ^ m).isRestrictedReduction (σ := Fin k) (hI.isOpen_pow m)) =
      (RingHom.ker ((I ^ m).restrictedReduction (k := k) (hI.isOpen_pow m))).map e := by
    ext f
    rw [Ideal.mem_map_iff_of_surjective e e.surjective]
    refine ⟨fun hf ↦ ⟨e.symm f, ?_, e.apply_symm_apply f⟩, ?_⟩
    · rw [RingHom.mem_ker] at hf ⊢; simpa [e] using hf
    · rintro ⟨g, hg, rfl⟩; rw [RingHom.mem_ker] at hg ⊢; simpa [e] using hg
  rw [hker, ker_restrictedReduction_pow hI hfg m]
  simp [Ideal.map_pow, ← algebraMap_weightedRestrictedSubring]

/-- Reduction modulo a finitely generated ideal of definition `I` on `R⟨X₁, …, Xₖ⟩` has kernel
`I · R⟨X₁, …, Xₖ⟩`. -/
theorem ker_isRestrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.isRestrictedReduction (σ := Fin k)
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  rw [← pow_one (I.map _), ← ker_isRestrictedReduction_pow (k := k) hI hfg 1]
  ext f; rw [Ideal.mem_ker_isRestrictedReduction, Ideal.mem_ker_isRestrictedReduction]; simp

/-- **Polynomial quotient equivalence on Gauss-normed restricted series** modulo
`(I · R⟨X₁, …, Xₖ⟩) ^ m`, for a finitely generated ideal of definition `I`. -/
noncomputable def quotientIsRestrictedPowEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) := by
  let e := (Ideal.quotEquivOfEq (ker_isRestrictedReduction_pow (k := k) hI hfg m).symm).trans
    (((I ^ m).isRestrictedReduction (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      ((I ^ m).isRestrictedReduction_surjective (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) =
      (I ^ m).isRestrictedReduction (hI.isOpen_pow m) (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he, Ideal.isRestrictedReduction_algebraMap]; rfl

/-- On a represented series, `quotientIsRestrictedPowEquivMvPolynomialQuotient` computes its
open-ideal polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientIsRestrictedPowEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedReduction (hI.isOpen_pow m) f := by
  simp [quotientIsRestrictedPowEquivMvPolynomialQuotient]

/-- **Polynomial quotient equivalence on Gauss-normed restricted series modulo `I`.** -/
noncomputable def quotientIsRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) :=
  ((Ideal.quotientEquivAlgOfEq R (pow_one _).symm).trans
    (quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg 1)).trans
    (MvPolynomial.mapAlgEquiv (Fin k) (Ideal.quotientEquivAlgOfEq R (pow_one I)))

/-- On a represented series, `quotientIsRestrictedEquivMvPolynomialQuotient` computes its
open-ideal polynomial reduction modulo `I`. -/
@[simp]
theorem quotientIsRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      I.isRestrictedReduction (by simpa only [pow_one] using hI.isOpen_pow 1) f := by
  simp only [quotientIsRestrictedEquivMvPolynomialQuotient, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, quotientIsRestrictedPowEquivMvPolynomialQuotient_mk,
    MvPolynomial.mapAlgEquiv_apply, Ideal.quotientEquivAlgOfEq_coe_eq_factor]
  exact map_isRestrictedReduction _ _ _ _

/-- **Compatibility of adic polynomial quotients with the uncompleted Gauss comparison.** -/
@[simp]
theorem
    quotientIsRestrictedPowEquivMvPolynomialQuotient_restrictedMvPowerSeriesGaussAlgEquiv
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (q : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight) ^ m) :
    quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg m
        (Ideal.quotientEquivAlg _ _ restrictedMvPowerSeriesGaussAlgEquiv
          (by simp [Ideal.map_pow, Ideal.map_coe, ← algebraMap_weightedRestrictedSubring,
            Ideal.map_map_algebraMap]) q) =
      quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m q := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q; simp

/-- **Compatibility of `quotientIsRestrictedEquivMvPolynomialQuotient` with the uncompleted Gauss
comparison.** -/
@[simp]
theorem
    quotientIsRestrictedEquivMvPolynomialQuotient_restrictedMvPowerSeriesGaussAlgEquiv
    (hI : IsAdic I) (hfg : I.FG)
    (q : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight)) :
    quotientIsRestrictedEquivMvPolynomialQuotient hI hfg
        (Ideal.quotientEquivAlg _ _ restrictedMvPowerSeriesGaussAlgEquiv
          (by simp [Ideal.map_coe, ← algebraMap_weightedRestrictedSubring,
            Ideal.map_map_algebraMap]) q) =
      quotientRestrictedEquivMvPolynomialQuotient hI hfg q := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q; simp

/-- Over an `I`-adically separated ultrametric normed ring whose norm topology is `I`-adic, a
series in `R⟨X₁, …, Xₖ⟩` is uniquely determined by its reductions modulo `I ^ (m + 1)`. -/
theorem isRestrictedReduction_pow_succ_injective (hI : IsAdic I) [IsHausdorff I R] :
    Function.Injective (fun (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (m : ℕ) ↦
      (I ^ (m + 1)).isRestrictedReduction (hI.isOpen_pow (m + 1)) f) := fun _ _ hfg ↦
  (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.injective <|
    restrictedReduction_pow_succ_injective hI (funext fun m ↦ by simpa using congrFun hfg m)

/-- **Inverse-limit characterisation on the Gauss-normed carrier** (EGA I, Ch. 0, §7.5.1), over an
`I`-adically complete ultrametric normed ring whose norm topology is `I`-adic (with no finite
generation assumption on `I`). -/
theorem existsUnique_isRestrictedReduction_pow_succ_eq (hI : IsAdic I) [IsAdicComplete I R]
    (p : ∀ m : ℕ, MvPolynomial (Fin k) (R ⧸ I ^ (m + 1)))
    (hp : ∀ m : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ)) (p (m + 1)) = p m) :
    ∃! f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1),
      ∀ m : ℕ, (I ^ (m + 1)).isRestrictedReduction (hI.isOpen_pow (m + 1)) f = p m := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_restrictedReduction_pow_succ_eq hI p hp
  exact ⟨restrictedMvPowerSeriesGaussEquiv g, fun m ↦ by simp [hg m], fun f hf ↦
    (restrictedMvPowerSeriesGaussEquiv.apply_symm_apply f).symm.trans <|
      congrArg restrictedMvPowerSeriesGaussEquiv <|
        huniq (restrictedMvPowerSeriesGaussEquiv.symm f) fun m ↦ by simp [hf m]⟩

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` as the inverse limit of polynomial reductions**, over an
`I`-adically complete ultrametric normed ring whose norm topology is `I`-adic (with no finite
generation assumption on `I`). -/
noncomputable def liftIsRestrictedReductionPowSucc {S : Type*} [NonAssocSemiring S]
    (hI : IsAdic I) [IsAdicComplete I R]
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (R ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m) :
    S →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
  (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom.comp
    (liftRestrictedReductionPowSucc hI φ hφ)

/-- Reducing `liftIsRestrictedReductionPowSucc hI φ hφ s` modulo `I ^ (m + 1)` recovers `φ m s`. -/
@[simp]
theorem isRestrictedReduction_pow_succ_liftIsRestrictedReductionPowSucc {S : Type*}
    [NonAssocSemiring S] (hI : IsAdic I) [IsAdicComplete I R]
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (R ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m)
    (m : ℕ) (s : S) :
    (I ^ (m + 1)).isRestrictedReduction (hI.isOpen_pow (m + 1))
        (liftIsRestrictedReductionPowSucc hI φ hφ s) = φ m s := by
  simp [liftIsRestrictedReductionPowSucc]

/-- Uniqueness of `liftIsRestrictedReductionPowSucc`. -/
theorem eq_liftIsRestrictedReductionPowSucc {S : Type*} [NonAssocSemiring S] (hI : IsAdic I)
    [IsAdicComplete I R] (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (R ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m)
    {ψ : S →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)}
    (hψ : ∀ m : ℕ,
      ((I ^ (m + 1)).isRestrictedReduction (hI.isOpen_pow (m + 1))).comp ψ = φ m) :
    ψ = liftIsRestrictedReductionPowSucc hI φ hφ :=
  RingHom.ext fun s ↦ isRestrictedReduction_pow_succ_injective hI <| funext fun m ↦
    (RingHom.congr_fun (hψ m) s).trans
      (isRestrictedReduction_pow_succ_liftIsRestrictedReductionPowSucc hI φ hφ m s).symm

/-- Over an adic ultrametric normed ring of finite ideal type, `R⟨X₁, …, Xₖ⟩` is an adic ring of
finite ideal type. -/
instance isAdicRing_isRestricted_subring (k : ℕ) [IsAdicRing R] :
    IsAdicRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  have hJ := isAdic_map_algebraMap_isRestricted_subring k hI hfg
  exact ⟨_, hfg.map _, hJ, hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

section CompleteAdic

variable [CompleteSpace R]

/-- **Compatibility of adic polynomial quotients with the completed Gauss comparison.** -/
@[simp]
theorem
    quotientIsRestrictedPowEquivMvPolynomialQuotient_restrictedMvPowerSeriesCompletionGaussAlgEquiv
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (q : restrictedMvPowerSeriesCompletion k R ⧸
      I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R)) ^ m) :
    quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg m
        (Ideal.quotientEquivAlg _ _ restrictedMvPowerSeriesCompletionGaussAlgEquiv
          (by simp [Ideal.map_pow, Ideal.map_coe, Ideal.map_map_algebraMap]) q) =
      quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q; simp

/-- **Compatibility of `quotientIsRestrictedEquivMvPolynomialQuotient` with the completed Gauss
comparison.** -/
@[simp]
theorem
    quotientIsRestrictedEquivMvPolynomialQuotient_restrictedMvPowerSeriesCompletionGaussAlgEquiv
    (hI : IsAdic I) (hfg : I.FG)
    (q : restrictedMvPowerSeriesCompletion k R ⧸
      I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R))) :
    quotientIsRestrictedEquivMvPolynomialQuotient hI hfg
        (Ideal.quotientEquivAlg _ _ restrictedMvPowerSeriesCompletionGaussAlgEquiv
          (by simp [Ideal.map_coe, Ideal.map_map_algebraMap]) q) =
      quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q; simp

/-- **Noetherianity of Gauss-normed restricted series over a complete noetherian adic ring.** -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic (k : ℕ) [IsNoetherianRing R]
    (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

end CompleteAdic

/-- Over a noetherian adic ultrametric normed ring, `R⟨X₁, …, Xₖ⟩` is noetherian (and hence
strongly noetherian via `IsStronglyNoetherian.of_isAdicRing`). -/
instance isNoetherianRing_isRestricted_subring_of_isAdicRing (k : ℕ) [IsAdicRing R]
    [IsNoetherianRing R] :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  isNoetherianRing_isRestricted_subring_of_isAdic k (IsAdicRing.ideal_spec R).2.1

end Adic

end TauCeti.MvPowerSeries
