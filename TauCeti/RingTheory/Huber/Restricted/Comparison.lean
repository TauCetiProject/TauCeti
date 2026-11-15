/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Coefficient maps, reductions, and universal properties under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers.
This file proves that their coefficient maps, polynomial reductions, adic topologies, noetherianity
theorems, and continuous evaluation universal properties agree wherever both constructions apply,
both before and after completion.

1. **Bounded coefficient maps and normed evaluation.** The coefficient map may be bounded by an
   arbitrary constant, not necessarily contractive, and the evaluation points have coordinate norms
   at most one. Evaluation on the completed Huber carrier satisfies the same Gauss-norm bound as the
   coefficient homomorphism. Completeness of the source coefficients is needed only for comparisons
   involving the source completion.
2. **Adic topology, polynomial reductions, and noetherianity on the Gauss carrier.** When the
   ultrametric normed base `R` carries the adic topology of a finitely generated ideal `I`, the
   Gauss-normed carrier `MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)` carries
   the `(I · R⟨X⟩)`-adic topology, its quotients modulo `(I · R⟨X⟩) ^ m` (`m ≠ 0`) are isomorphic
   to `(R ⧸ I ^ m)[X₁, …, Xₖ]` compatibly with coefficient maps and completion, and when `R` is
   complete and noetherian it is strongly noetherian. Over the valuation ring `𝒪[K]` of an
   ultrametric field `K`, Huber reduction modulo the maximal ideal agrees with unit-ball reduction
   `TauCeti.MvPowerSeries.restrictedReduction` without assuming `𝒪[K]` adic or compact.
3. **Explicit distinction between universal properties.** Normed evaluation requires a norm-bounded
   coefficient map and `‖a i‖ ≤ 1`; the topological universal property requires a continuous
   coefficient map into a complete Hausdorff nonarchimedean ring and power-bounded `b i`; and for a
   linearly topologised target (`[IsLinearTopology S S]`), open-ideal neighbourhoods make every
   element power-bounded so arbitrary `b i` lift uniquely. Conversely, no nontrivial `T₁` Tate ring
   carries a linear topology (`IsTateRing.not_isLinearTopology`), and over an ultrametric field `K`
   into a complete Hausdorff Huber ring `B`, power-boundedness of every coordinate is both necessary
   and sufficient for a continuous extension.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `weightedEvalHom_eq_restrictedEval₂OfBound` and
  `weightedEvalHomCompletion_eq_restrictedEval₂OfBound`: topological evaluation is normed
  evaluation when norm bounds hold, with Gauss-norm bound `norm_weightedEvalHomCompletion_le`.
* `isAdic_map_algebraMap_isRestricted_subring`,
  `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient`, and
  `isNoetherianRing_isRestricted_subring_of_isAdic`: adic topology, polynomial reductions modulo
  `I ^ m`, and noetherianity on the Gauss-normed carrier.
* `restrictedReduction_restrictedIntegerEquiv_gaussEquiv` and
  `restrictedReduction_restrictedIntegerEquiv_completionGaussEquiv`: Huber reduction modulo the
  maximal ideal of `𝒪[K]` agrees with unit-ball reduction `T° →+* 𝓀[K][X]`.
* `restrictedLift_eq_restrictedEval₂OfBound`,
  `existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology`,
  `IsTateRing.not_isLinearTopology`, and `exists_continuous_ringHom_isRestricted_subring_iff`:
  agreement and sharp hypothesis distinctions between the normed, topological, and linear-topology
  universal properties.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.1.1–5.1.3.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1–7.5.4.
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

section Adic

variable {I : Ideal R}

/-- The Gauss comparison maps the extended ideal `I · R⟨X⟩` of the Huber subring to the extended
ideal `I · R⟨X⟩` of the Gauss-normed subring. -/
theorem restrictedMvPowerSeriesGaussEquiv_map_ideal (I : Ideal R) :
    (I.map (weightedC (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight)).map
        (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro r
  exact restrictedMvPowerSeriesGaussEquiv_weightedC r

/-- Membership in the extended ideal `I · R⟨X⟩` of the Gauss-normed restricted-series subring is
coefficientwise when `I` is a finitely generated ideal of definition of `R`. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    f ∈ I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ↔
      ∀ ν, coeff ν (f : MvPowerSeries (Fin k) R) ∈ I := by
  rw [← restrictedMvPowerSeriesGaussEquiv_map_ideal,
    Ideal.mem_map_iff_of_surjective
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).surjective]
  refine ⟨?_, fun hf ↦ ⟨restrictedMvPowerSeriesGaussEquiv.symm f,
    (mem_map_weightedC_iff_of_isAdic hI hfg _).mpr (by simpa using hf),
    restrictedMvPowerSeriesGaussEquiv.apply_symm_apply f⟩⟩
  rintro ⟨g, hg, rfl⟩
  simpa using (mem_map_weightedC_iff_of_isAdic hI hfg g).mp hg

/-- When an ultrametric normed ring `R` carries the adic topology of a finitely generated ideal `I`,
the Gauss-normed subring `R⟨X₁, …, Xₖ⟩` carries the adic topology of `I · R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let hhomeo :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ≃ₜ
        IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
    { toEquiv := restrictedMvPowerSeriesGaussEquiv.toEquiv
      continuous_toFun := continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_invFun := continuous_restrictedMvPowerSeriesGaussEquiv_symm }
  have hadic := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI
    hfg).map_of_isOpenQuotientMap
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom hhomeo.isOpenQuotientMap
  rwa [algebraMap_weightedRestrictedSubring, restrictedMvPowerSeriesGaussEquiv_map_ideal] at hadic

/-- Over a complete ultrametric normed ring `R` whose topology is `I`-adic for finitely generated
`I`, the Gauss-normed algebra `R⟨X₁, …, Xₖ⟩` is `(I · R⟨X₁, …, Xₖ⟩)`-adically complete. -/
theorem isAdicComplete_map_algebraMap_isRestricted_subring [CompleteSpace R]
    (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))))
      (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isAdic_map_algebraMap_isRestricted_subring hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- For every nonzero `m`, reducing the Gauss-normed restricted-series algebra modulo
`(I · R⟨X₁, …, Xₖ⟩) ^ m` identifies the quotient with `(R ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).symm (by
    rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro r
    apply Subtype.ext
    simp)).trans
    (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg hm)

/-- `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` acts on a represented series via
Huber polynomial reduction along the inverse Gauss comparison. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      Ideal.restrictedReduction (I ^ m) (hI.isOpen_pow m)
        (restrictedMvPowerSeriesGaussEquiv.symm f) := by
  simp [quotientIsRestrictedSubringPowEquivMvPolynomialQuotient]

/-- The coefficients of `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` on the class of
`f` are the reductions of the coefficients of `f` modulo `I ^ m`. -/
theorem coeff_quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (ν : Fin k →₀ ℕ) :
    (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ f)).coeff ν =
      Ideal.Quotient.mk (I ^ m) (coeff ν (f : MvPowerSeries (Fin k) R)) := by
  simp

/-- On every completion element, `restrictedMvPowerSeriesCompletionGaussEquiv` factors through
`restrictedMvPowerSeriesCompletionEquiv` followed by `restrictedMvPowerSeriesGaussEquiv`. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_apply [CompleteSpace R]
    (x : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionGaussEquiv x =
      restrictedMvPowerSeriesGaussEquiv (restrictedMvPowerSeriesCompletionEquiv k R x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    (continuous_restrictedMvPowerSeriesGaussEquiv.comp
      uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous)) fun f ↦ ?_
  simp

/-- Over a complete coefficient ring `R`, the completed Huber quotient equivalence modulo `I ^ m`
and the Gauss-normed quotient equivalence agree along `restrictedMvPowerSeriesCompletionGaussEquiv`.
-/
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_completion [CompleteSpace R]
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k R) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesCompletionGaussEquiv x)) =
      quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ x) := by
  simp only [quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk,
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
    restrictedMvPowerSeriesCompletionGaussEquiv_apply, RingEquiv.symm_apply_apply,
    restrictedReduction_restrictedMvPowerSeriesCompletionEquiv]

/-- Polynomial reduction on the Gauss-normed carrier commutes with bounded coefficient maps
`restrictedMap`, with no flatness or completeness assumption. -/
theorem restrictedReduction_gaussEquiv_symm_restrictedMap
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) {J : Ideal S}
    (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.restrictedReduction J hJ
        (restrictedMvPowerSeriesGaussEquiv.symm (restrictedMap φ hφ f)) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ)
        (Ideal.restrictedReduction I hI (restrictedMvPowerSeriesGaussEquiv.symm f)) := by
  have hφc : Continuous φ := (AddMonoidHomClass.lipschitz_of_bound φ C hφ).continuous
  rw [← restrictedMvPowerSeriesGaussEquiv.apply_symm_apply f,
    ← restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ,
    RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact restrictedReduction_weightedMap hφc hI hJ hIJ _

/-- **Noetherianity of Gauss-normed restricted series over a complete adic noetherian ring.** -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [CompleteSpace R] [IsNoetherianRing R]
    (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

/-- **Strong noetherianity of Gauss-normed restricted series over a complete adic noetherian ring.**
-/
theorem IsStronglyNoetherian.isRestricted_subring_of_isAdic [CompleteSpace R] [IsNoetherianRing R]
    (hI : IsAdic I) :
    IsStronglyNoetherian (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have : IsAdicRing R := ⟨I, IsNoetherian.noetherian I, hI,
    hI.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩
  exact (isStronglyNoetherian_congr restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm).mp inferInstance

end Adic

section UnitBallReduction

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The maximal ideal of the valuation ring `𝒪[K]` is open for the induced metric topology, without
requiring `𝒪[K]` to be compact or discretely valued. -/
theorem isOpen_maximalIdeal_integer :
    IsOpen (IsLocalRing.maximalIdeal 𝒪[K] : Set 𝒪[K]) := by
  have h : (IsLocalRing.maximalIdeal 𝒪[K] : Set 𝒪[K]) = Metric.ball 0 1 := by
    ext x
    rw [SetLike.mem_coe, Valued.integer.mem_maximalIdeal_iff, mem_ball_zero_iff]
  exact h ▸ Metric.isOpen_ball

/-- Over the valuation ring `𝒪[K]` of a nontrivially normed ultrametric field `K`, Huber polynomial
reduction modulo the maximal ideal agrees with unit-ball reduction
`TauCeti.MvPowerSeries.restrictedReduction : T° →+* 𝓀[K][X]` along
`restrictedMvPowerSeriesGaussEquiv` and `restrictedIntegerEquiv`. -/
theorem restrictedReduction_restrictedIntegerEquiv_gaussEquiv
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set 𝒪[K])) isWeightFamily_one_weight) :
    TauCeti.MvPowerSeries.restrictedReduction (σ := Fin k) (K := K)
        (restrictedIntegerEquiv (σ := Fin k) (K := K)
          (restrictedMvPowerSeriesGaussEquiv (n := k) (R := 𝒪[K]) f)) =
      MvPolynomial.map (σ := Fin k)
        (Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.residue 𝒪[K])
          fun x hx ↦ (IsLocalRing.residue_eq_zero_iff x).mpr hx)
        (Ideal.restrictedReduction (k := k) (IsLocalRing.maximalIdeal 𝒪[K])
          isOpen_maximalIdeal_integer f) := by
  ext ν
  rw [TauCeti.MvPowerSeries.coeff_restrictedReduction, MvPolynomial.coeff_map,
    Ideal.coeff_restrictedReduction, Ideal.Quotient.lift_mk]
  exact congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext (by simp))

/-- Over a complete nontrivially normed ultrametric field `K`, completed Huber polynomial reduction
on `restrictedMvPowerSeriesCompletion k 𝒪[K]` modulo the maximal ideal agrees with unit-ball
reduction `TauCeti.MvPowerSeries.restrictedReduction` along
`restrictedMvPowerSeriesCompletionGaussEquiv` and `restrictedIntegerEquiv`. -/
theorem restrictedReduction_restrictedIntegerEquiv_completionGaussEquiv [CompleteSpace K]
    (x : restrictedMvPowerSeriesCompletion k 𝒪[K]) :
    TauCeti.MvPowerSeries.restrictedReduction (σ := Fin k) (K := K)
        (restrictedIntegerEquiv (σ := Fin k) (K := K)
          (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := 𝒪[K]) x)) =
      MvPolynomial.map (σ := Fin k)
        (Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.residue 𝒪[K])
          fun y hy ↦ (IsLocalRing.residue_eq_zero_iff y).mpr hy)
        (Ideal.restrictedReductionCompletion (k := k) (IsLocalRing.maximalIdeal 𝒪[K])
          isOpen_maximalIdeal_integer x) := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_apply,
    restrictedReduction_restrictedIntegerEquiv_gaussEquiv,
    restrictedReduction_restrictedMvPowerSeriesCompletionEquiv]

end UnitBallReduction

section UniversalProperties

/-- Topological Huber evaluation `weightedEvalHom` composed with the inverse Gauss comparison is
`TauCeti.MvPowerSeries.restrictedLift`, independently of the chosen weight-boundedness witness. -/
theorem weightedEvalHom_comp_gaussEquiv_symm_eq_restrictedLift
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
    [CompleteSpace B] [T2Space B] {θ : R →+* B} (hθ : Continuous θ) {b : Fin k → B}
    (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded θ (fun _ : Fin k ↦ ({1} : Set R)) b) :
    (weightedEvalHom isWeightFamily_one_weight hθ.continuousAt hb').comp
        (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom =
      restrictedLift hθ hb :=
  restrictedLift_unique hθ hb
    ((continuous_weightedEvalHom _ _ _).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm)
    (fun r ↦ by simp [← restrictedMvPowerSeriesGaussEquiv_weightedC])
    (fun i ↦ by simp [← restrictedMvPowerSeriesGaussEquiv_weightedX])

/-- Over a complete base `R`, completed `R`-algebra Huber evaluation `weightedEvalAlgHomCompletion`
agrees with `TauCeti.MvPowerSeries.restrictedLift` through the completed Gauss comparison. -/
theorem weightedEvalAlgHomCompletion_eq_restrictedLift [CompleteSpace R]
    {B : Type*} [CommRing B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
    [NonarchimedeanRing B] [CompleteSpace B] [T2Space B]
    (hR : Continuous (algebraMap R B)) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded (algebraMap R B) (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalAlgHomCompletion isWeightFamily_one_weight hR.continuousAt hb' x =
      restrictedLift hR hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalAlgHomCompletion _ _ _)
    ((continuous_restrictedLift hR hb).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) fun f ↦ ?_
  rw [coe_weightedEvalAlgHomCompletion, weightedEvalHomCompletion_coe,
    restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    ← weightedEvalHom_comp_gaussEquiv_symm_eq_restrictedLift hR hb hb', RingHom.comp_apply]
  simp

/-- When `φ : R →+* S` is norm-bounded (`∀ r, ‖φ r‖ ≤ C * ‖r‖`) and `∀ i, ‖a i‖ ≤ 1`, the
topological power-bounded lift `restrictedLift` agrees with normed bounded evaluation
`φ.restrictedEval₂OfBound`. -/
theorem restrictedLift_eq_restrictedEval₂OfBound [CompleteSpace S] {a : Fin k → S}
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, IsPowerBounded (a i)) :
    restrictedLift ((AddMonoidHomClass.lipschitz_of_bound φ C hφ).continuous) hb =
      φ.restrictedEval₂OfBound a hφ ha :=
  φ.eq_restrictedEval₂OfBound a hφ ha _
    (continuous_restrictedLift _ hb)
    (restrictedLift_algebraMap _ hb)
    (restrictedLift_X _ hb)

/-- Reducing `restrictedLift` modulo an open ideal `J` of `B` agrees with evaluating the polynomial
reduction of the series at the reduced tuple. -/
theorem mk_restrictedLift_eq_eval₂_restrictedReduction
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
    [CompleteSpace B] [T2Space B] {θ : R →+* B} (hθ : Continuous θ) {b : Fin k → B}
    (hb : ∀ i, IsPowerBounded (b i)) {I : Ideal R} {J : Ideal B}
    (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap θ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLift hθ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J θ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (Ideal.restrictedReduction I hI (restrictedMvPowerSeriesGaussEquiv.symm f)) := by
  rw [← weightedEvalHom_comp_gaussEquiv_symm_eq_restrictedLift hθ hb
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded θ b).mpr hb), RingHom.comp_apply]
  exact mk_weightedEvalHom_eq_eval₂_restrictedReduction hθ.continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded θ b).mpr hb) hI hJ hIJ _

/-- **The universal property of `R⟨X₁, …, Xₖ⟩` into linearly topologised `R`-algebras.** When `B`
carries `[IsLinearTopology B B]`, open-ideal neighbourhoods make every element of `B` power-bounded,
so *arbitrary* choices `b : Fin k → B` define a unique continuous `R`-algebra homomorphism out of
the Gauss-normed restricted-series subring. -/
theorem existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology
    {B : Type*} [CommRing B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
    [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    (hR : Continuous (algebraMap R B)) (b : Fin k → B) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] B,
      Continuous ψ ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  have hb : ∀ i, IsPowerBounded (b i) := fun i ↦
    mem_powerBoundedSubring.mp (powerBoundedSubring_eq_top (A := B) ▸ Subring.mem_top (b i))
  let ψ₀ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] B :=
    { restrictedLift hR hb with commutes' := restrictedLift_algebraMap hR hb }
  refine ⟨ψ₀, ⟨continuous_restrictedLift hR hb, restrictedLift_X hR hb⟩, fun ψ ⟨hψ, hX⟩ ↦ ?_⟩
  exact AlgHom.toRingHom_injective (restrictedLift_unique hR hb hψ ψ.commutes hX)

/-- **No nontrivial `T₁` Tate ring carries a linear topology.** Every open ideal of a Tate ring is
`⊤` (`IsTateRing.eq_top_of_isOpen`), whereas `{1}ᶜ` is a neighbourhood of `0` in any nontrivial `T₁`
ring. Thus the unrestricted linear-topology evaluation above never applies to nontrivial Hausdorff
Tate targets. -/
theorem IsTateRing.not_isLinearTopology {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] [Nontrivial A] [T1Space A] :
    ¬ IsLinearTopology A A := by
  intro h
  obtain ⟨J, hJ0, hJ1⟩ := (IsLinearTopology.hasBasis_ideal (R := A)).mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := A)))
  have htop : J = ⊤ := IsTateRing.eq_top_of_isOpen (J.toAddSubgroup.isOpen_of_mem_nhds hJ0)
  exact hJ1 (htop ▸ Submodule.mem_top) rfl

/-- **No nontrivially normed ultrametric field carries a linear topology.** -/
theorem not_isLinearTopology_of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] : ¬ IsLinearTopology K K :=
  IsTateRing.not_isLinearTopology

/-- **Exact criterion for continuous extensions out of `K⟨X₁, …, Xₖ⟩` into a Huber ring.** Over a
nontrivially normed ultrametric field `K`, `K⟨X₁, …, Xₖ⟩` is a Tate ring whose variables are
power-bounded, and continuous homomorphisms from a Tate ring to a Huber ring preserve
power-boundedness (`IsPowerBounded.map_of_isTateRing`). Hence a continuous extension sending `Xᵢ` to
`bᵢ` exists if and only if every `bᵢ` is power-bounded. -/
theorem exists_continuous_ringHom_isRestricted_subring_iff
    {K B : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
    [CompleteSpace B] [T2Space B] {θ : K →+* B} (hθ : Continuous θ) (b : Fin k → B) :
    (∃ ψ : IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1) →+* B,
      Continuous ψ ∧ (∀ c, ψ (algebraMap K _ c) = θ c) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) ↔
      ∀ i, IsPowerBounded (b i) := by
  refine ⟨fun ⟨ψ, hψ, _, hX⟩ i ↦ ?_, fun hb ↦
    ⟨restrictedLift hθ hb, continuous_restrictedLift hθ hb,
      restrictedLift_algebraMap hθ hb, restrictedLift_X hθ hb⟩⟩
  rw [← hX i]
  exact (isPowerBounded_X i).map_of_isTateRing hψ.continuousAt

/-- **Exact norm criterion for field-valued continuous extensions out of `K⟨X₁, …, Xₖ⟩`.** Into a
complete ultrametric normed field `L` along continuous `θ : K →+* L`, a continuous extension sending
`Xᵢ` to `bᵢ` exists if and only if `∀ i, ‖bᵢ‖ ≤ 1`. -/
theorem exists_continuous_ringHom_isRestricted_subring_iff_norm_le_one
    {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    {θ : K →+* L} (hθ : Continuous θ) (b : Fin k → L) :
    (∃ ψ : IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1) →+* L,
      Continuous ψ ∧ (∀ c, ψ (algebraMap K _ c) = θ c) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) ↔
      ∀ i, ‖b i‖ ≤ 1 := by
  have : IsHuberRing L := by
    rcases NormedField.discreteTopology_or_nontriviallyNormedField L with _ | ⟨_, rfl⟩
    · infer_instance
    · exact (IsTateRing.of_nontriviallyNormedField L).toIsHuberRing
  simp_rw [exists_continuous_ringHom_isRestricted_subring_iff hθ b, isPowerBounded_iff_norm_le_one]

end UniversalProperties

end TauCeti.Huber
