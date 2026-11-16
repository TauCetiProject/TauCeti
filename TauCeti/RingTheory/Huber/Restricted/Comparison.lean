/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Reduction
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty
import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology

/-!
# Coefficient maps, evaluation, and adic reductions under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers.
This file splits into two layers:

1. **Cross-carrier Huber-vs.-Gauss comparisons (`TauCeti.Huber`)**, proved both before and after
   uniform completion (with completeness of the source ring needed only for the completed Huber
   side): coefficient maps, norm-bounded, power-bounded, and linear-target evaluations, open-ideal
   polynomial reductions, and order-`m` polynomial quotient presentations
   `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]`.
2. **Properties on the Gauss-normed restricted-series carrier (`TauCeti.MvPowerSeries`)**: over an
   `I`-adic normed ring (`I` finitely generated), `R⟨X₁, …, Xₖ⟩` carries the `(I · R⟨X⟩)`-adic
   topology with polynomial quotients `(R ⧸ Iᵐ)[X₁, …, Xₖ]`; when `R` is complete, `R⟨X₁, …, Xₖ⟩`
   is canonically homeomorphic as an `R`-algebra to the `(I · R[X])`-adic completion of
   `MvPolynomial (Fin k) R` and is noetherian whenever `R` is noetherian; and over adic normed
   rings `R` and `S`, `R⟨X₁, …, Xₖ⟩` is an `IsAdicRing` whose completed tensor product
   `R⟨X₁, …, Xₖ⟩ ⊗̂_R S` is topologically isomorphic as an `R`-algebra to `S⟨X₁, …, Xₖ⟩`.

## Main definitions

* `TauCeti.MvPowerSeries.quotientIsRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.MvPowerSeries.quotientPowIsRestrictedEquivMvPolynomialQuotient`: the `R`-algebra
  equivalences `R⟨X⟩ ⧸ (I · R⟨X⟩) ≃ₐ[R] (R ⧸ I)[X]` and
  `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` (`m ≠ 0`) on the Gauss-normed carrier.
* `TauCeti.MvPowerSeries.isRestrictedSubringEquivAdicCompletion`: over a complete `I`-adic normed
  ring `R` with `I` finitely generated, the topological `R`-algebra isomorphism from `R⟨X⟩` to the
  `(I · R[X])`-adic completion of `MvPolynomial (Fin k) R`.
* `TauCeti.MvPowerSeries.isAdicRing_isRestricted_subring` and
  `TauCeti.MvPowerSeries.completedTensorRestrictedGaussEquiv`: the `IsAdicRing` instance on
  `R⟨X₁, …, Xₖ⟩` and the topological `R`-algebra base-change isomorphism
  `R⟨X₁, …, Xₖ⟩ ⊗̂_R S ≃ₐ[R] S⟨X₁, …, Xₖ⟩` over adic normed rings.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `weightedEvalHom_eq_restrictedEval₂OfBound`,
  `weightedEvalHomCompletion_eq_restrictedEval₂OfBound`,
  `weightedEvalHom_eq_restrictedLift`, `weightedEvalHomCompletion_eq_restrictedLift`,
  `weightedEvalHom_eq_restrictedLiftLinear`, and
  `weightedEvalHomCompletion_eq_restrictedLiftLinear`: Huber evaluation agrees with norm-bounded,
  power-bounded, and linear-topology evaluation on the Gauss-normed carrier.
* `restrictedReduction_eq_restrictedIdealReduction`,
  `restrictedCompletionReduction_eq_restrictedIdealReduction`,
  `quotientPowRestrictedEquiv_eq_quotientPowIsRestrictedEquiv`, and
  `quotientPowRestrictedCompletionEquiv_eq_quotientPowIsRestrictedEquiv`: Huber open-ideal
  reductions and order-`m` polynomial quotient equivalences agree with their Gauss-normed
  counterparts.
* `isAdic_map_algebraMap_isRestricted_subring` and
  `isNoetherianRing_isRestricted_subring_of_isAdic`: the Gauss-norm topology on `R⟨X⟩` over an
  `I`-adic normed ring (`I` finitely generated) is `(I · R⟨X⟩)`-adic, and `R⟨X⟩` is noetherian
  when `R` is complete and noetherian.
* `coe_completedTensorRestrictedGaussEquiv_inl`,
  `completedTensorRestrictedGaussEquiv_inl`,
  `completedTensorRestrictedGaussEquiv_inl_of_norm_le`, and
  `completedTensorRestrictedGaussEquiv_inr`: completed-tensor base change acts unconditionally on
  `R⟨X⟩` by coefficientwise application of `algebraMap R S` (agreeing with `restrictedMap` when
  `algebraMap R S` is norm-bounded) and on `S` as `algebraMap`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries Topology

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

/-- Huber open-ideal polynomial reduction and normed open-ideal reduction agree across the Gauss
comparison. -/
theorem restrictedReduction_eq_restrictedIdealReduction {J : Ideal R} (hJ : IsOpen (J : Set R))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    Ideal.restrictedReduction J hJ f =
      restrictedIdealReduction J hJ (restrictedMvPowerSeriesGaussEquiv f) := by
  ext ν
  simp

/-- Over a complete coefficient ring, completed Huber polynomial reduction agrees with normed
open-ideal reduction across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem restrictedCompletionReduction_eq_restrictedIdealReduction [CompleteSpace R]
    {J : Ideal R} (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
    Ideal.restrictedCompletionReduction J hJ x =
      restrictedIdealReduction J hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  conv_lhs => rw [← restrictedMvPowerSeriesCompletionGaussEquiv.symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
    Ideal.restrictedCompletionReduction_coe,
    restrictedReduction_eq_restrictedIdealReduction hJ, RingEquiv.apply_symm_apply]

end Reduction

section PowerBoundedAndLinearEvaluation

/-- Topological evaluation into a complete Hausdorff nonarchimedean ring agrees with
`restrictedLift` across the Gauss comparison. -/
theorem weightedEvalHom_eq_restrictedLift {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb' f =
      restrictedLift hψ hb (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [restrictedLift_apply, RingEquiv.symm_apply_apply]

/-- Completed topological evaluation into a complete Hausdorff nonarchimedean ring agrees with
`restrictedLift` across the completed Gauss comparison. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [CompleteSpace R] {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt hb' x =
      restrictedLift hψ hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ hψ.continuousAt hb')
    ((continuous_restrictedLift hψ hb).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedLift hψ hb hb']

/-- Topological evaluation into a complete Hausdorff linearly topologized ring agrees with
`restrictedLiftLinear` across the Gauss comparison. -/
theorem weightedEvalHom_eq_restrictedLiftLinear {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [IsLinearTopology B B]
    [CompleteSpace B] [T2Space B] {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    (hb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb f =
      restrictedLiftLinear hψ b (restrictedMvPowerSeriesGaussEquiv f) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have hbPB := (isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mp hb
  rw [restrictedLiftLinear_eq_restrictedLift hψ hbPB]
  exact weightedEvalHom_eq_restrictedLift hψ hbPB hb f

/-- Completed topological evaluation into a complete Hausdorff linearly topologized ring agrees
with `restrictedLiftLinear` across the completed Gauss comparison. -/
theorem weightedEvalHomCompletion_eq_restrictedLiftLinear [CompleteSpace R]
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [NonarchimedeanRing B] [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    (hb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt hb x =
      restrictedLiftLinear hψ b (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have hbPB := (isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mp hb
  rw [restrictedLiftLinear_eq_restrictedLift hψ hbPB]
  exact weightedEvalHomCompletion_eq_restrictedLift hψ hbPB hb x

end PowerBoundedAndLinearEvaluation

end TauCeti.Huber

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber Topology

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {C : ℝ}

section EvalReduction

/-- Reducing `restrictedLift` modulo an open ideal `J` of the target agrees with polynomial
evaluation of `restrictedIdealReduction` modulo `I`. -/
theorem mk_restrictedLift_eq_eval₂_restrictedIdealReduction {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    {I : Ideal R} {J : Ideal B} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap ψ) (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLift hψ hb g) =
      (restrictedIdealReduction I hI g).eval₂ (Ideal.quotientMap J ψ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  rw [restrictedLift_apply,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction hψ.continuousAt _ hI hJ hIJ,
    restrictedReduction_eq_restrictedIdealReduction hI, RingEquiv.apply_symm_apply]

/-- Reducing `restrictedLiftLinear` modulo an open ideal `J` of a linearly topologized target ring
agrees with polynomial evaluation of `restrictedIdealReduction` modulo `I`. -/
theorem mk_restrictedLiftLinear_eq_eval₂_restrictedIdealReduction {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    {I : Ideal R} {J : Ideal B} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap ψ) (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLiftLinear hψ b g) =
      (restrictedIdealReduction I hI g).eval₂ (Ideal.quotientMap J ψ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  have hb : ∀ i, IsPowerBounded (b i) :=
    fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  rw [restrictedLiftLinear_eq_restrictedLift hψ hb]
  exact mk_restrictedLift_eq_eval₂_restrictedIdealReduction hψ hb hI hJ hIJ g

end EvalReduction

section Adic

variable {I : Ideal R}

/-- **Adic topology of Gauss-normed restricted series.** If `R` has the `I`-adic topology for a
finitely generated ideal `I`, then `R⟨X₁, …, Xₖ⟩` under the Gauss norm has the `(I · R⟨X⟩)`-adic
topology. -/
theorem isAdic_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hInd : IsInducing e.symm :=
    (Homeomorph.mk e.symm.toEquiv continuous_restrictedMvPowerSeriesGaussEquiv_symm
      continuous_restrictedMvPowerSeriesGaussEquiv).isInducing
  convert (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap e.symm hInd
  rw [← Ideal.map_comap_of_equiv, Ideal.map_map]
  exact congrArg (Ideal.map · I)
    (RingHom.ext fun _ ↦ by simp [e, algebraMap_weightedRestrictedSubring])

/-- Membership in the extension of a finitely generated ideal of definition `I` to `R⟨X₁, …, Xₖ⟩`
is coefficientwise. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    g ∈ I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ↔
      ∀ ν, coeff ν (g : MvPowerSeries (Fin k) R) ∈ I := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hmap : I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) =
      (I.map (weightedC _ isWeightFamily_one_weight)).map e := by
    conv_rhs => rw [← Ideal.map_coe, Ideal.map_map]
    exact congrArg (Ideal.map · I)
      (RingHom.ext fun r ↦ (restrictedMvPowerSeriesGaussEquiv_weightedC r).symm)
  rw [hmap, ← Ideal.symm_apply_mem_of_equiv_iff, mem_map_weightedC_iff_of_isAdic hI hfg]
  simp [e]

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo a finitely generated ideal of definition `I` has kernel
`I · R⟨X⟩`. -/
theorem ker_restrictedIdealReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedIdealReduction (σ := Fin k) I (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  ext g
  rw [RingHom.mem_ker, restrictedIdealReduction_eq_zero_iff,
    mem_map_algebraMap_isRestricted_subring_iff_of_isAdic hI hfg]

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo `I ^ m` (`m ≠ 0`) for a finitely generated ideal of
definition `I` has kernel `(I · R⟨X⟩) ^ m`. -/
theorem ker_restrictedIdealReduction_pow (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    RingHom.ker (restrictedIdealReduction (σ := Fin k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m :=
  Ideal.map_pow (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) I m ▸
    ker_restrictedIdealReduction (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow

/-- Infinitesimal reduction modulo `I · R⟨X⟩` on Gauss-normed restricted series. -/
noncomputable def quotientIsRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) := by
  let hopen : IsOpen (I : Set R) := pow_one I ▸ hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq (ker_restrictedIdealReduction (k := k) hI hfg).symm).trans
    ((restrictedIdealReduction I hopen).quotientKerEquivOfSurjective
      (restrictedIdealReduction_surjective I hopen))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]; simp [e, -Ideal.Quotient.mk_algebraMap]

/-- On a represented series, `quotientIsRestrictedEquivMvPolynomialQuotient` computes
`restrictedIdealReduction` modulo `I`. -/
@[simp]
theorem quotientIsRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ g) =
      restrictedIdealReduction I (pow_one I ▸ hI.isOpen_pow 1) g := by
  simp [quotientIsRestrictedEquivMvPolynomialQuotient]

/-- **Infinitesimal thickening on Gauss-normed restricted series**: for `m ≠ 0`, reducing modulo
`(I · R⟨X⟩) ^ m` gives `(R ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientPowIsRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq R (Ideal.map_pow _ I m).symm).trans
    (quotientIsRestrictedEquivMvPolynomialQuotient
      (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow)

/-- On a represented series, `quotientPowIsRestrictedEquivMvPolynomialQuotient` computes
`restrictedIdealReduction` modulo `I ^ m`. -/
@[simp]
theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ g) =
      restrictedIdealReduction (I ^ m) (hI.isOpen_pow m) g := by
  simp [quotientPowIsRestrictedEquivMvPolynomialQuotient]

section CompleteAdic

variable [CompleteSpace R]

/-- **Inverse-limit presentation of `R⟨X₁, …, Xₖ⟩` over a complete adic normed ring**
(EGA I, Ch. 0, §7.5.1). Over a complete ultrametric normed commutative ring `R` with finitely
generated ideal of definition `I`, the Gauss-normed restricted-series algebra `R⟨X₁, …, Xₖ⟩` is
isomorphic as an `R`-algebra to the `(I · R[X])`-adic completion of `MvPolynomial (Fin k) R`. -/
noncomputable def isRestrictedSubringEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ≃ₐ[R]
      AdicCompletion (I.map (MvPolynomial.C (σ := Fin k))) (MvPolynomial (Fin k) R) :=
  (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).symm.trans
    (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg)

/-- On an embedded polynomial, `isRestrictedSubringEquivAdicCompletion` agrees with the canonical
`algebraMap` into the adic completion of `MvPolynomial (Fin k) R`. -/
@[simp]
theorem isRestrictedSubringEquivAdicCompletion_polynomialToRestricted
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) R) :
    isRestrictedSubringEquivAdicCompletion hI hfg (polynomialToRestricted (fun _ : Fin k ↦ 1) p) =
      algebraMap (MvPolynomial (Fin k) R) _ p := by
  rw [isRestrictedSubringEquivAdicCompletion, AlgEquiv.trans_apply,
    coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm,
    restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
    ← restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom, RingEquiv.symm_apply_apply,
    restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom]

/-- The inverse of `isRestrictedSubringEquivAdicCompletion` sends an embedded polynomial in
`AdicCompletion` to `polynomialToRestricted`. -/
@[simp]
theorem isRestrictedSubringEquivAdicCompletion_symm_algebraMap
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) R) :
    (isRestrictedSubringEquivAdicCompletion hI hfg).symm
        (algebraMap (MvPolynomial (Fin k) R) _ p) =
      polynomialToRestricted (fun _ : Fin k ↦ 1) p := by
  rw [AlgEquiv.symm_apply_eq, isRestrictedSubringEquivAdicCompletion_polynomialToRestricted]

/-- `isRestrictedSubringEquivAdicCompletion` is a homeomorphism when `AdicCompletion` carries the
adic topology of the extended ideal. -/
theorem isHomeomorph_isRestrictedSubringEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    @IsHomeomorph _ _ _
      ((I.map (MvPolynomial.C (σ := Fin k))).map (algebraMap _ _)).adicTopology
      (isRestrictedSubringEquivAdicCompletion (k := k) hI hfg) := by
  let _ : TopologicalSpace (AdicCompletion
      (I.map (MvPolynomial.C (σ := Fin k))) (MvPolynomial (Fin k) R)) :=
    ((I.map (MvPolynomial.C (σ := Fin k))).map (algebraMap _ _)).adicTopology
  let e1 := (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).symm
  have h1 : IsHomeomorph e1 := e1.toEquiv.isHomeomorph_iff.mpr
    ⟨by simpa [e1] using continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm,
     by simpa [e1] using continuous_restrictedMvPowerSeriesCompletionGaussEquiv⟩
  exact (isHomeomorph_restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg).comp h1

/-- Under `isRestrictedSubringEquivAdicCompletion`, the `m`-th inverse-limit projection (`m ≠ 0`)
identifies with polynomial reduction modulo `I ^ m` via
`MvPolynomial.quotientEquivQuotientMvPolynomial`. -/
theorem evalₐ_isRestrictedSubringEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    AdicCompletion.evalₐ _ m (isRestrictedSubringEquivAdicCompletion hI hfg g) =
      Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C (σ := Fin k)) I m)
        (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ m)
          (restrictedIdealReduction (I ^ m) (hI.isOpen_pow m) g)) := by
  simp only [isRestrictedSubringEquivAdicCompletion, AlgEquiv.trans_apply,
    evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg hm,
    coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm,
    restrictedCompletionReduction_eq_restrictedIdealReduction, RingEquiv.apply_symm_apply]

/-- **Noetherianity of Gauss-normed restricted power series.** Over a complete noetherian
ultrametric normed commutative ring `R` whose topology is `I`-adic, the Gauss-normed
restricted-series ring `R⟨X₁, …, Xₖ⟩` is noetherian. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [IsNoetherianRing R] (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  isNoetherianRing_of_ringEquiv _ (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

end CompleteAdic

end Adic

section CompletedTensor

/-- Over an adic ultrametric normed commutative ring `R`, the Gauss-normed restricted-series ring
`R⟨X₁, …, Xₖ⟩` is an adic ring of finite ideal type. -/
instance isAdicRing_isRestricted_subring [IsAdicRing R] :
    IsAdicRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  have hJ := isAdic_map_algebraMap_isRestricted_subring (k := k) hI hfg
  exact ⟨_, hfg.map _, hJ, hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

variable [IsAdicRing R] [IsAdicRing S] [Algebra R S] [ContinuousSMul R S]

private noncomputable def coeffMapAlgHom :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R]
      IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1) :=
  { (restrictedMvPowerSeriesGaussEquiv (n := k) (R := S)).toRingHom.comp
      ((weightedMap (continuous_algebraMap R S) isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp)).comp
        (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom) with
    commutes' r := Subtype.ext (by simp [coe_algebraMap_isRestrictedSubring_apply]) }

omit [IsAdicRing R] [IsAdicRing S] in
private theorem continuous_coeffMapAlgHom :
    Continuous (coeffMapAlgHom (k := k) (R := R) (S := S)) :=
  continuous_restrictedMvPowerSeriesGaussEquiv.comp
    ((continuous_weightedMap _ _ _ _).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm)

omit [IsUltrametricDist R] [IsAdicRing R] [IsAdicRing S] [ContinuousSMul R S] in
private theorem continuous_toAlgHom_isRestrictedSubring :
    Continuous (IsScalarTower.toAlgHom R S (IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1))) :=
  isometry_algebraMap_isRestrictedSubring.continuous

private noncomputable def toCompletedTensorGauss :
    AdicRing.CompletedTensorProduct R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S →ₐ[R]
      IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1) :=
  AdicRing.CompletedTensorProduct.lift (coeffMapAlgHom (k := k) (R := R) (S := S))
    (IsScalarTower.toAlgHom R S (IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1)))
    continuous_coeffMapAlgHom continuous_toAlgHom_isRestrictedSubring

omit [ContinuousSMul R S] in
private theorem ofCompletedTensorGauss_commutes (r : R) :
    restrictedLiftLinear (AdicRing.CompletedTensorProduct.continuous_inr R
        (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S)
      (fun i ↦ AdicRing.CompletedTensorProduct.inl R _ S
        ⟨X i, IsRestricted.mem_subring.mpr (isRestricted_X _ i)⟩)
      (algebraMap R (IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1)) r) =
      algebraMap R (AdicRing.CompletedTensorProduct R
        (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S) r := by
  rw [IsScalarTower.algebraMap_apply R S, restrictedLiftLinear_algebraMap]
  exact (AdicRing.CompletedTensorProduct.inr R _ S).commutes r

private noncomputable def ofCompletedTensorGauss :
    IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1) →ₐ[R]
      AdicRing.CompletedTensorProduct R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S :=
  { restrictedLiftLinear (AdicRing.CompletedTensorProduct.continuous_inr R
        (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S)
      (fun i ↦ AdicRing.CompletedTensorProduct.inl R _ S
        ⟨X i, IsRestricted.mem_subring.mpr (isRestricted_X _ i)⟩) with
    commutes' := ofCompletedTensorGauss_commutes }

omit [ContinuousSMul R S] in
@[simp]
private theorem coe_ofCompletedTensorGauss :
    ⇑(ofCompletedTensorGauss (k := k) (R := R) (S := S)) =
      ⇑(restrictedLiftLinear (AdicRing.CompletedTensorProduct.continuous_inr R
          (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S)
        (fun i ↦ AdicRing.CompletedTensorProduct.inl R _ S
          ⟨X i, IsRestricted.mem_subring.mpr (isRestricted_X _ i)⟩)) := rfl

private theorem continuous_toCompletedTensorGauss :
    Continuous (toCompletedTensorGauss (k := k) (R := R) (S := S)) :=
  AdicRing.CompletedTensorProduct.continuous_lift ..

omit [ContinuousSMul R S] in
private theorem continuous_ofCompletedTensorGauss :
    Continuous (ofCompletedTensorGauss (k := k) (R := R) (S := S)) :=
  continuous_restrictedLiftLinear ..

private theorem toCompletedTensorGauss_comp_ofCompletedTensorGauss :
    (toCompletedTensorGauss (k := k) (R := R) (S := S)).comp
      (ofCompletedTensorGauss (k := k) (R := R) (S := S)) = AlgHom.id R _ := by
  refine AlgHom.toRingHom_injective <| isRestricted_subring_ringHom_ext_of_continuous
    (continuous_toCompletedTensorGauss.comp continuous_ofCompletedTensorGauss) continuous_id
    (fun _ ↦ by simp [toCompletedTensorGauss]) (fun i ↦ ?_)
  simp only [AlgHom.comp_toRingHom, RingHom.comp_apply, RingHom.coe_coe,
    AlgHom.id_toRingHom, RingHom.id_apply, coe_ofCompletedTensorGauss]
  have hX := restrictedLiftLinear_X (AdicRing.CompletedTensorProduct.continuous_inr R
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S)
    (fun j ↦ AdicRing.CompletedTensorProduct.inl R _ S
      ⟨X j, IsRestricted.mem_subring.mpr (isRestricted_X _ j)⟩) i
  rw [hX, toCompletedTensorGauss, AdicRing.CompletedTensorProduct.lift_inl]
  exact Subtype.ext (by simp [coeffMapAlgHom])

private theorem ofCompletedTensorGauss_comp_toCompletedTensorGauss :
    (ofCompletedTensorGauss (k := k) (R := R) (S := S)).comp
      (toCompletedTensorGauss (k := k) (R := R) (S := S)) = AlgHom.id R _ := by
  refine AdicRing.CompletedTensorProduct.algHom_ext
    (continuous_ofCompletedTensorGauss.comp continuous_toCompletedTensorGauss) continuous_id
    (AlgHom.toRingHom_injective ?_) (AlgHom.ext fun _ ↦ by simp [toCompletedTensorGauss])
  refine isRestricted_subring_ringHom_ext_of_continuous
    ((continuous_ofCompletedTensorGauss.comp continuous_toCompletedTensorGauss).comp
      (AdicRing.CompletedTensorProduct.continuous_inl ..))
    (AdicRing.CompletedTensorProduct.continuous_inl ..)
    (fun _ ↦ by
      simp only [AlgHom.comp_toRingHom, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes])
    (fun i ↦ ?_)
  simp only [AlgHom.comp_toRingHom, RingHom.comp_apply, RingHom.coe_coe,
    toCompletedTensorGauss, AdicRing.CompletedTensorProduct.lift_inl, coe_ofCompletedTensorGauss]
  have hX : coeffMapAlgHom (k := k) (R := R) (S := S) ⟨X i, isRestricted_X _ i⟩ =
      ⟨X i, isRestricted_X _ i⟩ := Subtype.ext (by simp [coeffMapAlgHom])
  rw [hX]
  exact restrictedLiftLinear_X _ _ i

/-- **Completed-tensor base change on Gauss-normed restricted series.** Over adic ultrametric normed
commutative rings `R` and `S` connected by a continuous `R`-algebra structure, the completed tensor
product `R⟨X₁, …, Xₖ⟩ ⊗̂_R S` is isomorphic as an `R`-algebra to `S⟨X₁, …, Xₖ⟩`. -/
noncomputable def completedTensorRestrictedGaussEquiv :
    AdicRing.CompletedTensorProduct R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S ≃ₐ[R]
      IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1) :=
  AlgEquiv.ofAlgHom (toCompletedTensorGauss (k := k) (R := R) (S := S))
    (ofCompletedTensorGauss (k := k) (R := R) (S := S))
    toCompletedTensorGauss_comp_ofCompletedTensorGauss
    ofCompletedTensorGauss_comp_toCompletedTensorGauss

/-- `completedTensorRestrictedGaussEquiv` is a homeomorphism of topological `R`-algebras. -/
theorem isHomeomorph_completedTensorRestrictedGaussEquiv :
    IsHomeomorph (completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)) :=
  (completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_toCompletedTensorGauss, continuous_ofCompletedTensorGauss⟩

/-- Unconditionally on `R⟨X₁, …, Xₖ⟩`, `completedTensorRestrictedGaussEquiv` transports `g` along
`weightedMap (continuous_algebraMap R S)` across `restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem completedTensorRestrictedGaussEquiv_inl
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)
        (AdicRing.CompletedTensorProduct.inl R _ S g) =
      restrictedMvPowerSeriesGaussEquiv
        (weightedMap (continuous_algebraMap R S) isWeightFamily_one_weight
          isWeightFamily_one_weight (by simp) (restrictedMvPowerSeriesGaussEquiv.symm g)) := by
  simp [completedTensorRestrictedGaussEquiv, toCompletedTensorGauss, coeffMapAlgHom]

/-- As a formal power series, `completedTensorRestrictedGaussEquiv` acts on `inl g` by mapping
coefficients along `algebraMap R S` (without requiring a Lipschitz norm bound). -/
theorem coe_completedTensorRestrictedGaussEquiv_inl
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    (completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)
        (AdicRing.CompletedTensorProduct.inl R _ S g) : MvPowerSeries (Fin k) S) =
      MvPowerSeries.map (algebraMap R S) g := by simp

/-- When `algebraMap R S` satisfies a norm bound, `completedTensorRestrictedGaussEquiv` acts on
`inl g` as `restrictedMap (algebraMap R S)`. -/
theorem completedTensorRestrictedGaussEquiv_inl_of_norm_le (hφ : ∀ r, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)
        (AdicRing.CompletedTensorProduct.inl R _ S g) =
      restrictedMap (algebraMap R S) hφ g :=
  Subtype.ext <| (coe_completedTensorRestrictedGaussEquiv_inl g).trans (coe_restrictedMap ..).symm

/-- On `S`, `completedTensorRestrictedGaussEquiv` is the constant-series embedding `algebraMap`. -/
@[simp]
theorem completedTensorRestrictedGaussEquiv_inr (s : S) :
    completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)
        (AdicRing.CompletedTensorProduct.inr R
          (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S s) =
      algebraMap S (IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1)) s := by
  simp [completedTensorRestrictedGaussEquiv, toCompletedTensorGauss]

/-- The inverse of `completedTensorRestrictedGaussEquiv` sends a constant series `s` to `inr s`. -/
@[simp]
theorem completedTensorRestrictedGaussEquiv_symm_algebraMap (s : S) :
    (completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)).symm
        (algebraMap S (IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1)) s) =
      AdicRing.CompletedTensorProduct.inr R
        (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S s := by
  rw [AlgEquiv.symm_apply_eq, completedTensorRestrictedGaussEquiv_inr]

/-- The inverse of `completedTensorRestrictedGaussEquiv` sends each coordinate `Xᵢ` to `inl Xᵢ`. -/
@[simp]
theorem completedTensorRestrictedGaussEquiv_symm_X (i : Fin k) :
    (completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)).symm
        ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ =
      AdicRing.CompletedTensorProduct.inl R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) S
        ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ := by
  rw [AlgEquiv.symm_apply_eq]; exact Subtype.ext (by simp)

end CompletedTensor

end TauCeti.MvPowerSeries

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- The order-`m` polynomial quotient equivalences on Huber and Gauss-normed restricted series
commute with the Gauss comparison. -/
theorem quotientPowRestrictedEquiv_eq_quotientPowIsRestrictedEquiv
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesGaussEquiv f)) := by
  simp [restrictedReduction_eq_restrictedIdealReduction]

/-- Over a complete `I`-adic normed ring, the order-`m` polynomial quotient equivalence on the
completed Huber carrier agrees with that on Gauss-normed restricted series. -/
theorem quotientPowRestrictedCompletionEquiv_eq_quotientPowIsRestrictedEquiv [CompleteSpace R]
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k R) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ x) =
      quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesCompletionGaussEquiv x)) := by
  simp [restrictedCompletionReduction_eq_restrictedIdealReduction]

end TauCeti.Huber
