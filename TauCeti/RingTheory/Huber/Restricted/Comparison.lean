/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Reduction
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty
import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology

/-!
# Coefficient maps, evaluation, and adic reductions under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers:

1. **Cross-carrier comparisons (`TauCeti.Huber`)**, before and after completion (completeness of the
   source ring is needed only on the completed Huber side): continuous and bounded coefficient maps,
   norm-bounded, power-bounded, and linear-target evaluations, open-ideal reductions, polynomial
   quotients modulo `(I·R⟨X⟩)ᵐ` (`m : ℕ`), and `(I·R[X])`-adic inverse-limit presentations.
2. **Gauss-normed carrier (`TauCeti.MvPowerSeries`)**: over an `I`-adic normed ring (`I.FG`),
   `R⟨X₁, …, Xₖ⟩` has the `(I·R⟨X⟩)`-adic topology with quotients `(R ⧸ Iᵐ)[X]` (`m : ℕ`); when `R`
   is complete, `R⟨X⟩ ≃ₐ[R] AdicCompletion (I.map C) R[X]` (homeomorphic) and `R⟨X⟩` is noetherian
   if `R` is; over an `IsAdicRing`, `R⟨X⟩` is an `IsAdicRing` (completed-tensor base change is in
   `TauCeti.RingTheory.AdicRing.CompletedTensorProduct.GaussNorm`).

## Main definitions and results

* `TauCeti.MvPowerSeries.quotientIsRestrictedEquivMvPolynomialQuotient`,
  `TauCeti.MvPowerSeries.quotientPowIsRestrictedEquivMvPolynomialQuotient`,
  `TauCeti.MvPowerSeries.isRestrictedSubringEquivAdicCompletion`, and
  `TauCeti.MvPowerSeries.isAdicRing_isRestricted_subring`.
* `restrictedMvPowerSeriesGaussEquiv_weightedMap_of_continuous`,
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous`,
  `weightedEvalHom_eq_restrictedLift`, `weightedEvalHom_eq_restrictedLiftLinear`,
  `restrictedReduction_eq_restrictedIdealReduction`,
  `quotientPowRestrictedEquiv_eq_quotientPowIsRestrictedEquiv`,
  `isAdic_map_algebraMap_isRestricted_subring`, and
  `isNoetherianRing_isRestricted_subring_of_isAdic`.

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

/-- The Gauss comparison commutes with continuous coefficient maps. -/
theorem restrictedMvPowerSeriesGaussEquiv_weightedMap_of_continuous (hφc : Continuous φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesGaussEquiv
        (weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      restrictedMapOfContinuous hφc (restrictedMvPowerSeriesGaussEquiv f) := by
  apply Subtype.ext
  simp only [coe_restrictedMvPowerSeriesGaussEquiv, coe_weightedMap, coe_restrictedMapOfContinuous]

/-- The Gauss comparison commutes with bounded coefficient maps. -/
theorem restrictedMvPowerSeriesGaussEquiv_weightedMap
    (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesGaussEquiv
        (weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [restrictedMvPowerSeriesGaussEquiv_weightedMap_of_continuous hφc,
    restrictedMapOfContinuous_eq_restrictedMap hφc hφ]

variable [CompleteSpace R] [CompleteSpace S]

/-- The completed Gauss comparison commutes with the continuous coefficient map on completions,
without requiring a Lipschitz norm bound on `φ`. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous
    (hφc : Continuous φ) (f : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f) =
      restrictedMapOfContinuous hφc (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_restrictedMvPowerSeriesCompletionGaussEquiv.comp
      (continuous_weightedMapCompletion _ _ _ _))
    ((continuous_restrictedMapOfContinuous hφc).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro g
  simp only [weightedMapCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesGaussEquiv_weightedMap_of_continuous hφc]

/-- The completed Gauss comparison commutes with the continuous coefficient map on completions.
Thus completing the topological coefficient map does not change the normed coefficient map. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion
    (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (f : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f) =
      restrictedMap φ hφ (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous hφc,
    restrictedMapOfContinuous_eq_restrictedMap hφc hφ]

/-- A bounded coefficient map on Huber completions has the same bound in the compared Gauss
norms. No norm on the topological completion is chosen independently of the comparison. -/
theorem norm_restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_le
    (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
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

local notation:max "WSub" k:max R:max =>
  weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight
local notation:max "WComp" k:max R:max => restrictedMvPowerSeriesCompletion k R

section Reduction

/-- Huber and normed open-ideal polynomial reductions agree across the Gauss comparison. -/
theorem restrictedReduction_eq_restrictedIdealReduction {J : Ideal R} (hJ : IsOpen (J : Set R))
    (f : WSub k R) : Ideal.restrictedReduction J hJ f =
      J.restrictedIdealReduction hJ (restrictedMvPowerSeriesGaussEquiv f) := by ext ν; simp

/-- Over a complete ring, completed Huber reduction agrees with `restrictedIdealReduction`. -/
theorem restrictedCompletionReduction_eq_restrictedIdealReduction [CompleteSpace R]
    {J : Ideal R} (hJ : IsOpen (J : Set R)) (x : WComp k R) :
    Ideal.restrictedCompletionReduction J hJ x =
      J.restrictedIdealReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  conv_lhs => rw [← restrictedMvPowerSeriesCompletionGaussEquiv.symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
    Ideal.restrictedCompletionReduction_coe, restrictedReduction_eq_restrictedIdealReduction hJ,
    RingEquiv.apply_symm_apply]

end Reduction

section PowerBoundedAndLinearEvaluation

/-- Topological evaluation agrees with `restrictedLift` across the Gauss comparison. -/
theorem weightedEvalHom_eq_restrictedLift {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b) (f : WSub k R) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb' f =
      restrictedLift hψ hb (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [restrictedLift_apply, RingEquiv.symm_apply_apply]

/-- Completed topological evaluation agrees with `restrictedLift` across the completed Gauss
comparison. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [CompleteSpace R] {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b) (x : WComp k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt hb' x =
      restrictedLift hψ hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ hψ.continuousAt hb') ((continuous_restrictedLift hψ hb)
      |>.comp continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedLift hψ hb hb']

/-- Topological evaluation into a linearly topologized ring agrees with `restrictedLiftLinear`. -/
theorem weightedEvalHom_eq_restrictedLiftLinear {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [IsLinearTopology B B]
    [CompleteSpace B] [T2Space B] {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    (hb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b) (f : WSub k R) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb f =
      restrictedLiftLinear hψ b (restrictedMvPowerSeriesGaussEquiv f) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have hbPB := (isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mp hb
  rw [restrictedLiftLinear_eq_restrictedLift hψ hbPB]
  exact weightedEvalHom_eq_restrictedLift hψ hbPB hb f

/-- Completed topological evaluation into a linearly topologized ring agrees with
`restrictedLiftLinear`. -/
theorem weightedEvalHomCompletion_eq_restrictedLiftLinear [CompleteSpace R] {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [IsLinearTopology B B]
    [CompleteSpace B] [T2Space B] {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    (hb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b) (x : WComp k R) :
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

local notation:max "Tate" k':max R':max => IsRestricted.subring (R := R') (fun _ : Fin k' ↦ 1)

/-- Reducing `restrictedLift` modulo an open ideal `J` agrees with polynomial evaluation of
`restrictedIdealReduction` modulo `I`. -/
theorem mk_restrictedLift_eq_eval₂_restrictedIdealReduction {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    {I : Ideal R} {J : Ideal B} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap ψ) (g : Tate k R) :
    Ideal.Quotient.mk J (restrictedLift hψ hb g) =
      (I.restrictedIdealReduction hI g).eval₂ (Ideal.quotientMap J ψ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  rw [restrictedLift_apply,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction hψ.continuousAt _ hI hJ hIJ,
    restrictedReduction_eq_restrictedIdealReduction hI, RingEquiv.apply_symm_apply]

/-- Reducing `restrictedLiftLinear` modulo an open ideal `J` agrees with polynomial evaluation of
`restrictedIdealReduction` modulo `I`. -/
theorem mk_restrictedLiftLinear_eq_eval₂_restrictedIdealReduction {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    {I : Ideal R} {J : Ideal B} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap ψ) (g : Tate k R) :
    Ideal.Quotient.mk J (restrictedLiftLinear hψ b g) =
      (I.restrictedIdealReduction hI g).eval₂ (Ideal.quotientMap J ψ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  have hb : ∀ i, IsPowerBounded (b i) :=
    fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  rw [restrictedLiftLinear_eq_restrictedLift hψ hb]
  exact mk_restrictedLift_eq_eval₂_restrictedIdealReduction hψ hb hI hJ hIJ g

section Adic

variable {I : Ideal R}

/-- **Adic topology of Gauss-normed restricted series** over an `I`-adic normed ring (`I.FG`). -/
theorem isAdic_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (Tate k R))) := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hInd : IsInducing e.symm :=
    (Homeomorph.mk e.symm.toEquiv continuous_restrictedMvPowerSeriesGaussEquiv_symm
      continuous_restrictedMvPowerSeriesGaussEquiv).isInducing
  convert (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap e.symm hInd
  rw [← Ideal.map_comap_of_equiv, Ideal.map_map]
  exact congrArg (Ideal.map · I)
    (RingHom.ext fun _ ↦ by simp [e, algebraMap_weightedRestrictedSubring])

/-- Membership in `I · R⟨X⟩` for a finitely generated ideal of definition `I` is coefficientwise. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (g : Tate k R) :
    g ∈ I.map (algebraMap R (Tate k R)) ↔ ∀ ν, coeff ν (g : MvPowerSeries (Fin k) R) ∈ I := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hmap : I.map (algebraMap R (Tate k R)) =
      (I.map (weightedC _ isWeightFamily_one_weight)).map e := by
    conv_rhs => rw [← Ideal.map_coe, Ideal.map_map]
    exact congrArg (Ideal.map · I)
      (RingHom.ext fun r ↦ (restrictedMvPowerSeriesGaussEquiv_weightedC r).symm)
  rw [hmap, ← Ideal.symm_apply_mem_of_equiv_iff, mem_map_weightedC_iff_of_isAdic hI hfg]; simp [e]

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo a finitely generated ideal of definition `I` has kernel
`I · R⟨X⟩`. -/
theorem ker_restrictedIdealReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.restrictedIdealReduction (σ := Fin k) (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (algebraMap R (Tate k R)) := by
  ext g; rw [RingHom.mem_ker, Ideal.restrictedIdealReduction_eq_zero_iff,
    mem_map_algebraMap_isRestricted_subring_iff_of_isAdic hI hfg]

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo `I ^ m` (`I` adic and finitely generated) has kernel
`(I · R⟨X⟩) ^ m`. -/
theorem ker_restrictedIdealReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker ((I ^ m).restrictedIdealReduction (σ := Fin k) (hI.isOpen_pow m)) =
      I.map (algebraMap R (Tate k R)) ^ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · ext g; simp [Ideal.restrictedIdealReduction_eq_zero_iff]
  · exact Ideal.map_pow (algebraMap R (Tate k R)) I m ▸
      ker_restrictedIdealReduction (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow

/-- Infinitesimal reduction modulo `I · R⟨X⟩` on Gauss-normed restricted series. -/
noncomputable def quotientIsRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (Tate k R ⧸ I.map (algebraMap R (Tate k R))) ≃ₐ[R] MvPolynomial (Fin k) (R ⧸ I) := by
  let hopen : IsOpen (I : Set R) := pow_one I ▸ hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq (ker_restrictedIdealReduction (k := k) hI hfg).symm).trans
    ((I.restrictedIdealReduction hopen).quotientKerEquivOfSurjective
      (I.restrictedIdealReduction_surjective hopen))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]; simp [e, -Ideal.Quotient.mk_algebraMap]

/-- On a represented series, `quotientIsRestrictedEquivMvPolynomialQuotient` computes reduction. -/
@[simp] theorem quotientIsRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (g : Tate k R) :
    quotientIsRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ g) =
      I.restrictedIdealReduction (pow_one I ▸ hI.isOpen_pow 1) g := by
  simp [quotientIsRestrictedEquivMvPolynomialQuotient]

/-- `quotientIsRestrictedEquivMvPolynomialQuotient.symm` lifts a reduced polynomial. -/
@[simp] theorem quotientIsRestrictedEquivMvPolynomialQuotient_symm_map_mk (hI : IsAdic I)
    (hfg : I.FG) (p : MvPolynomial (Fin k) R) :
    (quotientIsRestrictedEquivMvPolynomialQuotient hI hfg).symm
        (MvPolynomial.map (Ideal.Quotient.mk I) p) =
      Ideal.Quotient.mk _ (polynomialToRestricted (fun _ : Fin k ↦ 1) p) := by
  rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientIsRestrictedEquivMvPolynomialQuotient.symm` sends `X i` to the class of `X i`. -/
@[simp] theorem quotientIsRestrictedEquivMvPolynomialQuotient_symm_X (hI : IsAdic I) (hfg : I.FG)
    (i : Fin k) : (quotientIsRestrictedEquivMvPolynomialQuotient hI hfg).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ⟨X i, isRestricted_X _ i⟩ := by rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientIsRestrictedEquivMvPolynomialQuotient.symm` sends `C (mk I r)` to scalars. -/
@[simp] theorem quotientIsRestrictedEquivMvPolynomialQuotient_symm_C_mk (hI : IsAdic I)
    (hfg : I.FG) (r : R) : (quotientIsRestrictedEquivMvPolynomialQuotient (k := k) hI hfg).symm
      (MvPolynomial.C (Ideal.Quotient.mk I r)) = algebraMap R _ r := by
  rw [AlgEquiv.symm_apply_eq, ← Ideal.Quotient.mk_algebraMap]; simp [-Ideal.Quotient.mk_algebraMap]

/-- **Infinitesimal thickening on Gauss-normed restricted series** modulo `(I · R⟨X⟩) ^ m`. -/
noncomputable def quotientPowIsRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (Tate k R ⧸ I.map (algebraMap R (Tate k R)) ^ m) ≃ₐ[R] MvPolynomial (Fin k) (R ⧸ I ^ m) := by
  let e := (Ideal.quotEquivOfEq (ker_restrictedIdealReduction_pow (k := k) hI hfg m).symm).trans
    (((I ^ m).restrictedIdealReduction (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      ((I ^ m).restrictedIdealReduction_surjective (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]; simp [e, -Ideal.Quotient.mk_algebraMap]

/-- `quotientPowIsRestrictedEquivMvPolynomialQuotient` computes reduction modulo `I ^ m`. -/
@[simp] theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (g : Tate k R) :
    quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ g) =
      (I ^ m).restrictedIdealReduction (hI.isOpen_pow m) g := by
  simp [quotientPowIsRestrictedEquivMvPolynomialQuotient]

/-- `quotientPowIsRestrictedEquivMvPolynomialQuotient.symm` lifts `map (mk (I ^ m)) p`. -/
@[simp] theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_symm_map_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (p : MvPolynomial (Fin k) R) :
    (quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m).symm
        (MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p) =
      Ideal.Quotient.mk _ (polynomialToRestricted (fun _ : Fin k ↦ 1) p) := by
  rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientPowIsRestrictedEquivMvPolynomialQuotient.symm` sends `X i` to the class of `X i`. -/
@[simp] theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_symm_X (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) (i : Fin k) :
    (quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ⟨X i, isRestricted_X _ i⟩ := by rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientPowIsRestrictedEquivMvPolynomialQuotient.symm` sends `C (mk (I ^ m) r)` to scalars. -/
@[simp] theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_symm_C_mk (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) (r : R) :
    (quotientPowIsRestrictedEquivMvPolynomialQuotient (k := k) hI hfg m).symm
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ m) r)) = algebraMap R _ r := by
  rw [AlgEquiv.symm_apply_eq, ← Ideal.Quotient.mk_algebraMap]; simp [-Ideal.Quotient.mk_algebraMap]

section CompleteAdic

variable [CompleteSpace R]

/-- **Inverse-limit presentation of `R⟨X₁, …, Xₖ⟩` over a complete adic normed ring**
(EGA I, Ch. 0, §7.5.1). -/
noncomputable def isRestrictedSubringEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    Tate k R ≃ₐ[R] AdicCompletion (I.map (MvPolynomial.C (σ := Fin k))) (MvPolynomial (Fin k) R) :=
  (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).symm.trans
    (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg)

/-- On embedded polynomials, `isRestrictedSubringEquivAdicCompletion` is `algebraMap`. -/
@[simp] theorem isRestrictedSubringEquivAdicCompletion_polynomialToRestricted
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) R) :
    isRestrictedSubringEquivAdicCompletion hI hfg (polynomialToRestricted (fun _ : Fin k ↦ 1) p) =
      algebraMap (MvPolynomial (Fin k) R) _ p := by
  rw [isRestrictedSubringEquivAdicCompletion, AlgEquiv.trans_apply,
    coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm,
    restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
    ← restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom, RingEquiv.symm_apply_apply,
    restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom]

/-- `isRestrictedSubringEquivAdicCompletion` sends `X i` to `algebraMap _ _ (X i)`. -/
@[simp] theorem isRestrictedSubringEquivAdicCompletion_X (hI : IsAdic I) (hfg : I.FG) (i : Fin k) :
    isRestrictedSubringEquivAdicCompletion hI hfg ⟨X i, isRestricted_X _ i⟩ =
      algebraMap (MvPolynomial (Fin k) R) _ (MvPolynomial.X i) := by
  rw [← polynomialToRestricted_X, isRestrictedSubringEquivAdicCompletion_polynomialToRestricted]

/-- `isRestrictedSubringEquivAdicCompletion.symm` sends embedded polynomials to
`polynomialToRestricted`. -/
@[simp] theorem isRestrictedSubringEquivAdicCompletion_symm_algebraMap
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) R) :
    (isRestrictedSubringEquivAdicCompletion hI hfg).symm (algebraMap (MvPolynomial (Fin k) R) _ p) =
      polynomialToRestricted (fun _ : Fin k ↦ 1) p := by
  rw [AlgEquiv.symm_apply_eq, isRestrictedSubringEquivAdicCompletion_polynomialToRestricted]

/-- `isRestrictedSubringEquivAdicCompletion` is a homeomorphism for the adic topology on
`AdicCompletion`. -/
theorem isHomeomorph_isRestrictedSubringEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    @IsHomeomorph _ _ _ ((I.map (MvPolynomial.C (σ := Fin k))).map (algebraMap _ _)).adicTopology
      (isRestrictedSubringEquivAdicCompletion (k := k) hI hfg) := by
  let _ : TopologicalSpace (AdicCompletion
      (I.map (MvPolynomial.C (σ := Fin k))) (MvPolynomial (Fin k) R)) :=
    ((I.map (MvPolynomial.C (σ := Fin k))).map (algebraMap _ _)).adicTopology
  let e1 := (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).symm
  have h1 : IsHomeomorph e1 := e1.toEquiv.isHomeomorph_iff.mpr
    ⟨by simpa [e1] using continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm,
     by simpa [e1] using continuous_restrictedMvPowerSeriesCompletionGaussEquiv⟩
  exact (isHomeomorph_restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg).comp h1

/-- Under `isRestrictedSubringEquivAdicCompletion`, `evalₐ _ m` computes polynomial reduction modulo
`I ^ m`. -/
theorem evalₐ_isRestrictedSubringEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (g : Tate k R) :
    AdicCompletion.evalₐ _ m (isRestrictedSubringEquivAdicCompletion hI hfg g) =
      Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C (σ := Fin k)) I m)
        (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ m)
          ((I ^ m).restrictedIdealReduction (hI.isOpen_pow m) g)) := by
  simp only [isRestrictedSubringEquivAdicCompletion, AlgEquiv.trans_apply,
    evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg m,
    coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm,
    restrictedCompletionReduction_eq_restrictedIdealReduction, RingEquiv.apply_symm_apply]

/-- **Noetherianity of `R⟨X₁, …, Xₖ⟩`** over a complete noetherian `I`-adic normed ring `R`. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [IsNoetherianRing R] (hI : IsAdic I) :
    IsNoetherianRing (Tate k R) :=
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  isNoetherianRing_of_ringEquiv _ (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

end CompleteAdic

/-- Over an adic ultrametric normed commutative ring `R`, `R⟨X₁, …, Xₖ⟩` is an `IsAdicRing`. -/
instance isAdicRing_isRestricted_subring [IsAdicRing R] : IsAdicRing (Tate k R) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  have hJ := isAdic_map_algebraMap_isRestricted_subring (k := k) hI hfg
  exact ⟨_, hfg.map _, hJ, hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

end Adic

end TauCeti.MvPowerSeries

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

local notation:max "WSub" k:max R:max =>
  weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight
local notation:max "WComp" k:max R:max => restrictedMvPowerSeriesCompletion k R

/-- Unpowered polynomial quotient equivalences on Huber and Gauss series agree. -/
theorem quotientRestrictedEquiv_eq_quotientIsRestrictedEquiv (hI : IsAdic I) (hfg : I.FG)
    (f : WSub k R) : quotientRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      quotientIsRestrictedEquivMvPolynomialQuotient hI hfg
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesGaussEquiv f)) := by
  simp [restrictedReduction_eq_restrictedIdealReduction]

/-- Completed Huber and Gauss unpowered polynomial quotient equivalences agree. -/
theorem quotientRestrictedCompletionEquiv_eq_quotientIsRestrictedEquiv [CompleteSpace R]
    (hI : IsAdic I) (hfg : I.FG) (x : WComp k R) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) =
      quotientIsRestrictedEquivMvPolynomialQuotient hI hfg
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesCompletionGaussEquiv x)) := by
  simp [restrictedCompletionReduction_eq_restrictedIdealReduction]

/-- Order-`m` polynomial quotient equivalences on Huber and Gauss series agree. -/
theorem quotientPowRestrictedEquiv_eq_quotientPowIsRestrictedEquiv (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) (f : WSub k R) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesGaussEquiv f)) := by
  simp [restrictedReduction_eq_restrictedIdealReduction]

/-- Completed Huber and Gauss order-`m` polynomial quotient equivalences agree. -/
theorem quotientPowRestrictedCompletionEquiv_eq_quotientPowIsRestrictedEquiv [CompleteSpace R]
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (x : WComp k R) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesCompletionGaussEquiv x)) := by
  simp [restrictedCompletionReduction_eq_restrictedIdealReduction]

/-- `isRestrictedSubringEquivAdicCompletion` commutes with the completed Gauss comparison. -/
theorem isRestrictedSubringEquivAdicCompletion_restrictedMvPowerSeriesCompletionGaussEquiv
    [CompleteSpace R] (hI : IsAdic I) (hfg : I.FG) (x : WComp k R) :
    isRestrictedSubringEquivAdicCompletion hI hfg (restrictedMvPowerSeriesCompletionGaussEquiv x) =
      restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg x := by
  simp [isRestrictedSubringEquivAdicCompletion]

/-- Composing `restrictedMvPowerSeriesCompletionGaussAlgEquiv` with the normed adic-limit comparison
recovers `restrictedMvPowerSeriesCompletionEquivAdicCompletion`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussAlgEquiv_trans_isRestrictedSubringEquivAdicCompletion
    [CompleteSpace R] (hI : IsAdic I) (hfg : I.FG) :
    (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).trans
      (isRestrictedSubringEquivAdicCompletion hI hfg) =
      restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg :=
  AlgEquiv.ext fun x ↦ by simp [isRestrictedSubringEquivAdicCompletion]
end TauCeti.Huber
