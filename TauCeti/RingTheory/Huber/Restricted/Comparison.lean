/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.Basic
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Reduction
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

/-!
# Coefficient maps, evaluation, and adic reductions under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers:

1. **Cross-carrier comparisons (`TauCeti.Huber`)**, before and after completion (completeness of the
   source ring is needed only on the completed Huber side): continuous and bounded coefficient maps,
   norm-bounded and power-bounded evaluations, open-ideal reductions, and `(I·R[X])`-adic
   inverse-limit presentations.
2. **Gauss-normed carrier (`TauCeti.MvPowerSeries`)**: over an `I`-adic normed ring (`I.FG`),
   `R⟨X₁, …, Xₖ⟩` has the `(I·R⟨X⟩)`-adic topology with quotients `(R ⧸ Iᵐ)[X]` (`m : ℕ`); when `R`
   is complete, `R⟨X⟩ ≃ₐ[R] AdicCompletion (I.map C) R[X]` (homeomorphic) and `R⟨X⟩` is noetherian
   if `R` is; over an `IsAdicRing`, `R⟨X⟩` is an `IsAdicRing` (completed-tensor base change is in
   `TauCeti.RingTheory.AdicRing.CompletedTensorProduct.GaussNorm`).

## Main definitions and results

* `TauCeti.MvPowerSeries.quotientPowIsRestrictedEquivMvPolynomialQuotient`,
  `TauCeti.MvPowerSeries.isRestrictedSubringEquivAdicCompletion`, and
  `TauCeti.MvPowerSeries.isAdicRing_isRestricted_subring`.
* `restrictedMvPowerSeriesGaussEquiv_weightedMap_of_continuous`,
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous`,
  `weightedEvalHom_eq_restrictedLift`,
  `norm_weightedEvalHom_sub_le`,
  `restrictedReduction_eq_isRestrictedSubringReduction`,
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

local notation:max "WSub" k:max R:max =>
  weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight
local notation:max "WComp" k:max R:max => restrictedMvPowerSeriesCompletion k R

section Reduction

/-- Huber and normed open-ideal polynomial reductions agree across the Gauss comparison. -/
theorem restrictedReduction_eq_isRestrictedSubringReduction {J : Ideal R} (hJ : IsOpen (J : Set R))
    (f : WSub k R) : Ideal.restrictedReduction J hJ f =
      J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesGaussEquiv f) := by ext ν; simp

/-- Over a complete ring, completed Huber reduction agrees with `isRestrictedSubringReduction`. -/
theorem restrictedCompletionReduction_eq_isRestrictedSubringReduction [CompleteSpace R]
    {J : Ideal R} (hJ : IsOpen (J : Set R)) (x : WComp k R) :
    Ideal.restrictedCompletionReduction J hJ x =
      J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  conv_lhs => rw [← restrictedMvPowerSeriesCompletionGaussEquiv.symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
    Ideal.restrictedCompletionReduction_coe, restrictedReduction_eq_isRestrictedSubringReduction hJ,
    RingEquiv.apply_symm_apply]

end Reduction

section PowerBoundedEvaluation

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

end PowerBoundedEvaluation

end TauCeti.Huber

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber Topology

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {C : ℝ}

local notation:max "Tate" k':max R':max => IsRestricted.subring (R := R') (fun _ : Fin k' ↦ 1)

/-- Reducing `restrictedLift` modulo an open ideal `J` agrees with polynomial evaluation of
`isRestrictedSubringReduction` modulo `I`. -/
theorem mk_restrictedLift_eq_eval₂_isRestrictedSubringReduction {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    {I : Ideal R} {J : Ideal B} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap ψ) (g : Tate k R) :
    Ideal.Quotient.mk J (restrictedLift hψ hb g) =
      (I.isRestrictedSubringReduction hI g).eval₂ (Ideal.quotientMap J ψ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  rw [restrictedLift_apply,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction hψ.continuousAt _ hI hJ hIJ,
    restrictedReduction_eq_isRestrictedSubringReduction hI, RingEquiv.apply_symm_apply]

section Adic

variable {I : Ideal R}

private theorem map_gaussEquiv_symm_ideal_pow (I : Ideal R) (m : ℕ) :
    I.map (weightedC _ isWeightFamily_one_weight) ^ m =
      (I.map (algebraMap R (Tate k R)) ^ m).map
        (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm := by
  rw [Ideal.map_pow,
    ← Ideal.map_coe (f := (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm),
    Ideal.map_map]
  refine congrArg (· ^ m) (congrArg (Ideal.map · I) (RingHom.ext fun r ↦ ?_))
  apply (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).injective
  simp

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
  have hmap := map_gaussEquiv_symm_ideal_pow (k := k) I 1
  simp only [pow_one] at hmap
  rw [← Ideal.apply_mem_of_equiv_iff
      (f := (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm),
    ← hmap, mem_map_weightedC_iff_of_isAdic hI hfg]
  simp

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo `I ^ m` (`I` adic and finitely generated) has kernel
`(I · R⟨X⟩) ^ m`. -/
theorem ker_isRestrictedSubringReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker ((I ^ m).isRestrictedSubringReduction (σ := Fin k) (hI.isOpen_pow m)) =
      I.map (algebraMap R (Tate k R)) ^ m := by
  ext g
  rw [RingHom.mem_ker, ← Ideal.apply_mem_of_equiv_iff
      (f := (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm),
    ← map_gaussEquiv_symm_ideal_pow I m, ← ker_restrictedReduction_pow hI hfg m,
    RingHom.mem_ker, restrictedReduction_eq_isRestrictedSubringReduction]
  simp

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo a finitely generated ideal of definition `I` has kernel
`I · R⟨X⟩`. -/
theorem ker_isRestrictedSubringReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.isRestrictedSubringReduction (σ := Fin k) (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (algebraMap R (Tate k R)) := by
  ext g
  rw [RingHom.mem_ker, Ideal.isRestrictedSubringReduction_eq_zero_iff,
    mem_map_algebraMap_isRestricted_subring_iff_of_isAdic hI hfg]

/-- **Infinitesimal thickening on Gauss-normed restricted series** modulo `(I · R⟨X⟩) ^ m`,
transported from `TauCeti.Huber.quotientPowRestrictedEquivMvPolynomialQuotient` along
`TauCeti.Huber.restrictedMvPowerSeriesGaussAlgEquiv`. -/
noncomputable def quotientPowIsRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (Tate k R ⧸ I.map (algebraMap R (Tate k R)) ^ m) ≃ₐ[R] MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).symm
      ((map_gaussEquiv_symm_ideal_pow I m).trans <| congrArg (Ideal.map · _) <|
        congrArg RingEquiv.symm <| RingEquiv.ext fun x ↦
          (congrFun coe_restrictedMvPowerSeriesGaussAlgEquiv x).symm)).trans
    (quotientPowRestrictedEquivMvPolynomialQuotient hI hfg m)

/-- `quotientPowIsRestrictedEquivMvPolynomialQuotient` computes reduction modulo `I ^ m`. -/
@[simp] theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (g : Tate k R) :
    quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ g) =
      (I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) g := by
  rw [quotientPowIsRestrictedEquivMvPolynomialQuotient, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlg_mk, quotientPowRestrictedEquivMvPolynomialQuotient_mk,
    restrictedReduction_eq_isRestrictedSubringReduction, ← coe_restrictedMvPowerSeriesGaussAlgEquiv]
  simp

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
          ((I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) g)) := by
  simp only [isRestrictedSubringEquivAdicCompletion, AlgEquiv.trans_apply,
    evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg m,
    coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm,
    restrictedCompletionReduction_eq_isRestrictedSubringReduction, RingEquiv.apply_symm_apply]

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

local notation:max "WComp" k:max R:max => restrictedMvPowerSeriesCompletion k R

/-- `isRestrictedSubringEquivAdicCompletion` commutes with the completed Gauss comparison. -/
@[simp]
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

section LinearTopologyEvaluation

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T] [CompleteSpace T]
  [T2Space T]

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
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) _ f

/-- **Completed linearly topologised evaluation agrees with
`restrictedLiftAlgHomOfIsLinearTopology`** across the completed Gauss comparison. -/
theorem weightedEvalCompletionAlgHomOfIsLinearTopology_eq_restrictedLiftAlgHomOfIsLinearTopology
    [CompleteSpace R] [IsLinearTopology T T] [Algebra R T] (hR : Continuous (algebraMap R T))
    (b : Fin k → T)
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
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) _ x

end LinearTopologyEvaluation

end TauCeti.Huber

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

section Adic

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

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

end CompleteAdic

/-- Over a noetherian adic ultrametric normed ring, `R⟨X₁, …, Xₖ⟩` is noetherian (and hence
strongly noetherian via `IsStronglyNoetherian.of_isAdicRing`). -/
instance isNoetherianRing_isRestricted_subring_of_isAdicRing (k : ℕ) [IsAdicRing R]
    [IsNoetherianRing R] :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  isNoetherianRing_isRestricted_subring_of_isAdic (k := k) (IsAdicRing.ideal_spec R).2.1

end Adic

end TauCeti.MvPowerSeries
