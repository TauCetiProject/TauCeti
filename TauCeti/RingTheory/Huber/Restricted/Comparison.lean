/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct.Restricted
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
This file proves that their coefficient maps, evaluations (both norm-bounded and into linearly
topologized targets), open-ideal polynomial reductions, adic topologies, infinitesimal quotient
presentations `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]`, inverse-limit adic completions, and
completed-tensor base changes agree, both before and after completion.

Completeness of the source coefficients is needed only for comparisons involving the source
completion. Over a complete noetherian adic normed ring `R`, the normed restricted-series ring
`R⟨X₁, …, Xₖ⟩` is noetherian and coincides with its `(I · R⟨X⟩)`-adic completion.

## Main definitions

* `TauCeti.Huber.quotientIsRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientPowIsRestrictedEquivMvPolynomialQuotient`: the `R`-algebra equivalences
  `R⟨X⟩ ⧸ (I · R⟨X⟩) ≃ₐ[R] (R ⧸ I)[X]` and `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` (`m ≠ 0`) on
  the Gauss-normed carrier.
* `TauCeti.Huber.isRestrictedSubringEquivAdicCompletion`: over a complete `I`-adic normed ring `R`
  with `I` finitely generated, the ring isomorphism from `R⟨X⟩` to its algebraic `(I · R⟨X⟩)`-adic
  completion.
* `TauCeti.Huber.completedTensorRestrictedGaussEquiv`: over complete adic normed rings, the base
  change isomorphism `(R⟨X⟩ ⊗̂_R S) ≃+* S⟨X⟩` onto the Gauss-normed restricted-series carrier.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `weightedEvalHom_eq_restrictedEval₂OfBound`,
  `weightedEvalHomCompletion_eq_restrictedEval₂OfBound`,
  `weightedEvalHom_eq_restrictedLiftLinear`, and
  `weightedEvalHomCompletion_eq_restrictedLiftLinear`: topological evaluation agrees with normed
  evaluation and with linear-topology evaluation.
* `restrictedReduction_eq_restrictedIdealReduction` and
  `restrictedCompletionReduction_eq_restrictedIdealReduction`: Huber open-ideal polynomial reduction
  agrees with normed open-ideal reduction across the Gauss comparison.
* `isAdic_map_algebraMap_isRestricted_subring` and
  `isNoetherianRing_isRestricted_subring_of_isAdic`: the Gauss-norm topology on `R⟨X⟩` over an
  `I`-adic normed ring (`I` finitely generated) is `(I · R⟨X⟩)`-adic, and `R⟨X⟩` is noetherian
  when `R` is complete and noetherian.
* `completedTensorRestrictedGaussEquiv_inl` and `completedTensorRestrictedGaussEquiv_inr`:
  completed-tensor base change acts on `R⟨X⟩` as `restrictedMap` and on `S` as `algebraMap`.

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
  let g := restrictedMvPowerSeriesCompletionGaussEquiv x
  have hx : x = (restrictedMvPowerSeriesGaussEquiv.symm g :
      restrictedMvPowerSeriesCompletion k R) := by
    rw [← restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply, RingEquiv.symm_apply_apply]
  conv_lhs => rw [hx]
  rw [Ideal.restrictedCompletionReduction_coe,
    restrictedReduction_eq_restrictedIdealReduction hJ, RingEquiv.apply_symm_apply]

end Reduction

section LinearTopology

/-- Topological evaluation into a complete Hausdorff linearly topologized ring agrees with
`restrictedLiftLinear` across the Gauss comparison. -/
theorem weightedEvalHom_eq_restrictedLiftLinear {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CompleteSpace B] [T2Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    (hb : let _ := IsLinearTopology.nonarchimedeanRing B;
      IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (let _ := IsLinearTopology.nonarchimedeanRing B;
      weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb f) =
      restrictedLiftLinear hψ b (restrictedMvPowerSeriesGaussEquiv f) := by
  have := IsLinearTopology.nonarchimedeanRing B
  have hcomp :
      weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb =
        (restrictedLiftLinear hψ b).comp
          (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom :=
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (continuous_weightedEvalHom _ hψ.continuousAt hb)
      ((continuous_restrictedLiftLinear hψ b).comp continuous_restrictedMvPowerSeriesGaussEquiv)
      (fun r ↦ by simp)
      (fun i ↦ by simp)
  exact congr($hcomp f)

/-- Completed topological evaluation into a complete Hausdorff linearly topologized ring agrees
with `restrictedLiftLinear` across the completed Gauss comparison. -/
theorem weightedEvalHomCompletion_eq_restrictedLiftLinear [CompleteSpace R]
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) (b : Fin k → B)
    (hb : let _ := IsLinearTopology.nonarchimedeanRing B;
      IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    (let _ := IsLinearTopology.nonarchimedeanRing B;
      weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt hb x) =
      restrictedLiftLinear hψ b (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  have := IsLinearTopology.nonarchimedeanRing B
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ hψ.continuousAt hb)
    ((continuous_restrictedLiftLinear hψ b).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe]
  exact weightedEvalHom_eq_restrictedLiftLinear hψ b hb f

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
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hb' : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mpr hb
  have heq : restrictedLift hψ hb g =
      weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb' (e.symm g) := by
    have hcomp := restrictedLift_unique (b := b)
      (ψ := (weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb').comp e.symm.toRingHom)
      hψ hb
      ((continuous_weightedEvalHom _ hψ.continuousAt hb').comp
        continuous_restrictedMvPowerSeriesGaussEquiv_symm)
      (fun r ↦ by
        have hr : e.symm (algebraMap R _ r) = weightedC _ isWeightFamily_one_weight r :=
          e.injective (by simp [e])
        rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr,
          weightedEvalHom_weightedC])
      (fun i ↦ by
        have hi : e.symm ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ =
            weightedX _ isWeightFamily_one_weight i :=
          e.injective (by simp [e])
        rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hi,
          weightedEvalHom_weightedX])
    exact congr($hcomp g).symm
  rw [heq, mk_weightedEvalHom_eq_eval₂_restrictedReduction hψ.continuousAt hb' hI hJ hIJ,
    restrictedReduction_eq_restrictedIdealReduction hI, e.apply_symm_apply]

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
    fun i ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  have hcomp := restrictedLift_unique (b := b) hψ hb (continuous_restrictedLiftLinear hψ b)
    (restrictedLiftLinear_algebraMap hψ b) (restrictedLiftLinear_X hψ b)
  rw [congr($hcomp g)]
  exact mk_restrictedLift_eq_eval₂_restrictedIdealReduction hψ hb hI hJ hIJ g

end LinearTopology

section Adic

variable {I : Ideal R}

/-- **Adic topology of Gauss-normed restricted series.** If `R` has the `I`-adic topology for a
finitely generated ideal `I`, then `R⟨X₁, …, Xₖ⟩` under the Gauss norm has the `(I · R⟨X⟩)`-adic
topology. -/
theorem isAdic_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  let hHomeo : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ≃ₜ
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight :=
    { toEquiv := e.symm.toEquiv
      continuous_toFun := continuous_restrictedMvPowerSeriesGaussEquiv_symm
      continuous_invFun := continuous_restrictedMvPowerSeriesGaussEquiv }
  have hAdic := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap
    e.symm hHomeo.isInducing
  have heq : (I.map (algebraMap R
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
        isWeightFamily_one_weight))).comap e.symm =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_map]
    refine congrArg (Ideal.map · I) (RingHom.ext fun r ↦ ?_)
    simp [e, algebraMap_weightedRestrictedSubring]
  exact heq ▸ hAdic

/-- Membership in the extension of a finitely generated ideal of definition `I` to `R⟨X₁, …, Xₖ⟩`
is coefficientwise. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    g ∈ I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ↔
      ∀ ν, coeff ν (g : MvPowerSeries (Fin k) R) ∈ I := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hmap : I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) =
      (I.map (weightedC _ isWeightFamily_one_weight)).map e.toRingHom := by
    rw [Ideal.map_map]
    exact congrArg (Ideal.map · I)
      (RingHom.ext fun r ↦ (restrictedMvPowerSeriesGaussEquiv_weightedC r).symm)
  rw [hmap]
  have hmem : g ∈ (I.map (weightedC _ isWeightFamily_one_weight)).map e.toRingHom ↔
      e.symm g ∈ I.map (weightedC _ isWeightFamily_one_weight) :=
    (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).trans
      ⟨fun ⟨f, hf, hfg'⟩ ↦ by simpa [← hfg'] using hf,
       fun h ↦ ⟨e.symm g, h, e.apply_symm_apply g⟩⟩
  rw [hmem, mem_map_weightedC_iff_of_isAdic hI hfg]
  simp [e]

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo `I ^ m` (`m ≠ 0`) for a finitely generated ideal of
definition `I` has kernel `(I · R⟨X⟩) ^ m`. -/
theorem ker_restrictedIdealReduction_pow (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    RingHom.ker (restrictedIdealReduction (σ := Fin k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m := by
  rw [← Ideal.map_pow]
  ext g
  rw [RingHom.mem_ker, restrictedIdealReduction_eq_zero_iff (hI.isOpen_pow m),
    mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI.pow hm) hfg.pow]

/-- Reduction of `R⟨X₁, …, Xₖ⟩` modulo a finitely generated ideal of definition `I` has kernel
`I · R⟨X⟩`. -/
theorem ker_restrictedIdealReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedIdealReduction (σ := Fin k) I
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  have h1 : ∀ (J : Ideal R) (_ : J = I) (hJ : IsOpen (J : Set R)) (hI' : IsOpen (I : Set R)),
      RingHom.ker (restrictedIdealReduction (σ := Fin k) I hI') =
        RingHom.ker (restrictedIdealReduction (σ := Fin k) J hJ) := by
    rintro _ rfl _ _; rfl
  rw [h1 (I ^ 1) (pow_one I) (hI.isOpen_pow 1),
    ker_restrictedIdealReduction_pow (k := k) hI hfg one_ne_zero, pow_one]

/-- **Infinitesimal thickening on Gauss-normed restricted series**: for `m ≠ 0`, reducing modulo
`(I · R⟨X⟩) ^ m` gives `(R ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientPowIsRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) := by
  let hker := (ker_restrictedIdealReduction_pow (k := k) hI hfg hm).symm
  let e := (Ideal.quotEquivOfEq hker).trans
    ((restrictedIdealReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (restrictedIdealReduction_surjective (I ^ m) (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) =
      restrictedIdealReduction (I ^ m) (hI.isOpen_pow m) (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp

/-- On a represented series, `quotientPowIsRestrictedEquivMvPolynomialQuotient` computes
`restrictedIdealReduction` modulo `I ^ m`. -/
@[simp]
theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ g) =
      restrictedIdealReduction (I ^ m) (hI.isOpen_pow m) g := by
  simp [quotientPowIsRestrictedEquivMvPolynomialQuotient]

/-- Infinitesimal reduction modulo `I · R⟨X⟩` on Gauss-normed restricted series. -/
noncomputable def quotientIsRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) := by
  let hker := (ker_restrictedIdealReduction (k := k) hI hfg).symm
  let hopen : IsOpen (I : Set R) := by simpa only [pow_one] using hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq hker).trans
    ((restrictedIdealReduction I hopen).quotientKerEquivOfSurjective
      (restrictedIdealReduction_surjective I hopen))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) = restrictedIdealReduction I hopen (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp

/-- On a represented series, `quotientIsRestrictedEquivMvPolynomialQuotient` computes
`restrictedIdealReduction` modulo `I`. -/
@[simp]
theorem quotientIsRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ g) =
      restrictedIdealReduction I (by simpa only [pow_one] using hI.isOpen_pow 1) g := by
  simp [quotientIsRestrictedEquivMvPolynomialQuotient]

/-- The order-`m` polynomial quotient equivalences on Huber and Gauss-normed restricted series
commute with the Gauss comparison. -/
theorem quotientPowRestrictedEquiv_eq_quotientPowIsRestrictedEquiv
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesGaussEquiv f)) := by
  simp [restrictedReduction_eq_restrictedIdealReduction]

section CompleteAdic

variable [CompleteSpace R]

/-- Over a complete `I`-adic normed ring, the order-`m` polynomial quotient equivalence on the
completed Huber carrier agrees with that on Gauss-normed restricted series. -/
theorem quotientPowRestrictedCompletionEquiv_eq_quotientPowIsRestrictedEquiv
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k R) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ x) =
      quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesCompletionGaussEquiv x)) := by
  simp [restrictedCompletionReduction_eq_restrictedIdealReduction]

/-- **Inverse-limit presentation of `R⟨X₁, …, Xₖ⟩` over a complete adic normed ring.** Because
`R⟨X₁, …, Xₖ⟩` is complete and Hausdorff and carries the `(I · R⟨X⟩)`-adic topology, it is
canonically isomorphic to its algebraic `(I · R⟨X⟩)`-adic completion. -/
noncomputable def isRestrictedSubringEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ≃+*
      AdicCompletion
        (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))))
        (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (UniformSpace.Completion.completeRingEquivSelf _).symm.trans
    ((isAdic_map_algebraMap_isRestricted_subring (k := k) hI hfg).completionEquivAdicCompletion
      (hfg.map _))

/-- `isRestrictedSubringEquivAdicCompletion` is the canonical `algebraMap` into `AdicCompletion`. -/
@[simp]
theorem isRestrictedSubringEquivAdicCompletion_apply (hI : IsAdic I) (hfg : I.FG)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    isRestrictedSubringEquivAdicCompletion hI hfg g =
      algebraMap (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) _ g := by
  simp [isRestrictedSubringEquivAdicCompletion,
    UniformSpace.Completion.completeRingEquivSelf_symm_apply]

/-- Under `isRestrictedSubringEquivAdicCompletion`, the `m`-th inverse-limit projection (`m ≠ 0`)
computes polynomial reduction modulo `I ^ m`. -/
theorem quotientPowIsRestrictedEquiv_evalₐ_isRestrictedSubringEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg hm
        (AdicCompletion.evalₐ _ m (isRestrictedSubringEquivAdicCompletion hI hfg g)) =
      restrictedIdealReduction (I ^ m) (hI.isOpen_pow m) g := by
  simp [isRestrictedSubringEquivAdicCompletion_apply, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of]

/-- **Noetherianity of Gauss-normed restricted power series over a complete adic noetherian ring.**
Transported from `isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic` along the completed
Gauss isomorphism. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [IsNoetherianRing R] (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  isNoetherianRing_of_ringEquiv _ (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

end CompleteAdic

end Adic

section CompletedTensor

variable [CompleteSpace S] [IsAdicRing R] [IsAdicRing S] [Algebra R S] [ContinuousSMul R S]

/-- **Completed-tensor base change onto the Gauss-normed carrier.** Over adic normed rings `R` and
`S` with `S` complete, `R⟨X₁, …, Xₖ⟩ ⊗̂_R S` is isomorphic to the Gauss-normed restricted-series
ring `S⟨X₁, …, Xₖ⟩`. -/
noncomputable def completedTensorRestrictedGaussEquiv :
    AdicRing.CompletedTensorProduct R (restrictedMvPowerSeriesCompletion k R) S ≃+*
      IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1) :=
  (AdicRing.CompletedTensorProduct.restrictedEquiv k R S).trans
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := S))

/-- On `R⟨X₁, …, Xₖ⟩`, `completedTensorRestrictedGaussEquiv` applies the normed coefficient map
`restrictedMap (algebraMap R S)` whenever `R` is complete and `algebraMap R S` is norm-bounded. -/
theorem completedTensorRestrictedGaussEquiv_inl [CompleteSpace R]
    (hφ : ∀ r, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (x : restrictedMvPowerSeriesCompletion k R) :
    completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)
        (AdicRing.CompletedTensorProduct.inl R _ S x) =
      restrictedMap (algebraMap R S) hφ (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  simp only [completedTensorRestrictedGaussEquiv, RingEquiv.trans_apply,
    AdicRing.CompletedTensorProduct.restrictedEquiv_inl]
  exact restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion
    (continuous_algebraMap R S) hφ x

/-- On `S`, `completedTensorRestrictedGaussEquiv` is the constant-series embedding `algebraMap`. -/
@[simp]
theorem completedTensorRestrictedGaussEquiv_inr (s : S) :
    completedTensorRestrictedGaussEquiv (k := k) (R := R) (S := S)
        (AdicRing.CompletedTensorProduct.inr R (restrictedMvPowerSeriesCompletion k R) S s) =
      algebraMap S (IsRestricted.subring (R := S) (fun _ : Fin k ↦ 1)) s := by
  simp only [completedTensorRestrictedGaussEquiv, RingEquiv.trans_apply,
    AdicRing.CompletedTensorProduct.restrictedEquiv_inr,
    ← coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv]
  exact (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := S)).commutes s

end CompletedTensor

end TauCeti.Huber
