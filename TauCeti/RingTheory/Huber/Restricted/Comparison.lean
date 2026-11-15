/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.Limit
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

/-!
# Adic structure, reductions, and evaluation under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber restricted-series carriers with the
Gauss-normed carrier `MvPowerSeries.IsRestricted.subring (fun _ ↦ 1)`. This file shows that
coefficient maps, evaluations (norm-bounded, power-bounded, and linear-topology), adic topologies,
adic completeness, noetherianity, polynomial reductions modulo open ideals, and inverse-limit cones
of polynomial thickenings all agree across the comparison.

## Main definitions

* `Ideal.isRestrictedReduction`: polynomial reduction
  `IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* MvPolynomial (Fin k) (R ⧸ J)` modulo an
  open ideal `J : Ideal R`.
* `TauCeti.Huber.quotientIsRestrictedSubringEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientIsRestrictedSubringPowEquivMvPolynomialQuotient`: `R`-algebra
  identifications of quotients modulo `I · R⟨X⟩` and `(I · R⟨X⟩) ^ m` (`0 < m`) with polynomial
  algebras over `R ⧸ I` and `R ⧸ I ^ m`.
* `TauCeti.Huber.isRestrictedSubringPolynomialCone`: the cone of polynomial reductions from
  `IsRestricted.subring` to `I.mvPolynomialQuotientPowSuccDiagram k`.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `weightedEvalHom_eq_restrictedEval₂OfBound`, `weightedEvalHom_eq_restrictedLift`,
  `weightedEvalHomCompletion_eq_restrictedLift`, and
  `restrictedCompletionEvalLinear_eq_restrictedLiftLinear`: Huber evaluation agrees with normed
  and power-bounded evaluation on `IsRestricted.subring`.
* `isAdic_map_algebraMap_isRestricted_subring`,
  `isAdicComplete_map_algebraMap_isRestricted_subring`, and
  `isNoetherianRing_isRestricted_subring_of_isAdic`: adic topology, adic completeness, and
  noetherianity for Gauss-normed restricted series over an `I`-adic normed ring.
* `Ideal.isRestrictedReduction_restrictedMvPowerSeriesCompletionGaussEquiv` and
  `restrictedReduction_eq_isRestrictedReduction_maximalIdeal`: agreement of
  `Ideal.isRestrictedReduction` with `Ideal.restrictedReductionCompletion` and with Gauss unit-ball
  reduction `TauCeti.MvPowerSeries.restrictedReduction`.
* `isLimitIsRestrictedSubringPolynomialCone`: over a complete `I`-adic ultrametric normed ring
  (`I` finitely generated), `IsRestricted.subring` is the limit in `CommRingCat` of
  `(R ⧸ I ^ (n + 1))[X₁, …, Xₖ]`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§5.1.1–5.1.3.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

universe u

public section

namespace TauCeti.Huber

open CategoryTheory Limits Opposite _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped Valued

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

/-- Power-bounded `restrictedLift` agrees with `RingHom.restrictedEval₂OfBound` whenever the
coefficient homomorphism is norm-bounded and `‖a i‖ ≤ 1`. -/
theorem restrictedLift_eq_restrictedEval₂OfBound (hφ_cont : Continuous φ)
    (hba : ∀ i, IsPowerBounded (a i))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    restrictedLift hφ_cont hba f = φ.restrictedEval₂OfBound a hφ ha f := by
  rw [restrictedLift_apply, RingHom.restrictedEval₂OfBound_apply]

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

section PowerBoundedEval

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]

/-- Huber evaluation `weightedEvalHom` into an arbitrary complete Hausdorff nonarchimedean target
agrees with `restrictedLift` across `restrictedMvPowerSeriesGaussEquiv`. -/
theorem weightedEvalHom_eq_restrictedLift {ψ : R →+* B} (hψ : Continuous ψ)
    {b : Fin k → B} (hb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (hb' : ∀ i, IsPowerBounded (b i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hψ.continuousAt hb f =
      restrictedLift hψ hb' (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [coe_weightedEvalHom, restrictedLift_apply, coe_restrictedMvPowerSeriesGaussEquiv]

/-- Over a complete base `R`, completed Huber evaluation `weightedEvalHomCompletion` agrees with
`restrictedLift` across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [CompleteSpace R] {ψ : R →+* B}
    (hψ : Continuous ψ) {b : Fin k → B}
    (hb : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (hb' : ∀ i, IsPowerBounded (b i))
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hψ.continuousAt hb x =
      restrictedLift hψ hb' (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((continuous_restrictedLift hψ hb').comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedLift hψ hb hb']

end PowerBoundedEval

section LinearEval

variable [CompleteSpace R] {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- Linear-topology evaluation `restrictedCompletionEvalLinear` agrees with `restrictedLiftLinear`
across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem restrictedCompletionEvalLinear_eq_restrictedLiftLinear {ψ : R →+* B}
    (hψ : Continuous ψ) (b : Fin k → B) (x : restrictedMvPowerSeriesCompletion k R) :
    restrictedCompletionEvalLinear hψ b x =
      restrictedLiftLinear hψ b (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  let _ := IsLinearTopology.isTopologicalRing (R := B)
  let _ := IsLinearTopology.nonarchimedeanRing B
  rw [restrictedCompletionEvalLinear_eq_weightedEvalHomCompletion,
    restrictedLiftLinear_eq_restrictedLift]
  exact weightedEvalHomCompletion_eq_restrictedLift hψ _ _ x

/-- The `R`-algebra lift `restrictedCompletionLiftLinear` agrees with `restrictedAlgLiftLinear`
across `restrictedMvPowerSeriesCompletionGaussAlgEquiv`. -/
theorem restrictedCompletionLiftLinear_eq_restrictedAlgLiftLinear [Algebra R B]
    (hR : Continuous (algebraMap R B)) (b : Fin k → B)
    (x : restrictedMvPowerSeriesCompletion k R) :
    restrictedCompletionLiftLinear hR b x =
      restrictedAlgLiftLinear hR b (restrictedMvPowerSeriesCompletionGaussAlgEquiv x) := by
  rw [coe_restrictedCompletionLiftLinear, coe_restrictedAlgLiftLinear,
    coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv]
  exact restrictedCompletionEvalLinear_eq_restrictedLiftLinear hR b x

end LinearEval

/-! ### Adic topology, completeness, and noetherianity on `IsRestricted.subring` -/

section Adic

variable {I : Ideal R}

/-- Pulling back the extended ideal `I · R⟨X⟩` along `restrictedMvPowerSeriesGaussEquiv.symm`
gives the extended ideal in `IsRestricted.subring`. -/
private theorem comap_restrictedMvPowerSeriesGaussEquiv_symm_map_algebraMap :
    (I.map (algebraMap R (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
        isWeightFamily_one_weight))).comap
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  let e := restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun r hr ↦ ?_)
  · rw [Ideal.mem_comap, ← coe_restrictedMvPowerSeriesGaussAlgEquiv_symm] at hf
    have hmap : (I.map (algebraMap R _)).map e.toRingHom =
        I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
      rw [Ideal.map_map]
      exact congrArg (Ideal.map · I) (RingHom.ext e.commutes)
    rw [← hmap, ← e.apply_symm_apply f]
    exact Ideal.mem_map_of_mem e.toRingHom hf
  · rw [Ideal.mem_comap, Ideal.mem_comap, ← coe_restrictedMvPowerSeriesGaussAlgEquiv_symm]
    change e.symm (algebraMap R _ r) ∈ _
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hr

/-- Over an ultrametric normed ring `R` whose norm topology is `I`-adic for a finitely generated
ideal `I`, the Gauss-normed restricted-series ring `IsRestricted.subring (fun _ : Fin k ↦ 1)` has
the adic topology of the extended ideal `I · R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestricted_subring (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  have he : Topology.IsInducing
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm :=
    (Homeomorph.mk (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv_symm
      continuous_restrictedMvPowerSeriesGaussEquiv).isInducing
  have h := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm he
  rwa [comap_restrictedMvPowerSeriesGaussEquiv_symm_map_algebraMap] at h

/-- Membership in `I · R⟨X₁, …, Xₖ⟩` inside `IsRestricted.subring` is coefficientwise when `I` is
a finitely generated ideal of definition of `R`. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    f ∈ I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ↔
      ∀ ν, coeff ν (f : MvPowerSeries (Fin k) R) ∈ I := by
  rw [← comap_restrictedMvPowerSeriesGaussEquiv_symm_map_algebraMap, Ideal.mem_comap,
    algebraMap_weightedRestrictedSubring, mem_map_weightedC_iff_of_isAdic hI hfg]
  simp

/-- Over a complete ultrametric normed ring `R` whose norm topology is `I`-adic (`I` finitely
generated), `IsRestricted.subring (fun _ : Fin k ↦ 1)` is adically complete with respect to
`I · R⟨X₁, …, Xₖ⟩`. -/
theorem isAdicComplete_map_algebraMap_isRestricted_subring [CompleteSpace R]
    (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))))
      (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isAdic_map_algebraMap_isRestricted_subring k hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- Over an ultrametric normed adic ring `R` of finite ideal type, the Gauss-normed restricted
power-series ring `IsRestricted.subring (fun _ : Fin k ↦ 1)` is an adic ring of finite ideal
type. -/
instance isAdicRing_isRestricted_subring [IsAdicRing R] {k : ℕ} :
    IsAdicRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  exact ⟨(IsAdicRing.ideal R).map (algebraMap R _), hfg.map _,
    isAdic_map_algebraMap_isRestricted_subring k hI hfg,
    isAdicComplete_map_algebraMap_isRestricted_subring k hI hfg⟩

/-- Over a complete noetherian ultrametric normed ring `R` whose norm topology is `I`-adic, the
Gauss-normed restricted power-series ring `IsRestricted.subring (fun _ : Fin k ↦ 1)` is
noetherian. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [CompleteSpace R] [IsNoetherianRing R]
    (k : ℕ) (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _ restrictedMvPowerSeriesCompletionGaussEquiv

end Adic

end TauCeti.Huber

/-! ### Polynomial reduction on `IsRestricted.subring` -/

namespace Ideal

open _root_.MvPowerSeries TauCeti.Huber TauCeti.MvPowerSeries

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S]

/-- Polynomial reduction of Gauss-normed unit-radius restricted power series modulo an open ideal
`J : Ideal R`. Only finitely many coefficients have norm outside `J`, so coefficientwise reduction
lands in `MvPolynomial (Fin k) (R ⧸ J)`. -/
noncomputable def isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* MvPolynomial (Fin k) (R ⧸ J) :=
  (J.restrictedReduction hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom

/-- Polynomial reduction on `IsRestricted.subring` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (ν : Fin k →₀ ℕ) :
    (J.isRestrictedReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (coeff ν (f : MvPowerSeries (Fin k) R)) := by
  simp [isRestrictedReduction]

/-- `isRestrictedReduction` agrees with `restrictedReduction` across
`restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv
    (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    J.isRestrictedReduction hJ (restrictedMvPowerSeriesGaussEquiv f) =
      J.restrictedReduction hJ f := by
  simp [isRestrictedReduction]

/-- On embedded polynomials, `isRestrictedReduction` is the usual coefficient map
`MvPolynomial.map (Ideal.Quotient.mk J)`. -/
@[simp]
theorem isRestrictedReduction_polynomialToRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (p : MvPolynomial (Fin k) R) :
    J.isRestrictedReduction hJ (polynomialToRestricted (fun _ : Fin k ↦ (1 : ℝ)) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  rw [← restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom,
    isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv,
    restrictedReduction_weightedPolynomialHom]

/-- Reduction sends a scalar `algebraMap R _ r` to the constant polynomial `C (mk J r)`. -/
@[simp]
theorem isRestrictedReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R)) (r : R) :
    J.isRestrictedReduction (k := k) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  rw [← restrictedMvPowerSeriesGaussEquiv_weightedC,
    isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv, restrictedReduction_weightedC]

/-- Reduction preserves the coordinate variables `X i`. -/
@[simp]
theorem isRestrictedReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : Fin k) :
    J.isRestrictedReduction hJ ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ = MvPolynomial.X i := by
  rw [← restrictedMvPowerSeriesGaussEquiv_weightedX,
    isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv, restrictedReduction_weightedX]

/-- Polynomial reduction modulo an open ideal is surjective on `IsRestricted.subring`. -/
theorem isRestrictedReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedReduction (k := k) hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := J.restrictedReduction_surjective (k := k) hJ p
  exact ⟨restrictedMvPowerSeriesGaussEquiv f, by simp⟩

/-- Over a complete base `R`, `isRestrictedReduction` agrees with `restrictedReductionCompletion`
across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
@[simp]
theorem isRestrictedReduction_restrictedMvPowerSeriesCompletionGaussEquiv [CompleteSpace R]
    (J : Ideal R) (hJ : IsOpen (J : Set R))
    (x : restrictedMvPowerSeriesCompletion k R) :
    J.isRestrictedReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) =
      J.restrictedReductionCompletion hJ x := by
  conv_rhs => rw [← restrictedMvPowerSeriesCompletionGaussEquiv.symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply, restrictedReductionCompletion_coe]
  rfl

/-- **Base-change naturality of `isRestrictedReduction`**: along a norm-bounded ring homomorphism
`φ : R →+* S` mapping an open ideal `J` into an open ideal `K`, reduction commutes with
`restrictedMap` and `MvPolynomial.map (Ideal.quotientMap K φ hJK)`. -/
theorem isRestrictedReduction_restrictedMap {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (K : Ideal S) (hK : IsOpen (K : Set S))
    (hJK : J ≤ K.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    K.isRestrictedReduction hK (restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap K φ hJK) (J.isRestrictedReduction hJ f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

end Ideal

namespace TauCeti.Huber

open CategoryTheory Limits Opposite _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped NormedField Valued

section ReductionComparison

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- `Ideal.isRestrictedReduction` is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_isRestrictedReduction {J : Ideal R} (hJ : IsOpen (J : Set R))
    (hI : IsOpen (I : Set R)) (hJI : J ≤ I)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (J.isRestrictedReduction hJ f) =
      I.isRestrictedReduction hI f := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- The maximal ideal `𝓂[K]` of the valuation ring `𝒪[K]` of a nontrivially normed ultrametric
field is open in `𝒪[K]`. -/
theorem isOpen_maximalIdeal_integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] : IsOpen ((𝓂[K] : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  have h : ((𝓂[K] : Ideal 𝒪[K]) : Set 𝒪[K]) = {x : 𝒪[K] | ‖x‖ < 1} :=
    Set.ext fun _ ↦ Valued.integer.mem_maximalIdeal_iff
  exact h ▸ isOpen_lt continuous_norm continuous_const

/-- **Agreement with Gauss unit-ball reduction**: for a nontrivially normed ultrametric field `K`,
the canonical reduction `TauCeti.MvPowerSeries.restrictedReduction` on the Gauss unit ball of
`K⟨X₁, …, Xₖ⟩` coincides with `𝓂[K].isRestrictedReduction` on `𝒪[K]⟨X₁, …, Xₖ⟩` across
`restrictedIntegerEquiv`. -/
theorem restrictedReduction_eq_isRestrictedReduction_maximalIdeal
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (hm : IsOpen ((𝓂[K] : Ideal 𝒪[K]) : Set 𝒪[K]))
    (f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1))) :
    TauCeti.MvPowerSeries.restrictedReduction f =
      𝓂[K].isRestrictedReduction hm (restrictedIntegerEquiv.symm f) := by
  have h1 (ν : Fin k →₀ ℕ) := TauCeti.MvPowerSeries.coeff_restrictedReduction f ν
  have h2 (ν : Fin k →₀ ℕ) :=
    Ideal.coeff_isRestrictedReduction 𝓂[K] hm (restrictedIntegerEquiv.symm f) ν
  refine MvPolynomial.ext _ _ fun ν ↦ (h1 ν).trans
    (Eq.trans (congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext (by simp))) (h2 ν).symm)

/-- Reduction of `IsRestricted.subring` modulo a finitely generated ideal of definition `I` has the
extended ideal `I · R⟨X₁, …, Xₖ⟩` as its kernel. -/
theorem ker_isRestrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.isRestrictedReduction (k := k)
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  ext f
  rw [RingHom.mem_ker, mem_map_algebraMap_isRestricted_subring_iff_of_isAdic hI hfg,
    MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Quotienting `IsRestricted.subring` by the extension of a finitely generated ideal of definition
`I` yields the polynomial algebra `(R ⧸ I)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) := by
  set hI₁ : IsOpen (I : Set R) := by simpa only [pow_one] using hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq (ker_isRestrictedReduction (k := k) hI hfg).symm).trans
    ((I.isRestrictedReduction hI₁).quotientKerEquivOfSurjective
      (I.isRestrictedReduction_surjective hI₁))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) = I.isRestrictedReduction hI₁ (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp

/-- On a represented series, `quotientIsRestrictedSubringEquivMvPolynomialQuotient` computes
`I.isRestrictedReduction`. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      I.isRestrictedReduction (by simpa only [pow_one] using hI.isOpen_pow 1) f := by
  simp [quotientIsRestrictedSubringEquivMvPolynomialQuotient]

/-- For every positive power `I ^ m` of a finitely generated ideal of definition, the quotient of
`IsRestricted.subring` by `(I · R⟨X₁, …, Xₖ⟩) ^ m` is `(R ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq R
    (I.map_pow (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) m).symm).trans
    (quotientIsRestrictedSubringEquivMvPolynomialQuotient (is_ideal_adic_pow hI hm) hfg.pow)

/-- On a represented series, `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` computes
`(I ^ m).isRestrictedReduction`. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedReduction (hI.isOpen_pow m) f := by
  simp [quotientIsRestrictedSubringPowEquivMvPolynomialQuotient]

/-- **Evaluation on `IsRestricted.subring` commutes with polynomial reduction modulo open
ideals**: reducing `restrictedLift hψ hb f` modulo an open ideal `K` equals evaluating
`J.isRestrictedReduction hJ f` via `MvPolynomial.eval₂`. -/
theorem mk_restrictedLift_eq_eval₂_isRestrictedReduction
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {ψ : R →+* B} (hψ : Continuous ψ) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap ψ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk K (restrictedLift hψ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap K ψ hJK) (Ideal.Quotient.mk K ∘ b)
        (J.isRestrictedReduction hJ f) := by
  have hb_wt : IsWeightBounded ψ (fun _ : Fin k ↦ ({1} : Set R)) b :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mpr hb
  conv_lhs => rw [← restrictedMvPowerSeriesGaussEquiv.apply_symm_apply f]
  rw [← weightedEvalHom_eq_restrictedLift hψ hb_wt hb,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction hψ.continuousAt hb_wt J hJ K hK hJK]
  rfl

/-- For a linearly topologised `R`-algebra `B` with a continuous structure map, reducing
`restrictedAlgLiftLinear` at arbitrary `b : Fin k → B` modulo an open ideal `K` equals polynomial
evaluation of `J.isRestrictedReduction`. -/
theorem mk_restrictedAlgLiftLinear_eq_eval₂_isRestrictedReduction
    {B : Type*} [CommRing B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
    [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    (hR : Continuous (algebraMap R B)) (b : Fin k → B)
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap (algebraMap R B))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk K (restrictedAlgLiftLinear hR b f) =
      MvPolynomial.eval₂ (Ideal.quotientMap K (algebraMap R B) hJK) (Ideal.Quotient.mk K ∘ b)
        (J.isRestrictedReduction hJ f) := by
  let _ := IsLinearTopology.isTopologicalRing (R := B)
  let _ := IsLinearTopology.nonarchimedeanRing B
  rw [coe_restrictedAlgLiftLinear, restrictedLiftLinear_eq_restrictedLift]
  exact mk_restrictedLift_eq_eval₂_isRestrictedReduction hR _ J hJ K hK hJK f

end ReductionComparison

section Limit

variable {R : Type u} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- The cone with apex `IsRestricted.subring (fun _ : Fin k ↦ 1)` over
`I.mvPolynomialQuotientPowSuccDiagram k`, whose projections are the polynomial reductions
`(I ^ (n + 1)).isRestrictedReduction`. -/
noncomputable abbrev isRestrictedSubringPolynomialCone (k : ℕ) (hI : IsAdic I) :
    Cone (I.mvPolynomialQuotientPowSuccDiagram k) where
  pt := CommRingCat.of (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
  π.app n := CommRingCat.ofHom
    ((I ^ (n.unop + 1)).isRestrictedReduction (hI.isOpen_pow (n.unop + 1)))
  π.naturality _ _ f := CommRingCat.hom_ext <| RingHom.ext fun x ↦ by
    simpa [Ideal.mvPolynomialQuotientPowSuccDiagram] using
      (map_isRestrictedReduction (hI.isOpen_pow _) (hI.isOpen_pow _)
        (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

/-- **Gauss-normed restricted series as a limit of polynomial algebras**: over a complete
ultrametric normed ring `R` whose norm topology is `I`-adic (`I` finitely generated),
`IsRestricted.subring (fun _ : Fin k ↦ 1)` is the limit in `CommRingCat` of
`(R ⧸ I ^ (n + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitIsRestrictedSubringPolynomialCone [CompleteSpace R]
    (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsLimit (isRestrictedSubringPolynomialCone k hI) := by
  refine IsLimit.ofIsoLimit (isLimitRestrictedCompletionPolynomialCone k hI hfg)
    ((Cone.extendIso _
      (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toCommRingCatIso).trans ?_)
  refine Cone.ext (Iso.refl _) fun n ↦ CommRingCat.hom_ext <| RingHom.ext fun f ↦ ?_
  simp [restrictedCompletionPolynomialCone, isRestrictedSubringPolynomialCone,
    Ideal.isRestrictedReduction, RingEquiv.toCommRingCatIso]

end Limit

end TauCeti.Huber

end

