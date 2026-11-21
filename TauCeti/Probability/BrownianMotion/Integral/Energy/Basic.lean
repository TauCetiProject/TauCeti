/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Analysis.Normed.Group.Real

/-!
# Elementary Brownian isometry in the predictable energy measure

At every finite observation horizon `T`, the second moment of an elementary Brownian gain on a
nondecreasing grid equals the lower square-energy integral of its holding against
`(Probability.timeMeasure T).prod P` (`lintegral_enorm_sq_simpleGains_timeMeasure`,
`eLpNorm_simpleGains_eq`), while at the terminal grid date `τ n` this isometry is also expressed
against the trimmed predictable measure `ℱ.predictableMeasure P (τ n)`
(`lintegral_enorm_sq_simpleGains`). This identifies the finite-grid isometry with the native
predictable `L²` norm used for completion, without introducing an integral operator or assuming
that the general stochastic integral exists.

Heights need only be square integrable and measurable at their left endpoints.
The grid must be nondecreasing (`MonotoneOn τ (Iic n)`), though it may be empty or have repeated
dates; Brownian path regularity and usual conditions on the filtration are not needed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory Set TauCeti.Finance
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- Elementary Brownian gains with square-integrable left-measurable heights belong to `L²(P)` at
every observation time `T`. -/
theorem memLp_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    MemLp (simpleGains τ n a W T) 2 P :=
  (hW.memLp_sum_mul_sub_min (range n)
    (fun i hi ↦ hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
    (fun i hi ↦ ha i (mem_range.mp hi)) (fun i hi ↦ ha₂ i (mem_range.mp hi)) T).ae_eq
      (.of_forall fun ω ↦ (simpleGains_def τ n a W T ω).symm)

/-- Lower-integral form of the elementary Brownian isometry at an arbitrary observation time `T`. -/
theorem lintegral_enorm_sq_simpleGains_timeMeasure (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Iic n)) (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    ∫⁻ ω, ‖simpleGains τ n a W T ω‖ₑ ^ 2 ∂P =
      ∫⁻ p, ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2 ∂(timeMeasure T).prod P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm : Measurable (fun p : ℝ≥0 × Ω ↦ ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2) :=
    ((isStronglyPredictable_simpleHolding ha).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const
      2
  rw [lintegral_prod_symm _ hm.aemeasurable]
  simp_rw [lintegral_enorm_sq_simpleHolding_timeMeasure hτ, Real.enorm_sq_eq_ofReal_sq]
  have hdisj : ((range n : Finset ℕ) : Set ℕ).Pairwise
      fun i j ↦ τ (i + 1) ≤ τ j ∨ τ (j + 1) ≤ τ i :=
    fun i hi j hj hij ↦ hij.lt_or_gt.imp
      (hτ (mem_range.mp hi) (mem_range.mp hj).le) (hτ (mem_range.mp hj) (mem_range.mp hi).le)
  have hmeas (i : ℕ) (hi : i < n) : Measurable (fun ω ↦ ENNReal.ofReal (a i ω ^ 2)) :=
    (((ha i hi).mono (ℱ.le _)).measurable.pow_const 2).ennreal_ofReal
  rw [← ofReal_integral_eq_lintegral_ofReal (hW.memLp_simpleGains hτ ha ha₂ T).integrable_sq
    (.of_forall fun _ ↦ sq_nonneg _)]
  simp_rw [simpleGains_def]
  rw [hW.integral_sq_sum_mul_sub_min (range n)
      (fun i hi ↦ hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i)) hdisj
      (fun i hi ↦ ha i (mem_range.mp hi)) (fun i hi ↦ ha₂ i (mem_range.mp hi)) T,
    lintegral_finsetSum _ (fun i hi ↦ (hmeas i (mem_range.mp hi)).mul_const _),
    ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_min_right T
        (hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))))))]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  have hlen : ENNReal.ofReal (((min (τ (i + 1)) T : ℝ≥0) : ℝ) - ((min (τ i) T : ℝ≥0) : ℝ)) =
      ENNReal.ofReal (((min (τ (i + 1)) T : ℝ≥0) : ℝ) - (τ i : ℝ)) := by
    by_cases hle : τ i ≤ T
    · rw [min_eq_left hle]
    · have hgt : T ≤ τ i := le_of_not_ge hle
      rw [min_eq_right hgt, min_eq_right (hgt.trans (hτ hi'.le hi' (Nat.le_succ i))), sub_self,
        ENNReal.ofReal_zero,
        ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hgt))]
  rw [lintegral_mul_const _ (hmeas i hi'), ← ofReal_integral_eq_lintegral_ofReal
      (ha₂ i hi').integrable_sq (.of_forall fun _ ↦ sq_nonneg _),
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ sq_nonneg _), Nat.succ_eq_add_one, hlen]

/-- The elementary Brownian isometry at the terminal grid date `τ n`, expressed against the trimmed
predictable measure `ℱ.predictableMeasure P (τ n)`. Square-integrable left-measurable heights
suffice; no boundedness assumption is imposed. -/
theorem lintegral_enorm_sq_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Iic n)) (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫⁻ ω, ‖simpleGains τ n a W (τ n) ω‖ₑ ^ 2 ∂P =
      ∫⁻ p, ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2 ∂ℱ.predictableMeasure P (τ n) := by
  have hm : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2) :=
    (isStronglyPredictable_simpleHolding ha).eNorm.pow_const 2
  rw [ℱ.predictableMeasure_def, lintegral_trim ℱ.predictable_le_prod hm,
    hW.lintegral_enorm_sq_simpleGains_timeMeasure hτ ha ha₂ (τ n)]

/-- `L²`-seminorm form of the elementary Brownian isometry at an arbitrary observation time `T`. -/
theorem eLpNorm_simpleGains_eq (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    eLpNorm (simpleGains τ n a W T) 2 P =
      eLpNorm (Function.uncurry (simpleHolding τ n a)) 2 ((timeMeasure T).prod P) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
      (hW.memLp_simpleGains hτ ha ha₂ T).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
      ((isStronglyPredictable_simpleHolding ha).mono ℱ.predictable_le_prod).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Function.uncurry_def,
    hW.lintegral_enorm_sq_simpleGains_timeMeasure hτ ha ha₂ T]

end TauCeti.Probability.IsFilteredPreBrownianReal
