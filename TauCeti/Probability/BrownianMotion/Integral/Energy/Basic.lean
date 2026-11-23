/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.Order.Monotone.Basic

/-!
# Elementary Brownian isometry in the predictable energy measure

The second moment of an elementary Brownian gain is the lower square-energy integral
of its holding against the finite-horizon predictable measure. This identifies the
finite-grid isometry with the native predictable `L²` norm used for completion, without
introducing an integral operator or assuming that the general stochastic integral exists.

At an arbitrary observation time `t`, the `L²(P)` norm of the elementary integral equals the
`L²` norm of its holding for Lebesgue time on `(0,t]` times `P`
(`TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_simpleGains`); the grid may extend
beyond `t`. This is the form used to show that elementary integrals of `L²`-approximating
holdings are Cauchy in `L²(P)` at every time.

Heights need only be square integrable and measurable at their left endpoints.
The grid may be empty or have repeated dates; Brownian path regularity and usual
conditions on the filtration are not needed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory Finset Set TauCeti.Finance
open scoped ENNReal NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- An elementary Brownian integral with square-integrable left-measurable heights is square
integrable at every time. -/
theorem memLp_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (t : ℝ≥0) :
    MemLp (simpleGains τ n a W t) 2 P := by
  rw [show simpleGains τ n a W t = _ from funext (simpleGains_def τ n a W t)]
  exact hW.memLp_sum_mul_sub_min (range n)
    (fun i hi ↦ hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
    (fun i hi ↦ ha i (mem_range.mp hi)) (fun i hi ↦ ha₂ i (mem_range.mp hi)) t

/-- **The elementary Brownian isometry at an observation time.** The `L²(P)` norm of an
elementary Brownian integral at time `t` is the `L²` norm of its holding for Lebesgue time on
`(0,t]` times `P`. The grid may extend beyond `t`, and square-integrable left-measurable
heights suffice; no boundedness assumption is imposed. -/
theorem eLpNorm_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (t : ℝ≥0) :
    eLpNorm (simpleGains τ n a W t) 2 P =
      eLpNorm (Function.uncurry (simpleHolding τ n a)) 2
        ((TauCeti.Probability.timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hle (i : ℕ) (hi : i ∈ range n) : τ i ≤ τ (i + 1) :=
    hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i)
  have hdisj : ((range n : Finset ℕ) : Set ℕ).Pairwise
      fun i j ↦ τ (i + 1) ≤ τ j ∨ τ (j + 1) ≤ τ i := by
    simpa only [coe_range] using hτ.pairwise_succ_le_or_succ_le
  have hG : simpleGains τ n a W t = fun ω ↦ ∑ i ∈ range n,
      a i ω * (W (min (τ (i + 1)) t) ω - W (min (τ i) t) ω) :=
    funext (simpleGains_def τ n a W t)
  have hmem := hW.memLp_simpleGains hτ ha ha₂ t
  have hmeasa (i : ℕ) (hi : i < n) : Measurable (fun ω ↦ ENNReal.ofReal (a i ω ^ 2)) :=
    (((ha i hi).mono (ℱ.le _)).measurable.pow_const 2).ennreal_ofReal
  -- Compare the squares of both norms as lower integrals.
  refine ENNReal.rpow_left_injective (x := 2) two_ne_zero ?_
  simp only [ENNReal.rpow_two]
  rw [eLpNorm_two_sq_eq_lintegral hmem.aestronglyMeasurable,
    ← lintegral_lintegral_enorm_sq_eq_eLpNorm_prod_sq
      ((isStronglyPredictable_simpleHolding ha).mono ℱ.predictable_le_prod).aestronglyMeasurable]
  simp_rw [Function.uncurry_apply_pair, lintegral_enorm_sq_simpleHolding_timeMeasure hτ,
    Real.enorm_sq_eq_ofReal_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq (ae_of_all _ fun _ ↦ sq_nonneg _)]
  simp only [hG]
  rw [hW.integral_sq_sum_mul_sub_min (range n) hle hdisj (fun i hi ↦ ha i (mem_range.mp hi))
      (fun i hi ↦ ha₂ i (mem_range.mp hi)) t,
    lintegral_finsetSum _ (fun i hi ↦ (hmeasa i (mem_range.mp hi)).mul_const _),
    ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast min_le_min_right t (hle i hi))))]
  refine sum_congr rfl fun i hi ↦ ?_
  -- An interval starting after `t` has no elapsed length on either side.
  have hlen : ENNReal.ofReal ((min (τ (i + 1)) t : ℝ≥0) - (τ i : ℝ)) =
      ENNReal.ofReal ((min (τ (i + 1)) t : ℝ≥0) - (min (τ i) t : ℝ≥0)) := by
    by_cases hit : τ i ≤ t
    · rw [min_eq_left hit]
    · have hti : t ≤ τ i := (not_le.mp hit).le
      rw [min_eq_right hti, min_eq_right (hti.trans (hle i hi)), sub_self,
        ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hti)),
        ENNReal.ofReal_zero]
  rw [lintegral_mul_const _ (hmeasa i (mem_range.mp hi)), hlen,
    ← ofReal_integral_eq_lintegral_ofReal (ha₂ i (mem_range.mp hi)).integrable_sq
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ sq_nonneg _)]

/-- The elementary Brownian isometry with its actual predictable lower-integral energy.
Square-integrable left-measurable heights suffice; no boundedness assumption is imposed. -/
theorem lintegral_enorm_sq_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫⁻ ω, ‖simpleGains τ n a W (τ n) ω‖ₑ ^ 2 ∂P =
      ∫⁻ p, ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2 ∂ℱ.predictableMeasure P (τ n) := by
  have hholding := isStronglyPredictable_simpleHolding ha
  have hm : Measurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2) :=
    hholding.eNorm.pow_const 2
  rw [ℱ.predictableMeasure_def, lintegral_trim ℱ.predictable_le_prod hm,
    ← eLpNorm_two_sq_eq_lintegral (hW.memLp_simpleGains hτ ha ha₂ _).aestronglyMeasurable,
    hW.eLpNorm_simpleGains hτ ha ha₂,
    eLpNorm_two_sq_eq_lintegral (hholding.mono ℱ.predictable_le_prod).aestronglyMeasurable]
  simp only [Function.uncurry_def]

end TauCeti.Probability.IsFilteredPreBrownianReal
