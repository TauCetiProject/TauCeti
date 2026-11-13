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

The second moment of an elementary Brownian gain is the lower square-energy integral
of its holding against the finite-horizon predictable measure. This identifies the
finite-grid isometry with the native predictable `L²` norm used for completion, without
introducing an integral operator or assuming that the general stochastic integral exists.

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

/-- The elementary Brownian isometry with its actual predictable lower-integral energy.
Square-integrable left-measurable heights suffice; no boundedness assumption is imposed. -/
theorem lintegral_enorm_sq_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫⁻ ω, ‖simpleGains τ n a W (τ n) ω‖ₑ ^ 2 ∂P =
      ∫⁻ p, ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2 ∂ℱ.predictableMeasure P (τ n) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hholding := isStronglyPredictable_simpleHolding ha
  have hm : Measurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2) :=
    hholding.eNorm.pow_const 2
  rw [ℱ.lintegral_predictableMeasure P hm]
  rw [lintegral_lintegral_swap (hm.mono ℱ.predictable_le_prod le_rfl).aemeasurable]
  simp_rw [lintegral_enorm_sq_simpleHolding_timeMeasure hτ]
  have hsum := hW.memLp_sum_mul_sub hτ ha ha₂
  simp_rw [Real.enorm_sq_eq_ofReal_sq, simpleGains_apply_eq_sum hτ le_rfl]
  have hmeas (i : ℕ) (hi : i < n) : Measurable (fun ω ↦ ENNReal.ofReal (a i ω ^ 2)) :=
    (((ha i hi).mono (ℱ.le _)).measurable.pow_const 2).ennreal_ofReal
  rw [lintegral_finsetSum _ (fun i hi ↦ (hmeas i (mem_range.mp hi)).mul_const _),
    ← ofReal_integral_eq_lintegral_ofReal hsum.integrable_sq (ae_of_all _ fun _ ↦ sq_nonneg _),
    hW.integral_sq_sum_mul_sub hτ ha ha₂,
    ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (sub_nonneg.mpr (by
        exact_mod_cast hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))))]
  refine sum_congr rfl fun i hi ↦ ?_
  have hin : τ (i + 1) ≤ τ n := hτ (mem_range.mp hi) self_mem_Iic (mem_range.mp hi)
  rw [lintegral_mul_const _ (hmeas i (mem_range.mp hi)), min_eq_left hin,
    ← ofReal_integral_eq_lintegral_ofReal (ha₂ i (mem_range.mp hi)).integrable_sq
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ sq_nonneg _)]

end TauCeti.Probability.IsFilteredPreBrownianReal
