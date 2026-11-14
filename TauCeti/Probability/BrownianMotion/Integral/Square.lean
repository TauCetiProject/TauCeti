/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Square compensation for elementary Brownian integrals

The square of an elementary Brownian integral, minus its elapsed pathwise square
energy, is a martingale. The heights are square integrable and known at the left
endpoints; they need not be bounded or independent of one another. This is the
elementary square decomposition used to identify the bracket of the completed integral.

The one-interval results also allow an integrable height for the first-order integral.
Only filtration-relative pre-Brownian laws are needed, not path continuity or usual
conditions on the filtration. Empty grids and repeated dates are allowed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.2, Proposition 3.2.10.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ξ : Ω → ℝ} {s v : ℝ≥0}

/-- A position known at `s` and integrable, held until `v`, gives a true Brownian
martingale. Independence supplies product integrability without boundedness or an
`L²` assumption on the position. -/
theorem martingale_mul_sub_min (hW : IsFilteredPreBrownianReal ℱ W P) (hsv : s ≤ v)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξi : Integrable ξ P) :
    Martingale (fun t ω ↦ ξ ω * (W (min v t) ω - W (min s t) ω)) ℱ P := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  refine ((hW.martingale.const_min v).sub (hW.martingale.const_min s)).mul_left_of_eq_zero
    (r := s) (fun t ht ↦ ?_) hξ (fun t ↦ ?_)
  · ext ω
    simp [min_eq_right ht, min_eq_right (ht.trans hsv)]
  · by_cases hst : s ≤ t
    · simpa only [min_eq_left hst, Pi.mul_def, Pi.sub_def] using
        (hW.indepFun_sub (le_min hsv hst) hξ.measurable).integrable_mul hξi
          ((hW.integrable_eval _).sub (hW.integrable_eval _))
    · have hts : t ≤ s := (not_le.mp hst).le
      convert integrable_zero Ω ℝ P using 1
      ext ω
      simp [min_eq_right hts, min_eq_right (hts.trans hsv)]

/-- The square of a Brownian position held on `(s,v]`, compensated by its elapsed
square energy, is a true martingale. Only the second moment of the position is needed. -/
theorem martingale_sq_mul_sub_min_sub (hW : IsFilteredPreBrownianReal ℱ W P) (hsv : s ≤ v)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    Martingale (fun t ω ↦ (ξ ω * (W (min v t) ω - W (min s t) ω)) ^ 2 -
      ξ ω ^ 2 * (↑(min v t) - ↑(min s t))) ℱ P := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  -- First center the Brownian square at s. Subtracting the cross term is essential:
  -- the difference of the two compensated marginal squares alone is not this square.
  have hcross := hW.martingale_mul_sub_min hsv (hW.adapted s).stronglyMeasurable
    (hW.integrable_eval s)
  have hcenter : Martingale (fun t ω ↦
      (W (min v t) ω - W (min s t) ω) ^ 2 -
        (↑(min v t) - ↑(min s t))) ℱ P := by
    convert ((hW.martingale_sq_sub.const_min v).sub
      (hW.martingale_sq_sub.const_min s)).sub (hcross.smul 2) using 1
    ext t ω
    by_cases hst : s ≤ t
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, min_eq_left hst]
      ring
    · have hts : t ≤ s := (not_le.mp hst).le
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, min_eq_right hts,
        min_eq_right (hts.trans hsv), sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0),
        Pi.zero_apply]
  have hproduct : ∀ t, Integrable (fun ω ↦ ξ ω ^ 2 *
      ((W (min v t) ω - W (min s t) ω) ^ 2 -
        (↑(min v t) - ↑(min s t)))) P := by
    intro t
    by_cases hst : s ≤ t
    · have hi := (hW.indepFun_sub (le_min hsv hst) hξ.measurable).comp
        (measurable_id.pow_const 2)
        ((measurable_id.pow_const 2).sub
          (measurable_const (a := (↑(min v t) - (s : ℝ)))))
      simpa only [Function.comp_apply, id_eq, min_eq_left hst, Pi.mul_def, Pi.sub_def] using
        hi.integrable_mul hξ₂.integrable_sq
          ((hW.integrable_pow_sub s (min v t) 2).sub (integrable_const _))
    · have hts : t ≤ s := (not_le.mp hst).le
      simp only [min_eq_right hts, min_eq_right (hts.trans hsv), sub_self,
        zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact integrable_zero _ _ _
  have h := hcenter.mul_left_of_eq_zero (r := s) (fun t ht ↦ by
    ext ω
    simp [min_eq_right ht, min_eq_right (ht.trans hsv)]) (hξ.pow 2) hproduct
  convert h using 1
  ext t ω
  simp only [Pi.mul_apply, Pi.pow_apply]
  ring

/-- **Elementary Brownian square decomposition.** Squared elementary gains minus the
sum of squared heights times elapsed interval lengths form a true martingale. The
compensator is random pathwise energy, not its expectation. The process is defined
at all observation times, including times inside trading intervals. -/
theorem martingale_sq_simpleGains_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    Martingale (fun t ω ↦ Finance.simpleGains τ n a W t ω ^ 2 -
      ∑ i ∈ range n, a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) ℱ P := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  induction n with
  | zero =>
    simpa only [Finance.simpleGains_def, sum_range_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero, Pi.zero_def] using (martingale_zero ℝ ℱ P)
  | succ n ih =>
    have hτn : MonotoneOn τ (Set.Iic n) := hτ.mono (Iic_subset_Iic.mpr n.le_succ)
    have han i (hi : i < n) := ha i (hi.trans n.lt_succ_self)
    have han₂ i (hi : i < n) := ha₂ i (hi.trans n.lt_succ_self)
    have hsv : τ n ≤ τ (n + 1) := hτ (by simp) (by simp) n.le_succ
    have hprev := ih hτn han han₂
    -- The new cross term uses the gains already realized at the left endpoint.
    -- Its height is L¹ by Cauchy–Schwarz, and Brownian independence suffices thereafter.
    have hknown : StronglyMeasurable[ℱ (τ n)] (Finance.simpleGains τ n a W (τ n)) :=
      Finance.stronglyAdapted_simpleGains hτn han hW.adapted.stronglyAdapted (τ n)
    have hprev₂ : MemLp (Finance.simpleGains τ n a W (τ n)) 2 P := by
      convert hW.memLp_sum_mul_sub hτn han han₂ using 1
      ext ω
      exact Finance.simpleGains_apply_eq_sum hτn le_rfl W ω
    have hcross := hW.martingale_mul_sub_min hsv (hknown.mul (ha n n.lt_succ_self))
      (hprev₂.integrable_mul (ha₂ n n.lt_succ_self))
    have hnext := hW.martingale_sq_mul_sub_min_sub hsv (ha n n.lt_succ_self)
      (ha₂ n n.lt_succ_self)
    convert (hprev.add hnext).add (hcross.smul 2) using 1
    ext t ω
    have hgain : Finance.simpleGains τ (n + 1) a W t ω =
        Finance.simpleGains τ n a W t ω +
          a n ω * (W (min (τ (n + 1)) t) ω - W (min (τ n) t) ω) := by
      simp only [Finance.simpleGains_def, sum_range_succ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [hgain, sum_range_succ]
    by_cases hnt : τ n ≤ t
    · rw [Finance.simpleGains_of_ge hτn hnt]
      ring
    · have htn : t ≤ τ n := (not_le.mp hnt).le
      simp only [min_eq_right htn, min_eq_right (htn.trans hsv), sub_self, mul_zero]
      ring

end TauCeti.Probability.IsFilteredPreBrownianReal
