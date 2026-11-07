/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Geometric.Basic
public import TauCeti.Probability.Martingale.MaximalInequality
import TauCeti.MeasureTheory.Integral.Lebesgue.Supremum
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Running maxima of exponential martingales and geometric Brownian motion

Let `W` be a Brownian motion relative to a filtration `ℱ` whose paths are almost surely
right-continuous before a horizon `T`. This file shows that the running maxima

`sup_{t ≤ T} exp (θ W_t - θ² t / 2)`  and  `sup_{t ≤ T} S_t ^ q`,

of an exponential martingale and of a real power of a geometric Brownian motion
`S_t = s exp ((μ - σ² / 2) t + σ W_t)`, `s ≥ 0`, have finite expectation, for every real `θ` and
`q`. For `q > 0` this is a finite `q`-th moment of the running maximum `sup_{t ≤ T} S_t`; for
`q < 0` and `s > 0` it is a finite `q`-th moment of the running minimum. (For `s = 0` and `q < 0`
the bound holds only through the convention `0 ^ q = 0`.) For a function `V` of polynomial
growth, `|V(x, t)| ≤ A (1 + x ^ p)` with `p ≥ 0`, these bounds dominate `|V(S_t, t)|` uniformly in
`t ≤ T` by an integrable random variable. This is the domination, and hence the uniform
integrability, used to pass to the limit in stopped expectations `E[V(S_{t ∧ τ}, t ∧ τ)]` along
localizing stopping times `τ`.

The running maxima are measured with `MeasureTheory.lintegral`. They are almost everywhere
measurable by `MeasureTheory.aemeasurable_iSup_le_ofReal`, so these bounds are genuine moment
bounds.

The proof combines two facts. A weak-type maximal inequality bounds the expected running maximum of
the square root of a nonnegative submartingale
(`MeasureTheory.Submartingale.lintegral_iSup_sqrt_le`). And the exponential martingale with
parameter `θ` is, up to the factor `exp (θ² t / 2)`, the square root of the exponential martingale
with parameter `2θ`.

## Main declarations

In the namespace `TauCeti.Probability`:

* `IsFilteredPreBrownianReal.lintegral_iSup_exponentialMartingale_lt_top`:
  `E[sup_{t ≤ T} exp (θ W_t - θ² t / 2)] < ∞`.
* `IsFilteredPreBrownianReal.lintegral_iSup_rpow_geometricBrownianMotion_lt_top`:
  `E[sup_{t ≤ T} S_t ^ q] < ∞` for `s ≥ 0` and real `q`.
* `IsFilteredPreBrownianReal.lintegral_iSup_geometricBrownianMotion_lt_top`:
  `E[sup_{t ≤ T} S_t] < ∞` for every initial value `s`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Theorem 1.3.8 and §5.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- **The running maximum of an exponential martingale is integrable.** If the paths of `W` are
almost surely right-continuous before `T`, then `E[sup_{t ≤ T} exp (θ W_t - θ² t / 2)] < ∞`. -/
theorem lintegral_iSup_exponentialMartingale_lt_top (hW : IsFilteredPreBrownianReal ℱ W P)
    {T : ℝ≥0} (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (θ : ℝ) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (exponentialMartingale θ W t ω) ∂P < ∞ := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  -- `Z^θ_t = exp (θ² t / 2) √(Z^{2θ}_t)`, and `Z^{2θ}` is a nonnegative martingale.
  refine lintegral_iSup_ofReal_lt_top_of_le_mul (exp_pos (θ ^ 2 * T / 2)).le
    (Y := fun t ω ↦ √(exponentialMartingale (2 * θ) W t ω)) (fun ω t ht ↦ ?_) ?_
  · rw [exponentialMartingale_def, exponentialMartingale_def, ← exp_half, ← exp_add]
    gcongr
    have : (t : ℝ) ≤ T := NNReal.coe_le_coe.2 ht
    nlinarith [sq_nonneg θ]
  · have hcont' : ∀ᵐ ω ∂P, ∀ t < T,
        ContinuousWithinAt (fun u ↦ exponentialMartingale (2 * θ) W u ω) (Ioi t) t := by
      filter_upwards [hcont] with ω hω t ht
      simp_rw [exponentialMartingale_def]
      exact (((hω t ht).const_mul _).sub (((NNReal.continuous_coe.const_mul _).div_const
        _).continuousWithinAt)).rexp
    refine lt_of_le_of_lt ((hW.martingale_exponentialMartingale (2 * θ)).submartingale
      |>.lintegral_iSup_sqrt_le (fun t ω ↦ (exponentialMartingale_pos _ W t ω).le) hcont') ?_
    simp [hW.integral_exponentialMartingale]

/-- **The running maximum of a power of geometric Brownian motion is integrable.** If the paths
of `W` are almost surely right-continuous before `T`, then for an initial value `s ≥ 0` and every
real `q`, `E[sup_{t ≤ T} S_t ^ q] < ∞`, where `S_t = s exp ((μ - σ² / 2) t + σ W_t)`. -/
theorem lintegral_iSup_rpow_geometricBrownianMotion_lt_top (hW : IsFilteredPreBrownianReal ℱ W P)
    {T : ℝ≥0} (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    {s : ℝ} (hs : 0 ≤ s) (μ σ q : ℝ) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω ^ q) ∂P < ∞ := by
  -- `S_t ^ q = s ^ q exp (c t) Z^{qσ}_t`, and `exp (c t) ≤ exp (|c| T)` for `t ≤ T`.
  set c := q * μ + q * (q - 1) * σ ^ 2 / 2
  refine lintegral_iSup_ofReal_lt_top_of_le_mul (by positivity) (C := s ^ q * exp (|c| * T))
    (fun ω t ht ↦ ?_) (hW.lintegral_iSup_exponentialMartingale_lt_top hcont (q * σ))
  rw [rpow_geometricBrownianMotion hs]
  gcongr
  exacts [(exponentialMartingale_pos _ W t ω).le, le_abs_self c]

/-- **The running maximum of geometric Brownian motion is integrable.** If the paths of `W` are
almost surely right-continuous before `T`, then `E[sup_{t ≤ T} S_t] < ∞`, where
`S_t = s exp ((μ - σ² / 2) t + σ W_t)`, for every initial value `s`. -/
theorem lintegral_iSup_geometricBrownianMotion_lt_top (hW : IsFilteredPreBrownianReal ℱ W P)
    {T : ℝ≥0} (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (s μ σ : ℝ) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω) ∂P < ∞ := by
  rcases le_or_gt 0 s with hs | hs
  · simpa using hW.lintegral_iSup_rpow_geometricBrownianMotion_lt_top hcont hs μ σ 1
  · -- For a negative initial value the process is negative and the integrand vanishes.
    have h (t : ℝ≥0) (ω : Ω) : geometricBrownianMotion s μ σ W t ω ≤ 0 := by
      rw [geometricBrownianMotion_def]
      exact mul_nonpos_iff.2 (Or.inr ⟨hs.le, (exp_pos _).le⟩)
    simp [ENNReal.ofReal_eq_zero.2 (h _ _)]

end TauCeti.Probability.IsFilteredPreBrownianReal
