/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Bond.Trading
public import TauCeti.MeasureTheory.VectorMeasure.Integral

/-!
# Approximation of bond gains on the full horizon

Elementary bond gains converge uniformly in observation time to the pathwise bond
integral when the holdings converge in L¹ of the bond's variation measure. The limiting
holding need only be almost everywhere strongly measurable for that measure; it need
not be continuous or bounded. Grids may vary, need not be nested, and may contain repeated dates.

The result is pathwise, so it applies to random holdings without an initial or terminal
moment assumption. The same full-horizon variation norm controls all observation times,
which is needed when passing the bond term of the self-financing identity to a limit.
The limit is the ordinary integral of interest income.
Neither positivity of the short rate nor positivity of the initial bond price is required.

The uniform estimate uses
`MeasureTheory.VectorMeasure.tendstoUniformly_setIntegral_of_L1`; the elementary
identification is `TauCeti.Finance.simpleGains_eq_setIntegral_vectorMeasureIcc_bondPrice`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.Finance

variable {Ω ι : Type*} {r : ℝ → ℝ} {β₀ T : ℝ}
  {l : Filter ι} {n : ι → ℕ} {τ : ι → ℕ → ℝ} {a : ι → ℕ → Ω → ℝ}

/-- Approximation of a bond holding in full-horizon variation L¹ gives uniform convergence
of its elementary gains to the integral of interest income `b r β`. This is a pathwise
statement: no measurability or moments in the sample variable are required. Convergence
in variation L¹ permits arbitrary changes where the bond has zero variation. -/
theorem tendstoUniformlyOn_simpleGains_bondPrice_of_L1
    (hr : ContinuousOn r (Icc 0 T)) (hT : 0 ≤ T)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k))) (hzero : ∀ k, 0 ≤ τ k 0)
    (ω : Ω) {b : ℝ → ℝ}
    (hb : AEStronglyMeasurable b
      ((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).variation)
    (hlim : Tendsto (fun k ↦ ∫⁻ u,
      ‖simpleHolding (τ k) (n k) (a k) u ω - b u‖ₑ
        ∂((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).variation)
      l (𝓝 0)) :
    TendstoUniformlyOn
      (fun k t ↦ simpleGains (τ k) (n k) (a k) (fun u _ ↦ bondPrice r β₀ u) t ω)
      (fun t ↦ ∫ u in 0..t, b u * (r u * bondPrice r β₀ u)) l (Icc 0 T) := by
  have hint k : ((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).Integrable
      (fun u ↦ simpleHolding (τ k) (n k) (a k) u ω) := by
    simp_rw [simpleHolding_def]
    exact integrable_finsetSum _ fun j _ ↦
      (integrable_const (a k j ω)).indicator measurableSet_Ioc
  have h := (VectorMeasure.tendstoUniformly_setIntegral_of_L1
    (B := ContinuousLinearMap.mul ℝ ℝ) hb (.of_forall hint) hlim).comp (fun t ↦ Ioc 0 t)
  apply (h.tendstoUniformlyOn.congr_right
    (fun t ht ↦ setIntegral_Ioc_vectorMeasureIcc_bondPrice hr hT β₀ b ht)).congr
  filter_upwards [] with k t ht
  exact (simpleGains_eq_setIntegral_vectorMeasureIcc_bondPrice hr hT β₀
    (hτ k) (hzero k) (a k) ω ht).symm

end TauCeti.Finance
