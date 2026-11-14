/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.RunningMaximum
public import TauCeti.MeasureTheory.Function.UniformIntegrable

/-!
# Removing localization for prices of polynomial growth

A price with a uniform bound `|C(s,t)| ≤ A (1 + s^q)` along a positive geometric Brownian
stock converges in `Lᵖ`, for every `1 ≤ p < ∞`, to its continuous terminal extension, when
sampled at any sequence of random times in a finite horizon tending almost surely to expiry.
In particular, this permits the removal of localization in square-integrable pricing identities,
not just in expectations.
The exponent `q` may be any real number, since positive geometric Brownian motion has maximal
moments of negative orders as well. Mean-square convergence also implies `L¹` convergence on
the probability space.

The intermediate uniform-integrability result allows an arbitrarily indexed family of different
sampled prices with a common bound by `A (1 + S_t ^ q)`, at any real initial stock price.
For nonpositive initial spot, this uses Mathlib's signed/zero `Real.rpow` conventions, not
`|S_t| ^ q`; the bound can degenerate (for example, at zero spot and negative `q`).
The times need not be
stopping times or even measurable: only the sampled values must be almost everywhere strongly
measurable. Continuity is required only at the terminal spot/time pair. No stochastic integral
or martingale property is inferred from these moment and continuity assumptions.

The maximal-moment input is
`IsFilteredPreBrownianReal.lintegral_iSup_rpow_geometricBrownianMotion_lt_top`.

## References

* I. Karatzas, S. E. Shreve, *Methods of Mathematical Finance*, Springer, 1998, §2.4.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §6.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {s μ σ A q : ℝ} {T : ℝ≥0}

/-- A common polynomial-growth bound along geometric Brownian motion gives uniform `Lᵖ`
integrability, for `1 ≤ p < ∞`, at any family of bounded random times. Any real initial spot and
growth exponent are allowed; for nonpositive spot, `hbound` uses Mathlib's signed/zero
`Real.rpow` conventions, not `|S_t| ^ q`, so it can degenerate rather than express polynomial
growth in the absolute spot. The times need not be stopping times or measurable. -/
theorem uniformIntegrable_polynomialGrowth_geometricBrownianMotion {ι : Type*}
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) {τ : ι → Ω → ℝ≥0} {V : ι → Ω → ℝ}
    (hV : ∀ i, AEStronglyMeasurable (V i) P)
    (hτ : ∀ i, ∀ᵐ ω ∂P, τ i ω ≤ T)
    (hbound : ∀ i, ∀ᵐ ω ∂P,
      |V i ω| ≤ A * (1 + geometricBrownianMotion s μ σ W (τ i ω) ω ^ q)) :
    UniformIntegrable V p P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  -- The absolute-spot process controls real powers even when the original spot is negative.
  let M : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T,
    ENNReal.ofReal (geometricBrownianMotion |s| μ σ W t ω ^ (q * p.toReal))
  have hM : AEMeasurable M P := by
    refine aemeasurable_iSup_le_ofReal
      (fun t ↦ (hW.integrable_rpow_geometricBrownianMotion |s| μ σ
        (q * p.toReal) t).aestronglyMeasurable.aemeasurable) ?_
    filter_upwards [hcont] with ω hω t ht
    simp_rw [rpow_geometricBrownianMotion, exponentialMartingale_def]
    exact ((NNReal.continuous_coe.const_mul _).rexp.continuousWithinAt.const_mul _).mul
      (((hω t ht).const_mul _).sub
        ((NNReal.continuous_coe.const_mul _).div_const _).continuousWithinAt).rexp
  have hmax : ∫⁻ ω, M ω ∂P < ∞ :=
    hW.lintegral_iSup_rpow_geometricBrownianMotion_lt_top hcont |s| μ σ (q * p.toReal)
  let K : ℝ≥0∞ := ENNReal.ofReal |A| ^ p.toReal * 2 ^ p.toReal
  have hK : K < ∞ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg (by norm_num))
  refine uniformIntegrable_of_eNorm_rpow_le_of_lintegral_lt_top
    (G := fun ω ↦ K * (1 + M ω)) hp hp_top hV
    (aemeasurable_const.mul (aemeasurable_const.add hM)) ?_ ?_
  · -- Only the constant factor and the known maximal moment remain to be integrated.
    rw [lintegral_const_mul' _ _ hK.ne, lintegral_add_left measurable_const]
    exact ENNReal.mul_lt_top hK (ENNReal.add_lt_top.2 ⟨by simp, hmax⟩)
  -- Dominate each sampled value separately; no countability of the family is needed.
  · intro i
    filter_upwards [hτ i, hbound i] with ω ht hb
    have hS : 0 ≤ geometricBrownianMotion |s| μ σ W (τ i ω) ω := by
      rw [← abs_geometricBrownianMotion]
      exact abs_nonneg _
    have hb' : |V i ω| ≤ |A| *
        (1 + geometricBrownianMotion |s| μ σ W (τ i ω) ω ^ q) := by
      calc
        _ ≤ |A * (1 + geometricBrownianMotion s μ σ W (τ i ω) ω ^ q)| :=
          hb.trans (le_abs_self _)
        _ ≤ _ := by
          rw [abs_mul]
          gcongr
          refine (abs_add_le _ _).trans ?_
          simpa only [abs_one, abs_geometricBrownianMotion] using
            add_le_add_right (Real.abs_rpow_le_abs_rpow
              (geometricBrownianMotion s μ σ W (τ i ω) ω) q) 1
    have he : ‖V i ω‖ₑ ≤ ENNReal.ofReal |A| *
        (1 + ENNReal.ofReal (geometricBrownianMotion |s| μ σ W (τ i ω) ω ^ q)) := by
      simpa only [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg A),
        ENNReal.ofReal_add zero_le_one (rpow_nonneg hS q), ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal hb'
    calc
      _ ≤ (ENNReal.ofReal |A| *
          (1 + ENNReal.ofReal (geometricBrownianMotion |s| μ σ W (τ i ω) ω ^ q))) ^
            p.toReal := ENNReal.rpow_le_rpow he ENNReal.toReal_nonneg
      _ ≤ K * (1 + ENNReal.ofReal
          (geometricBrownianMotion |s| μ σ W (τ i ω) ω ^ (q * p.toReal))) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
          Real.rpow_mul hS, ← ENNReal.ofReal_rpow_of_nonneg (rpow_nonneg hS q)
            ENNReal.toReal_nonneg, mul_assoc]
        exact mul_le_mul_right (by
          simpa only [ENNReal.one_rpow] using
            ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow 1
              (ENNReal.ofReal (geometricBrownianMotion |s| μ σ W (τ i ω) ω ^ q))
              ENNReal.toReal_nonneg) _
      _ ≤ _ := by
        gcongr
        exact le_iSup₂ (f := fun t _ ↦ ENNReal.ofReal
          (geometricBrownianMotion |s| μ σ W t ω ^ (q * p.toReal))) (τ i ω) ht

/-- A polynomial-growth price with a continuous terminal extension converges in `Lᵖ`, for
`1 ≤ p < ∞`, along bounded random times tending almost surely to maturity. Continuity is needed
only at the terminal spot/time pair, within positive spot and the finite horizon. This includes
negative polynomial exponents and localization times that are not monotone. -/
theorem tendsto_eLpNorm_polynomialGrowth_geometricBrownianMotion
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    (hs : 0 < s) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {τ : ℕ → Ω → ℝ≥0} {C : ℝ → ℝ≥0 → ℝ}
    (hτ : ∀ n, ∀ᵐ ω ∂P, τ n ω ≤ T)
    (hτlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 T))
    (hC : ∀ n, AEStronglyMeasurable
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω)) P)
    (hbound : ∀ x > 0, ∀ t ≤ T, |C x t| ≤ A * (1 + x ^ q))
    (hterminal : ∀ᵐ ω ∂P, ContinuousWithinAt (fun p : ℝ × ℝ≥0 ↦ C p.1 p.2)
      (Ioi 0 ×ˢ Iic T) (geometricBrownianMotion s μ σ W T ω, T)) :
    Tendsto (fun n ↦ eLpNorm
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω) -
        C (geometricBrownianMotion s μ σ W T ω) T) p P) atTop (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hUI := hW.uniformIntegrable_polynomialGrowth_geometricBrownianMotion
    (hcont.mono fun ω hω t _ ↦ hω.continuousAt.continuousWithinAt) hp hp_top hC hτ
    (fun n ↦ (hτ n).mono fun ω ht ↦ hbound _
      (geometricBrownianMotion_pos hs μ σ W _ ω) _ ht)
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω)) atTop
      (𝓝 (C (geometricBrownianMotion s μ σ W T ω) T)) := by
    filter_upwards [hcont, hτlim, hterminal, ae_all_iff.2 hτ] with ω hω ht hCt hb
    have hS : Continuous (fun t ↦ geometricBrownianMotion s μ σ W t ω) := by
      simp_rw [geometricBrownianMotion_def]
      fun_prop
    have hp : Tendsto (fun n ↦ (geometricBrownianMotion s μ σ W (τ n ω) ω, τ n ω))
        atTop (𝓝[Ioi 0 ×ˢ Iic T] (geometricBrownianMotion s μ σ W T ω, T)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(hS.tendsto T |>.comp ht).prodMk_nhds ht, ?_⟩
      exact Eventually.of_forall fun n ↦
        ⟨geometricBrownianMotion_pos hs μ σ W _ ω, hb n⟩
    exact hCt.tendsto.comp hp
  exact tendsto_Lp_finite_of_tendsto_ae hp hp_top hC
    (hUI.memLp_of_ae_tendsto hlim) hUI.1 hlim

end TauCeti.Probability.IsFilteredPreBrownianReal
