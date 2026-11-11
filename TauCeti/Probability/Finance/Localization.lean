/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.PolynomialGrowth
public import TauCeti.MeasureTheory.Function.UniformIntegrable

/-!
# Removing localization for prices of linear or polynomial growth

A price with a uniform bound `|C(s,t)| ≤ A (1 + s^q)` along a positive geometric Brownian
stock converges in `L²` to its continuous terminal extension, when sampled at any sequence of
random times in a finite horizon tending almost surely to expiry. In particular, this permits
the removal of localization in square-integrable pricing identities, not just in expectations.
The exponent `q` may be any real number, since positive geometric Brownian motion has maximal
moments of negative orders as well. Mean-square convergence also implies `L¹` convergence on
the probability space.

The intermediate uniform-integrability result allows a countable family of different sampled
prices with a common growth bound. The linear-growth `L¹` result additionally permits a zero
initial stock price. The times need not be stopping times or even measurable: only the sampled
values must be almost everywhere strongly measurable. Continuity is required only at the
terminal spot/time pair. No stochastic integral or martingale property is inferred from these
moment and continuity assumptions.

The maximal-moment inputs are
`IsFilteredPreBrownianReal.lintegral_iSup_geometricBrownianMotion_lt_top` and
`IsFilteredPreBrownianReal.lintegral_iSup_sq_price_geometricBrownianMotion_lt_top`.

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

/-- Prices with a common linear-growth bound along geometric Brownian motion, sampled at a
countable family of random times bounded by `T`, are uniformly integrable. No stopping-time
hypothesis is needed, and the evaluated prices need only be almost everywhere measurable. -/
theorem uniformIntegrable_linearGrowth_geometricBrownianMotion {ι : Type*} [Countable ι]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (hs : 0 ≤ s) (hA : 0 ≤ A) {τ : ι → Ω → ℝ≥0} {V : ι → Ω → ℝ}
    (hV : ∀ i, AEStronglyMeasurable (V i) P)
    (hτ : ∀ i, ∀ᵐ ω ∂P, τ i ω ≤ T)
    (hbound : ∀ i, ∀ᵐ ω ∂P,
      |V i ω| ≤ A * (1 + geometricBrownianMotion s μ σ W (τ i ω) ω)) :
    UniformIntegrable V 1 P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  -- A countable supremum of the sampled prices is measurable, even if the uncountable
  -- running maximum of the raw Brownian version is not literally measurable.
  let G : Ω → ℝ≥0∞ := fun ω ↦ ⨆ i, ENNReal.ofReal |V i ω|
  have hdom : ∀ᵐ ω ∂P, G ω ≤ ENNReal.ofReal A *
      (1 + ⨆ t ≤ T, ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω)) := by
    filter_upwards [ae_all_iff.2 hτ, ae_all_iff.2 hbound] with ω ht hb
    refine iSup_le fun i ↦ ?_
    calc
      ENNReal.ofReal |V i ω| ≤ ENNReal.ofReal
          (A * (1 + geometricBrownianMotion s μ σ W (τ i ω) ω)) :=
        ENNReal.ofReal_le_ofReal (hb i)
      _ = ENNReal.ofReal A *
          (1 + ENNReal.ofReal (geometricBrownianMotion s μ σ W (τ i ω) ω)) := by
        rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_add zero_le_one]
        · simp
        · rw [geometricBrownianMotion_def]
          positivity
      _ ≤ _ := by
        gcongr
        exact le_iSup₂ (f := fun t _ ↦
          ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω)) (τ i ω) (ht i)
  have hGi : ∫⁻ ω, G ω ∂P < ∞ := by
    calc
      ∫⁻ ω, G ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal A *
          (1 + ⨆ t ≤ T, ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω)) ∂P :=
        lintegral_mono_ae hdom
      _ = ENNReal.ofReal A * ∫⁻ ω,
          (1 + ⨆ t ≤ T, ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω)) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal A * ((∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P) +
          ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω) ∂P) := by
        rw [lintegral_add_left measurable_const]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨by simp,
          hW.lintegral_iSup_geometricBrownianMotion_lt_top hcont s μ σ⟩)
  apply uniformIntegrable_of_lintegral_iSup_enorm_rpow_lt_top le_rfl ENNReal.one_ne_top hV
  simpa only [ENNReal.toReal_one, ENNReal.rpow_one, Real.enorm_eq_ofReal_abs] using hGi

/-- A common polynomial-growth bound along positive geometric Brownian motion gives uniform
`L²` integrability at any countable family of bounded random times. Negative growth exponents
are allowed; no stopping-time or measurability assumption on the times themselves is needed. -/
theorem uniformIntegrable_polynomialGrowth_geometricBrownianMotion {ι : Type*} [Countable ι]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (hs : 0 < s) {τ : ι → Ω → ℝ≥0} {V : ι → Ω → ℝ}
    (hV : ∀ i, AEStronglyMeasurable (V i) P)
    (hτ : ∀ i, ∀ᵐ ω ∂P, τ i ω ≤ T)
    (hbound : ∀ i, ∀ᵐ ω ∂P,
      |V i ω| ≤ A * (1 + geometricBrownianMotion s μ σ W (τ i ω) ω ^ q)) :
    UniformIntegrable V 2 P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  -- The countable supremum is measurable even for raw versions of the driving process.
  let G : Ω → ℝ≥0∞ := fun ω ↦ ⨆ i, ENNReal.ofReal (V i ω ^ 2)
  have hmax := hW.lintegral_iSup_sq_price_geometricBrownianMotion_lt_top
    (C := fun x _ ↦ |A| * (1 + x ^ q)) hcont hs μ σ q
    (fun x hx _ _ ↦ by rw [abs_of_nonneg (by positivity)])
  have hGi : ∫⁻ ω, G ω ∂P < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hmax
    filter_upwards [ae_all_iff.2 hτ, ae_all_iff.2 hbound] with ω ht hb
    refine iSup_le fun i ↦ ?_
    have hpos := geometricBrownianMotion_pos hs μ σ W (τ i ω) ω
    have hb' : |V i ω| ≤ |A| *
        (1 + geometricBrownianMotion s μ σ W (τ i ω) ω ^ q) :=
      (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hb'
    rw [sq_abs] at hsq
    exact (ENNReal.ofReal_le_ofReal hsq).trans
      (le_iSup₂ (f := fun t _ ↦ ENNReal.ofReal
        ((|A| * (1 + geometricBrownianMotion s μ σ W t ω ^ q)) ^ 2)) (τ i ω) (ht i))
  apply uniformIntegrable_of_lintegral_iSup_enorm_rpow_lt_top (by norm_num) (by norm_num) hV
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using hGi

/-- A polynomial-growth price with a continuous terminal extension converges in mean square
along bounded random times tending almost surely to maturity. Continuity is needed only at the
terminal spot/time pair, within positive spot and the finite horizon. This includes negative
polynomial exponents and localization times that are not monotone. -/
theorem tendsto_eLpNorm_polynomialGrowth_geometricBrownianMotion
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    (hs : 0 < s) {τ : ℕ → Ω → ℝ≥0} {C : ℝ → ℝ≥0 → ℝ}
    (hτ : ∀ n, ∀ᵐ ω ∂P, τ n ω ≤ T)
    (hτlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 T))
    (hC : ∀ n, AEStronglyMeasurable
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω)) P)
    (hbound : ∀ x > 0, ∀ t ≤ T, |C x t| ≤ A * (1 + x ^ q))
    (hterminal : ∀ᵐ ω ∂P, ContinuousWithinAt (fun p : ℝ × ℝ≥0 ↦ C p.1 p.2)
      (Ioi 0 ×ˢ Iic T) (geometricBrownianMotion s μ σ W T ω, T)) :
    Tendsto (fun n ↦ eLpNorm
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω) -
        C (geometricBrownianMotion s μ σ W T ω) T) 2 P) atTop (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hUI := hW.uniformIntegrable_polynomialGrowth_geometricBrownianMotion
    (hcont.mono fun ω hω t _ ↦ hω.continuousAt.continuousWithinAt) hs hC hτ
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
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hC
    (hUI.memLp_of_ae_tendsto hlim) hUI.1 hlim

end TauCeti.Probability.IsFilteredPreBrownianReal
