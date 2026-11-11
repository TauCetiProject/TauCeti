/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.RunningMaximum
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Removing localization for prices of linear growth

A price bounded in absolute value by `A (1 + s)` along geometric Brownian motion is
uniformly integrable when evaluated at any countable family of random times in a fixed
finite horizon. The times need not be stopping times: only measurability of the evaluated
prices is needed. This includes the stopped prices appearing in localized pricing identities.

If these times converge to maturity, continuity of the price up to maturity gives convergence
in L¹ to its terminal value. Thus expectations in a stopped identity can be passed to the
limit without imposing boundedness of the price or of the stock. These results do not assert
an Itô identity, self-financing, or the martingale property of an arbitrary candidate price.

The maximal-moment input is
`TauCeti.Probability.IsFilteredPreBrownianReal.lintegral_iSup_geometricBrownianMotion_lt_top`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §6.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {s μ σ A : ℝ} {T : ℝ≥0}

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
  have hG : AEMeasurable G P := AEMeasurable.iSup fun i ↦
    (hV i).norm.aemeasurable.ennreal_ofReal
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
  have hGiR : Integrable (fun ω ↦ (G ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hG hGi.ne
  have hle (i : ι) : ∀ᵐ ω ∂P, ‖V i ω‖ₑ ≤ ‖(G ω).toReal‖ₑ := by
    filter_upwards [ae_lt_top' hG hGi.ne] with ω hω
    simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
    exact le_iSup (fun i ↦ ENNReal.ofReal |V i ω|) i
  have hUI : UniformIntegrable (fun _ : ι ↦ fun ω ↦ (G ω).toReal) 1 P :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_one_iff_integrable.2 hGiR)
  refine ⟨hUI.1.ae_mono hV hle, ?_⟩
  obtain ⟨C, hC⟩ := hUI.2
  exact ⟨C, fun i ↦ (eLpNorm_mono_enorm_ae (hV i) (hle i)).trans (hC i)⟩

/-- A continuous terminal extension of a linear-growth price converges in L¹ along bounded
random times tending almost surely to maturity. Continuity is required only at the terminal
stock/time pair on almost every path, within positive spot and the declared finite horizon.
This applies in particular to localized prices once their sampling times exhaust the horizon. -/
theorem tendsto_eLpNorm_linearGrowth_geometricBrownianMotion
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    (hs : 0 < s) (hA : 0 ≤ A) {τ : ℕ → Ω → ℝ≥0} {C : ℝ → ℝ≥0 → ℝ}
    (hτ : ∀ n, ∀ᵐ ω ∂P, τ n ω ≤ T)
    (hτlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 T))
    (hC : ∀ n, AEStronglyMeasurable
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω)) P)
    (hbound : ∀ x > 0, ∀ t ≤ T, |C x t| ≤ A * (1 + x))
    (hterminal : ∀ᵐ ω ∂P, ContinuousWithinAt (fun p : ℝ × ℝ≥0 ↦ C p.1 p.2)
      (Ioi 0 ×ˢ Iic T) (geometricBrownianMotion s μ σ W T ω, T)) :
    Tendsto (fun n ↦ eLpNorm
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ n ω) ω) (τ n ω) -
        C (geometricBrownianMotion s μ σ W T ω) T) 1 P) atTop (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hUI := hW.uniformIntegrable_linearGrowth_geometricBrownianMotion
    (hcont.mono fun ω hω t _ ↦ hω.continuousAt.continuousWithinAt) hs.le hA hC hτ
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
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hC
    (hUI.memLp_of_ae_tendsto hlim) hUI.1 hlim

end TauCeti.Probability.IsFilteredPreBrownianReal
