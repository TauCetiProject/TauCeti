/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.UniformLimit

/-!
# Pathwise uniform approximation of the Brownian Itô integral

Against an almost surely continuous filtered pre-Brownian motion `W`, any family of
left-measurable simple holdings whose pathwise square-energy error on `(0, T]` converges to zero
in probability has elementary gains converging uniformly on `[0, T]` in outer probability to every
Itô integral `I` of `H`
(`TauCeti.Probability.IsItoIntegral.tendsto_measure_exists_le_norm_simpleGains_sub_gt`).

No `L²` construction of the Itô integral is used: the result rests on the pathwise maximal
energy estimate
`TauCeti.Probability.IsFilteredPreBrownianReal.tendsto_measure_exists_le_norm_simpleGains_sub_prod`,
extraction of an almost surely uniformly Cauchy subsequence
`TauCeti.exists_tendsto_uniformlyInMeasure_Iic_of_cauchy`, and identification of the continuous
limit with `I` via `TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains_of_le`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ}

/-- Extract an approximating sequence of simple holdings whose elementary gains have a subsequence
converging almost surely pointwise on `[0, T]` to the Itô integral `I`. -/
private theorem IsItoIntegral.exists_approx_subseq_tendsto_ae
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) (T : ℝ≥0) :
    ∃ (n₂ : ℕ → ℕ) (τ₂ : ℕ → ℕ → ℝ≥0) (a₂ : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ),
      (∀ m, MonotoneOn (τ₂ m) (Iic (n₂ m))) ∧
      (∀ m j, j < n₂ m → StronglyMeasurable[ℱ (τ₂ m j)] (a₂ m j)) ∧
      (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure T}) atTop (𝓝 0)) ∧
      Tendsto k atTop atTop ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, Tendsto (fun m ↦
        Finance.simpleGains (τ₂ (k m)) (n₂ (k m)) (a₂ (k m)) W t ω) atTop (𝓝 (I t ω)) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, _⟩ := hI.exists_approx T
  let G₂ (m : ℕ) := Finance.simpleGains (τ₂ m) (n₂ m) (a₂ m) W
  have hC (ε : ℝ) (hε : 0 < ε) (δ : ℝ≥0∞) (hδ : 0 < δ) : ∃ N, ∀ p ≥ N, ∀ q ≥ N,
      P {ω | ∃ t ≤ T, ε < ‖G₂ p t ω - G₂ q t ω‖} ≤ δ := by
    have hlim := hW.tendsto_measure_exists_le_norm_simpleGains_sub_prod hWc
      hI.isStronglyPredictable hτ₂ ha₂ hτ₂ ha₂ hE₂ hE₂ hε
    obtain ⟨U, hU, hUU⟩ := mem_prod_self_iff.1 (hlim (gt_mem_nhds hδ))
    obtain ⟨N, hN⟩ := mem_atTop_sets.1 hU
    exact ⟨N, fun p hp q hq ↦ by
      have hpq : (p, q) ∈ U ×ˢ U := ⟨hN p hp, hN q hq⟩
      exact (hUU hpq).le⟩
  obtain ⟨L, -, k, hk_mono, hL_ae⟩ := exists_tendsto_uniformlyInMeasure_Iic_of_cauchy
    (fun m ↦ hWc.mono fun _ hω ↦ (Finance.continuous_simpleGains hω).continuousOn) hC
  -- Identify the extracted continuous limit `L` with `I` on `[0, T]` via indistinguishability.
  have hW_meas : ∀ s, AEStronglyMeasurable (W s) P :=
    fun s ↦ ((hW.martingale.stronglyAdapted s).mono (ℱ.le s)).aestronglyMeasurable
  have hG₂_meas (m : ℕ) (s : ℝ≥0) : AEStronglyMeasurable (G₂ m s) P :=
    Finance.aestronglyMeasurable_simpleGains
      (fun j hj ↦ ((ha₂ m j hj).mono (ℱ.le _)).aestronglyMeasurable) fun _ _ ↦ hW_meas _
  have hLI : ProbabilityTheory.Indistinguishable P
      (fun (s : Iic T) ω ↦ L s ω) (fun (s : Iic T) ω ↦ I s ω) := by
    refine indist_of_forall_ae_eq
      (hL_ae.mono fun ω hω ↦ continuousOn_iff_continuous_domRestrict.1 hω.1)
      (hI.ae_continuous.mono fun ω hω ↦ hω.comp continuous_subtypeVal) fun s ↦ ?_
    have hlim_in : TendstoInMeasure P (fun m ↦ G₂ (k m) s) atTop (I s) :=
      (hI.tendstoInMeasure_simpleGains_of_le hW s.property hτ₂ ha₂ hE₂).comp
        hk_mono.tendsto_atTop
    have hae_L : ∀ᵐ ω ∂P, Tendsto (fun m ↦ G₂ (k m) s ω) atTop (𝓝 (L s ω)) :=
      hL_ae.mono fun ω hω ↦ hω.2.tendsto_at s.property
    exact (tendstoInMeasure_ae_unique hlim_in
      (tendstoInMeasure_of_tendsto_ae (fun m ↦ hG₂_meas _ s) hae_L)).symm
  refine ⟨n₂, τ₂, a₂, k, hτ₂, ha₂, hE₂, hk_mono.tendsto_atTop, ?_⟩
  filter_upwards [hL_ae, hLI] with ω ⟨_, hL_unif⟩ hω t htT
  exact hω ⟨t, htT⟩ ▸ hL_unif.tendsto_at htT

/-- **Finite-horizon uniform convergence of elementary gains in outer probability.** Against an
almost surely continuous filtered pre-Brownian motion `W`, any family of left-measurable simple
holdings converging to `H` in pathwise square energy in probability on `(0, T]` has elementary
gains converging uniformly on `[0, T]` in outer probability to every Itô integral `I` of `H`. -/
theorem IsItoIntegral.tendsto_measure_exists_le_norm_simpleGains_sub_gt
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {ι : Type*} {l : Filter ι} {T : ℝ≥0} {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun i ↦ P {ω | δ ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure T}) l (𝓝 0))
    {ε : ℝ≥0} (hε : 0 < ε) :
    Tendsto (fun i ↦ P {ω | ∃ t ≤ T,
      (ε : ℝ) < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖}) l (𝓝 0) := by
  obtain ⟨n₂, τ₂, a₂, k, hτ₂, ha₂, hE₂, hk, hlim_ae⟩ :=
    hI.exists_approx_subseq_tendsto_ae hW hWc T
  let G₂ (m : ℕ) := Finance.simpleGains (τ₂ m) (n₂ m) (a₂ m) W
  refine tendsto_uniformlyInMeasure_of_subseq_tendsto_ae (X := G₂) (ns := k) ?_ hk hlim_ae
  intro δ hδ
  have hlim := hW.tendsto_measure_exists_le_norm_simpleGains_sub_prod hWc
    hI.isStronglyPredictable hτ ha hτ₂ ha₂ hE hE₂ (half_pos (NNReal.coe_pos.2 hε))
  exact (ENNReal.tendsto_nhds_zero.1 hlim δ hδ).curry

end TauCeti.Probability
