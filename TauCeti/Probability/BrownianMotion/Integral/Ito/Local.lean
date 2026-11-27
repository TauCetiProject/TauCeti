/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.Predictable.Basic
import TauCeti.Probability.Process.UniformLimit

/-!
# Itô integrals of locally square-integrable integrands

Against a pre-Brownian motion `W` relative to a filtration with almost surely continuous paths,
a predictable integrand has an Itô integral exactly when its pathwise square energy is finite on
every finite horizon outside one null set (`TauCeti.LocallyBrownianIntegrable`). No moment
assumption and no usual conditions on the filtration are needed.

* `TauCeti.LocallyBrownianIntegrable.exists_seq_simpleHolding_tendsto`: one sequence of bounded
  simple holdings, with heights known at the left endpoints of their intervals, approximates a
  locally Brownian-integrable integrand in square energy in probability on every finite horizon.
* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`: such an integrand has a predictable
  Itô integral.
* `TauCeti.Probability.IsItoIntegral.locallyBrownianIntegrable`: conversely, every integrand
  with an Itô integral is locally Brownian-integrable; together,
  `TauCeti.Probability.exists_isItoIntegral_iff_locallyBrownianIntegrable`.
* `TauCeti.Probability.IsItoIntegral.tendsto_measure_exists_le_abs_simpleGains_sub_gt`: the
  elementary integral processes of any simple holdings approximating the integrand on `(0,T]`
  converge to the Itô integral uniformly on `[0,T]` in outer probability.

The approximants are obtained by approximating, in `L²`, the integrand cut off when its
accumulated square energy reaches a level (`MeasureTheory.Measure.energyLocalizer`), and letting
the level and the horizon grow. The uniform energy estimate on a horizon
(`TauCeti.Probability.IsFilteredPreBrownianReal.measure_exists_le_abs_simpleGains_gt_le`) makes
their elementary integral processes uniformly Cauchy in probability on every finite horizon, so a
continuous adapted limit can be selected on the original filtration
(`TauCeti.Probability.exists_stronglyAdapted_tendsto_uniformlyInMeasure_of_cauchy`) and then
replaced by an indistinguishable predictable process. Whether this integral is a local martingale
is not addressed here.

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

/-- The integrand cut off when its accumulated square energy reaches the levels `k + 1`
approximates a locally Brownian-integrable integrand in square energy in probability on every
finite horizon. -/
private theorem _root_.TauCeti.LocallyBrownianIntegrable.tendsto_measure_le_lintegral_sub_ite
    [IsFiniteMeasure P] (hH : LocallyBrownianIntegrable ℱ P H) (t : ℝ≥0) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    Tendsto (fun k : ℕ ↦ P {ω | ε ≤ ∫⁻ s, ‖H s ω - (if (s : WithTop ℝ≥0) ≤
      nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then nnvolume.finiteEnergyCutoff H s ω
        else 0)‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  have hmeas (k : ℕ) : MeasurableSet {ω | ε ≤ ∫⁻ s, ‖H s ω - (if (s : WithTop ℝ≥0) ≤
      nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then nnvolume.finiteEnergyCutoff H s ω
        else 0)‖ₑ ^ 2 ∂timeMeasure t} :=
    measurableSet_le measurable_const (((hH.isStronglyPredictable.sub
      (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P)
        ((k : ℝ≥0) + 1)).isStronglyPredictable).mono
          ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).lintegral_prod_left'
  -- On each sample of a full event the cutoffs eventually agree with the integrand up to `t`.
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    MeasurableSet.empty hmeas (by
      filter_upwards [hH.ae_eventually_ite_le_energyLocalizer_eqOn] with ω hω
      filter_upwards [hω t] with k hk
      have h0 : ∫⁻ s, ‖H s ω - (if (s : WithTop ℝ≥0) ≤
          nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then nnvolume.finiteEnergyCutoff H s ω
            else 0)‖ₑ ^ 2 ∂timeMeasure t = ∫⁻ _, 0 ∂timeMeasure t := by
        refine lintegral_congr_ae ?_
        rw [timeMeasure_def]
        refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ ?_
        have hks := hk (mem_Iic.mpr hs.2)
        simp only at hks
        beta_reduce
        rw [hks, sub_self]
        simp
      simp only [mem_empty_iff_false, iff_false, not_le, h0, lintegral_zero]
      exact hε)
  simpa only [measure_empty] using hlim

/-- **Simple approximation of locally Brownian-integrable integrands.** One sequence of bounded
simple holdings, with heights known at the left endpoints of their intervals, approximates a
predictable integrand with finite pathwise square energy on every finite horizon, in square
energy in probability on every finite horizon. No moment assumption on the integrand is
needed. -/
theorem _root_.TauCeti.LocallyBrownianIntegrable.exists_seq_simpleHolding_tendsto
    [IsFiniteMeasure P] (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      ∀ (t : ℝ≥0) (ε : ℝ≥0∞), 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0) := by
  -- Approximate the `k`-th cutoff on the horizon `k`, with accuracy and error probability `1/k`.
  have hstep (k : ℕ) : ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (C : ℝ),
      MonotoneOn τ (Iic n) ∧ (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) ∧
      P {ω | (k : ℝ≥0∞)⁻¹ ≤ ∫⁻ s, ‖Finance.simpleHolding τ n a s ω - (if (s : WithTop ℝ≥0) ≤
        nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then nnvolume.finiteEnergyCutoff H s ω
          else 0)‖ₑ ^ 2 ∂timeMeasure k} ≤ (k : ℝ≥0∞)⁻¹ := by
    have hc := hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P)
      ((k : ℝ≥0) + 1)
    obtain ⟨n, τ, a, C, -, hτ, ha, haC, hlim⟩ := hc.exists_seq_simpleHolding_tendsto_eLpNorm
    have hpos : (0 : ℝ≥0∞) < (k : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k)
    have hP := tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm
      (fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
        hc.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (hlim k) hpos
    obtain ⟨m, hm⟩ := ((tendsto_order.1 hP).2 _ hpos).exists
    exact ⟨n m, τ m, a m, C m, (hτ m).monotoneOn, ha m, haC m, hm.le⟩
  choose n τ a C hτ ha haC hP using hstep
  refine ⟨n, τ, a, C, hτ, ha, haC, fun t ε hε ↦ ?_⟩
  -- The errors to the cutoffs vanish in probability on every fixed horizon.
  have hKc (δ : ℝ≥0∞) (hδ : 0 < δ) : Tendsto (fun k ↦ P {ω | δ ≤ ∫⁻ s,
      ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - (if (s : WithTop ℝ≥0) ≤
        nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then nnvolume.finiteEnergyCutoff H s ω
          else 0)‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [eventually_ge_atTop ⌈t⌉₊,
      (tendsto_order.1 ENNReal.tendsto_inv_nat_nhds_zero).2 δ hδ] with k hk hkδ
    refine (measure_mono fun ω hω ↦ ?_).trans (hP k)
    simp only [mem_ofPred_eq] at hω ⊢
    exact hkδ.le.trans (hω.trans (lintegral_mono' (timeMeasure_mono
      ((Nat.le_ceil t).trans (by exact_mod_cast hk))) le_rfl))
  exact tendsto_measure_le_lintegral_enorm_sub_sq
    (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
    (fun k ↦ (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P)
      ((k : ℝ≥0) + 1)).isStronglyPredictable)
    t hKc (fun δ hδ ↦ hH.tendsto_measure_le_lintegral_sub_ite t hδ) ε hε

/-- Two sequences of simple holdings approximating the same predictable integrand on `(0,T]` in
square energy in probability have elementary integral processes which are uniformly close on
`[0,T]` in outer probability. -/
private theorem tendsto_measure_exists_le_abs_simpleGains_sub_simpleGains_gt
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hH : IsStronglyPredictable ℱ H) {ι : Type*} {l : Filter ι} {n m : ι → ℕ}
    {τ σ : ι → ℕ → ℝ≥0} {a b : ι → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k))) (hσ : ∀ k, MonotoneOn (σ k) (Iic (m k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j))
    (hb : ∀ k j, j < m k → StronglyMeasurable[ℱ (σ k j)] (b k j)) (T : ℝ≥0)
    (hKH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
        l (𝓝 0))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
        l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ∃ t ≤ T, ε < |Finance.simpleGains (τ k) (n k) (a k) W t ω -
      Finance.simpleGains (σ k) (m k) (b k) W t ω|}) l (𝓝 0) := by
  choose N ρ c _ hρ hc hhold hgain using fun k ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ k) (hσ k) (ha k) (hb k)
  have henergy (δ : ℝ≥0∞) (hδ : 0 < δ) : Tendsto (fun k ↦ P {ω | δ ≤
      ∫⁻ s, ‖Finance.simpleHolding (ρ k) (N k) (c k) s ω‖ₑ ^ 2 ∂timeMeasure T}) l (𝓝 0) := by
    simp_rw [hhold]
    exact tendsto_measure_le_lintegral_enorm_sub_sq
      (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k)) (fun _ ↦ hH) T hKH hLH δ hδ
  simpa only [hgain] using hW.tendsto_measure_exists_le_abs_simpleGains_gt_of_energy hWc
    (fun k ↦ (hρ k).monotoneOn) hc T henergy hε

/-- A locally Brownian-integrable integrand has an adapted Itô integral which is the uniform limit
in outer probability, on every finite horizon, of the elementary integral processes of one
approximating sequence of simple holdings. -/
private theorem _root_.TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral_tendsto
    (hH : LocallyBrownianIntegrable ℱ P H) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ (t : ℝ≥0) (ε : ℝ≥0∞), 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0)) ∧
      IsItoIntegral ℱ P W H Y ∧ StronglyAdapted ℱ Y ∧
      ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε → Tendsto (fun k ↦ P {ω | ∃ t ≤ T,
        ε < |Finance.simpleGains (τ k) (n k) (a k) W t ω - Y t ω|}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hτ, ha, -, hKH⟩ := hH.exists_seq_simpleHolding_tendsto
  -- The elementary integral processes are uniformly Cauchy in probability on every horizon.
  have hC (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (δ : ℝ≥0∞) (hδ : 0 < δ) : ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N,
      P {ω | ∃ t ≤ T, ε < ‖Finance.simpleGains (τ k) (n k) (a k) W t ω -
        Finance.simpleGains (τ j) (n j) (a j) W t ω‖} ≤ δ := by
    have h := tendsto_measure_exists_le_abs_simpleGains_sub_simpleGains_gt hW hWc
      hH.isStronglyPredictable
      (l := atTop ×ˢ atTop) (fun p ↦ hτ p.1) (fun p ↦ hτ p.2) (fun p ↦ ha p.1)
      (fun p ↦ ha p.2) T (fun δ hδ ↦ (hKH T δ hδ).comp tendsto_fst)
      (fun δ hδ ↦ (hKH T δ hδ).comp tendsto_snd) hε
    have hev := ENNReal.tendsto_nhds_zero.1 h δ hδ
    rw [prod_atTop_atTop_eq] at hev
    simpa only [Real.norm_eq_abs] using eventually_atTop_prod_self'.1 hev
  obtain ⟨Y, hY, hYlim, ns, -, hYc⟩ := exists_stronglyAdapted_tendsto_uniformlyInMeasure_of_cauchy
    (fun k ↦ Finance.stronglyAdapted_simpleGains (hτ k) (ha k) hW.adapted.stronglyAdapted)
    (fun k ↦ hWc.mono fun ω hω ↦ Finance.continuous_simpleGains hω) hC
  -- Uniform convergence in probability gives convergence in probability at each time.
  have hYt (t : ℝ≥0) : TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t)
      atTop (Y t) := by
    refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hYlim t (ε / 2) (half_pos hε)) (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ ?_
    simp only [mem_ofPred_eq] at hω ⊢
    exact ⟨t, le_rfl, (half_lt_self hε).trans_le hω⟩
  refine ⟨n, τ, a, Y, hτ, ha, hKH, ⟨hH.isStronglyPredictable, hYc.mono fun ω hω ↦ hω.1,
    fun t ↦ ⟨n, τ, a, hτ, ha, hKH t, hYt t⟩⟩, hY, fun T ε hε ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using hYlim T ε hε

/-- **Existence of the Itô integral.** Against a pre-Brownian motion relative to the filtration
with almost surely continuous paths, every predictable integrand with finite pathwise square
energy on every finite horizon has a predictable Itô integral. Neither moments of the integrand
nor usual conditions on the filtration are assumed. -/
theorem _root_.TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral
    (hH : LocallyBrownianIntegrable ℱ P H) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ I, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I := by
  obtain ⟨-, -, -, Y, -, -, -, hY, hYa, -⟩ := hH.exists_isItoIntegral_tendsto hW hWc
  obtain ⟨I, hI, hIY⟩ := hYa.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
    (hY.ae_continuous.mono fun ω hω ↦ hω.isLeftContinuous)
  exact ⟨I, hY.congr hIY.symm, hI⟩

/-- Every integrand with an Itô integral has finite pathwise square energy on every finite
horizon outside one null set: approximating simple holdings have finite energy, and their errors
have finite energy outside events of vanishing probability. No assumption on the integrator or
the measure is needed. -/
theorem IsItoIntegral.locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun N ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hE, -⟩ := hI.exists_approx N
  have hnull : P {ω | ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure N = ∞} = 0 := by
    refine le_antisymm (ge_of_tendsto' (hE 1 one_pos) fun k ↦ measure_mono fun ω hω ↦ ?_) bot_le
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra hlt
    rw [not_le] at hlt
    have hK : ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2 ∂timeMeasure N < ∞ := by
      rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (hτ k)]
      exact ENNReal.sum_lt_top.2 fun j _ ↦ ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top
    have hrev : ∫⁻ s, ‖H s ω - Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2 ∂timeMeasure N =
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure N :=
      lintegral_congr fun s ↦ by rw [eNorm_sub_rev]
    have hmeas : AEMeasurable (fun s ↦ ‖H s ω - Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2)
        (timeMeasure N) :=
      ((((hI.isStronglyPredictable.sub (Finance.isStronglyPredictable_simpleHolding (ha k))).mono
        ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).comp
          (measurable_id.prodMk measurable_const)).aemeasurable
    have hle := lintegral_enorm_sub_sq_le_two_mul (f := fun s ↦ H s ω) (g := fun _ ↦ 0)
      (h := fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) hmeas
    simp only [sub_zero, zero_sub, eNorm_neg, hrev, hω] at hle
    exact (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2 ⟨hlt.trans ENNReal.one_lt_top,
      hK⟩)).not_ge hle
  have hmeasure : (volume.restrict (Ioc 0 (N : ℝ))).comap ((↑) : ℝ≥0 → ℝ) = timeMeasure N := by
    rw [← NNReal.coe_natCast N, NNReal.comap_volume_restrict_Ioc, timeMeasure_def]
  rw [hmeasure]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
  have hpath : AEStronglyMeasurable (fun t ↦ H t ω) (timeMeasure N) :=
    ((hI.isStronglyPredictable.mono ℱ.predictable_le_prod).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  rw [hpath.memLp_two_iff_lintegral_enorm_sq_lt_top]
  exact lt_top_iff_ne_top.2 (by simpa using hω)

/-- Against a pre-Brownian motion relative to the filtration with almost surely continuous paths,
a predictable integrand has an Itô integral exactly when it has finite pathwise square energy on
every finite horizon outside one null set. -/
theorem exists_isItoIntegral_iff_locallyBrownianIntegrable (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    (∃ I, IsItoIntegral ℱ P W H I) ↔ LocallyBrownianIntegrable ℱ P H :=
  ⟨fun ⟨_, hI⟩ ↦ hI.locallyBrownianIntegrable,
    fun hH ↦ (hH.exists_isItoIntegral hW hWc).imp fun _ h ↦ h.1⟩

/-- **Uniform approximation of the Itô integral.** Against a pre-Brownian motion relative to the
filtration with almost surely continuous paths, if simple holdings with heights known at the left
endpoints of their intervals approximate the integrand on `(0,T]` in square energy in probability,
then their elementary integral processes converge to the Itô integral uniformly on `[0,T]` in
outer probability. -/
theorem IsItoIntegral.tendsto_measure_exists_le_abs_simpleGains_sub_gt
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hI : IsItoIntegral ℱ P W H I) {T : ℝ≥0} {m : ℕ → ℕ} {σ : ℕ → ℕ → ℝ≥0}
    {b : ℕ → ℕ → Ω → ℝ} (hσ : ∀ k, MonotoneOn (σ k) (Iic (m k)))
    (hb : ∀ k j, j < m k → StronglyMeasurable[ℱ (σ k j)] (b k j))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
        atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ∃ t ≤ T,
      ε < |Finance.simpleGains (σ k) (m k) (b k) W t ω - I t ω|}) atTop (𝓝 0) := by
  -- Compare with the approximants constructed for the existence theorem.
  obtain ⟨n, τ, a, Y, hτ, ha, hKH, hY, -, hYlim⟩ :=
    hI.locallyBrownianIntegrable.exists_isItoIntegral_tendsto hW hWc
  have hLK := tendsto_measure_exists_le_abs_simpleGains_sub_simpleGains_gt hW hWc
    hI.isStronglyPredictable hσ hτ hb ha T hLH (hKH T) (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hLK.add (hYlim T _ (half_pos hε))) (fun _ ↦ zero_le)
    fun k ↦ (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [isItoIntegral_unique hW hI hY] with ω hω hbad
  obtain ⟨t, ht, hgt⟩ := hbad
  rw [hω t] at hgt
  by_cases h₁ : ε / 2 < |Finance.simpleGains (σ k) (m k) (b k) W t ω -
      Finance.simpleGains (τ k) (n k) (a k) W t ω|
  · exact Or.inl ⟨t, ht, h₁⟩
  · refine Or.inr ⟨t, ht, ?_⟩
    have := abs_sub_le (Finance.simpleGains (σ k) (m k) (b k) W t ω)
      (Finance.simpleGains (τ k) (n k) (a k) W t ω) (Y t ω)
    linarith [not_lt.mp h₁]

end TauCeti.Probability
