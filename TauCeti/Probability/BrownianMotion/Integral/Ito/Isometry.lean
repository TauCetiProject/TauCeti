/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W`, identifies it with the terminal `L²` integral
`TauCeti.Probability.IsFilteredPreBrownianReal.l2Integral`, and proves the Itô isometry.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral_approx` and
  `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale, approximated simultaneously on every
  finite horizon by one sequence of bounded simple strategies in `L²`, uniformly in probability on
  `[0, T]`, and along a subsequence a.s. uniformly on `[0, T]`.
* `TauCeti.Probability.IsItoIntegral.ae_eq_l2Integral`,
  `TauCeti.Probability.IsItoIntegral.toLp_eq_l2Integral`, and
  `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_iff_ae_eq_l2Integral`: every Itô
  integral of `H` agrees almost surely (and in `L²(P)`) at each horizon `T` with
  `hW.l2Integral T`, characterizing `IsItoIntegral` for `BrownianIntegrable` integrands.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq`,
  `TauCeti.Probability.IsItoIntegral.integral_sq`, `eLpNorm_sub_eq`,
  `eLpNorm_simpleGains_sub_eq`, `integral_mul`, `integral_sub_sq`: `L²(P)` membership, the Itô
  isometry (in `L²` norm, Bochner square, polarized, `(s, t]`-increment, and elementary-strategy
  comparison forms).

The integral is the limit of the elementary integrals of bounded simple holdings approximating
`H` in `L²` of the trimmed predictable measure on every finite horizon, identified via
`hW.l2Integral`. Their elementary integrals converge in `L²(P)` at every time to `hW.l2Integral`,
and, when `W` has continuous paths, `MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp`
selects a predictable version with almost surely continuous paths and uniform approximation on
compact horizons. Any Itô integral agrees almost surely at each time with `hW.l2Integral` by
`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`, which yields the isometry and,
combined with `MeasureTheory.exists_martingale_of_cauchySeq_Lp` for an adapted limit, the
martingale property.

Neither usual conditions on the filtration nor path continuity of `W` are needed for the
isometry, `l2Integral` identification, and martingale property; only existence uses continuous
paths. Adaptedness is needed for the martingale property because an Itô integral is determined
only up to indistinguishability, and an arbitrary indistinguishable version need not be adapted to
a raw filtration.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B (Proposition 3.2.10) and §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ}

private structure ItoIntegralApprox {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W H : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) where
  I : ℝ≥0 → Ω → ℝ
  approx : SimpleHoldingApprox ℱ P W H hW hH
  isItoIntegral : IsItoIntegral ℱ P W H I
  isStronglyPredictable : IsStronglyPredictable ℱ I
  martingale : Martingale I ℱ P
  tendsto_l2_gains : ∀ T : ℝ≥0, Tendsto (fun m ↦
    eLpNorm (Finance.simpleGains (approx.τ m) (approx.n m) (approx.a m) W T - I T) 2 P)
      atTop (𝓝 0)
  tendsto_unif_inMeasure : ∀ (T : ℝ≥0) (ε : ℝ≥0), 0 < ε → Tendsto (fun m ↦ P {ω | ∃ t ≤ T,
    (ε : ℝ) < ‖Finance.simpleGains (approx.τ m) (approx.n m) (approx.a m) W t ω - I t ω‖})
      atTop (𝓝 0)
  subseq : ℕ → ℕ
  strictMono_subseq : StrictMono subseq
  ae_tendstoUniformlyOn : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, TendstoUniformlyOn (fun m t ↦
    Finance.simpleGains (approx.τ (subseq m)) (approx.n (subseq m))
      (approx.a (subseq m)) W t ω) (fun t ↦ I t ω) atTop (Iic T)

private theorem exists_itoIntegralApprox
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    Nonempty (ItoIntegralApprox ℱ P W H hW hH) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨h⟩ := hW.exists_simpleHoldingApprox hH
  obtain ⟨I, hIm, hIp, hIlim, hIunif, φ, hφ, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp h.martingale
      (fun m ↦ hcont.mono fun _ hω ↦ by
        simpa only [← h.simpleGains_eq_integral m] using Finance.continuous_simpleGains hω)
      h.memLp fun T ↦ (h.tendsto_l2Integral T).cauchySeq
  have hIto : IsItoIntegral ℱ P W H I :=
    ⟨hH.isStronglyPredictable, hIpath.mono fun _ hpath ↦ hpath.1, fun t ↦
      ⟨h.n, h.τ, h.a, fun m ↦ (h.strictMonoOn m).monotoneOn, h.stronglyMeasurable,
        fun ε hε ↦ by simpa only [h.simpleHolding_eq_toProcess] using h.tendsto_energy t ε hε,
        tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
          (by simpa only [h.simpleGains_eq_integral] using (hIlim t).2)⟩⟩
  exact ⟨⟨I, h, hIto, hIp, hIm, fun T ↦ by simpa only [h.simpleGains_eq_integral] using (hIlim T).2,
    fun T ε hε ↦ by simpa only [h.simpleGains_eq_integral] using hIunif T ε hε,
    φ, hφ, hIpath.mono fun _ hpath ↦ by
      simpa only [h.simpleGains_eq_integral] using hpath.2⟩⟩

/-- **Existence and uniform approximation of the `L²` Brownian Itô integral**: every
`BrownianIntegrable` integrand against a filtered pre-Brownian motion `W` with a.s. continuous
paths admits a predictable continuous martingale Itô integral on the raw filtration, approximated
simultaneously on every finite horizon by one sequence of bounded simple strategies in `L²`,
uniformly in probability on `[0, T]`, and along a subsequence a.s. uniformly on `[0, T]`. -/
theorem _root_.TauCeti.BrownianIntegrable.exists_isItoIntegral_approx
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ m, τ m 0 = 0) ∧
      (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      (∀ T : ℝ≥0, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      (∀ T : ℝ≥0, Tendsto (fun m ↦
        eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T - I T) 2 P) atTop (𝓝 0)) ∧
      (∀ (T : ℝ≥0) (ε : ℝ≥0), 0 < ε → Tendsto (fun m ↦
        P {ω | ∃ t ≤ T, (ε : ℝ) < ‖Finance.simpleGains (τ m) (n m) (a m) W t ω - I t ω‖})
          atTop (𝓝 0)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun m t ↦ Finance.simpleGains (τ (φ m)) (n (φ m)) (a (φ m)) W t ω)
          (fun t ↦ I t ω) atTop (Iic T) := by
  obtain ⟨h⟩ := exists_itoIntegralApprox hW hcont hH
  exact ⟨h.I, h.approx.n, h.approx.τ, h.approx.a, h.approx.C, h.isItoIntegral,
    h.isStronglyPredictable, h.martingale, h.approx.tau_zero, h.approx.strictMonoOn,
    h.approx.stronglyMeasurable, h.approx.norm_le,
    fun T ↦ by simpa only [h.approx.simpleHolding_eq_toProcess] using h.approx.tendsto_holding T,
    h.tendsto_l2_gains, h.tendsto_unif_inMeasure, h.subseq, h.strictMono_subseq,
    h.ae_tendstoUniformlyOn⟩

/-- **Existence of the Itô integral for square-integrable integrands.** Against a pre-Brownian
motion relative to the filtration with almost surely continuous paths, every predictable
integrand with finite expected square energy on every finite horizon has an Itô integral which
is a predictable martingale. No usual conditions on the filtration are assumed. -/
theorem _root_.TauCeti.BrownianIntegrable.exists_isItoIntegral (hH : BrownianIntegrable ℱ P H)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ I, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  obtain ⟨h⟩ := exists_itoIntegralApprox hW hWc hH
  exact ⟨h.I, h.isItoIntegral, h.isStronglyPredictable, h.martingale⟩

/-- Every Itô integral of a `BrownianIntegrable` integrand agrees `P`-a.s. at horizon `T`
with `hW.l2Integral T`, without assuming path continuity of `W`. -/
theorem IsItoIntegral.ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨h⟩ := hW.exists_simpleHoldingApprox hH
  exact hI.ae_eq_of_tendstoInMeasure hW (fun m ↦ (h.strictMonoOn m).monotoneOn)
    h.stronglyMeasurable
    (fun ε hε ↦ by simpa only [h.simpleHolding_eq_toProcess] using h.tendsto_energy T ε hε)
    (by simpa only [h.simpleGains_eq_integral] using h.tendstoInMeasure_l2Integral T)

/-- **L² characterization of Itô integrals.** For a Brownian-integrable integrand `H`, an almost
surely continuous process `I` is an Itô integral of `H` if and only if `I T` agrees almost surely
with the terminal `L²` integral `hW.l2Integral T` at every horizon `T`. Path continuity of `W` is
not required. -/
theorem IsFilteredPreBrownianReal.isItoIntegral_iff_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) :
    IsItoIntegral ℱ P W H I ↔
      ∀ T : ℝ≥0, I T =ᵐ[P]
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  refine ⟨fun hI T ↦ hI.ae_eq_l2Integral hW hH T, fun hT ↦ ?_⟩
  obtain ⟨h⟩ := hW.exists_simpleHoldingApprox hH
  refine ⟨hH.isStronglyPredictable, hIcont, fun T ↦
    ⟨h.n, h.τ, h.a, fun m ↦ (h.strictMonoOn m).monotoneOn, h.stronglyMeasurable,
      fun ε hε ↦ by simpa only [h.simpleHolding_eq_toProcess] using h.tendsto_energy T ε hε,
      by simpa only [h.simpleGains_eq_integral] using
        (h.tendstoInMeasure_l2Integral T).congr_right (hT T).symm⟩⟩

/-- **The martingale property of the Itô integral.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral of a Brownian-integrable integrand is a martingale.
Neither path continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  obtain ⟨-, -, -, Z, -, -, -, -, hZ, -, -, hZL⟩ := hW.exists_simpleHolding_martingale_approx hH
  exact hZ.congr hIa fun t ↦ (hZL t).trans (hI.ae_eq_l2Integral hW hH t).symm

/-- An Itô integral of a Brownian-integrable integrand against a pre-Brownian motion relative to
the filtration is square integrable at every time. -/
theorem IsItoIntegral.memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    MemLp (I t) 2 P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH t).symm

/-- **The Itô isometry**, in `L²` norms. Against a pre-Brownian motion relative to the
filtration, the `L²(P)` norm at time `t` of an Itô integral of a Brownian-integrable integrand is
the `L²` norm of the integrand for Lebesgue time on `(0,t]` times `P`. -/
theorem IsItoIntegral.eLpNorm_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hiso := congrArg ENNReal.ofReal ((hW.l2Integral t).norm_map
    ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)))
  rw [Lp.norm_def, Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top,
    ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top] at hiso
  rw [eLpNorm_congr_ae (hI.ae_eq_l2Integral hW hH t), hiso,
    eLpNorm_congr_ae ((hH.memLp_predictableMeasure t).coeFn_toLp),
    ℱ.eLpNorm_predictableMeasure P hH.isStronglyPredictable t 2]

/-- **The Itô isometry.** Against a pre-Brownian motion relative to the filtration, an Itô
integral `I` of a Brownian-integrable integrand `H` satisfies `E[I_t²] = E ∫_(0,t] H_s² ds`. -/
theorem IsItoIntegral.integral_sq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  have hH₂ : AEStronglyMeasurable (Function.uncurry H) ((timeMeasure t).prod P) :=
    (hH.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
  have h := congrArg (fun x ↦ x.toReal ^ 2) (hI.eLpNorm_eq hW hH t)
  simp only [← integral_norm_sq_eq_toReal_eLpNorm_sq (hI.memLp hW hH t).aestronglyMeasurable,
    ← integral_norm_sq_eq_toReal_eLpNorm_sq hH₂, Real.norm_eq_abs, sq_abs] at h
  exact h

namespace IsItoIntegral

variable {K J : ℝ≥0 → Ω → ℝ}

/-- At every horizon `T`, the `L²(P)` class of `I T` equals `hW.l2Integral T` applied to `H`,
without assuming path continuity of `W`. -/
theorem toLp_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    (hI.memLp hW hH T).toLp (I T) =
      hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) :=
  Lp.ext ((hI.memLp hW hH T).coeFn_toLp.trans (hI.ae_eq_l2Integral hW hH T))

/-- **`(s, t]`-increment `L²`-seminorm Itô isometry**: for `s ≤ t`, `eLpNorm (I t - I s) 2 P` equals
the `L²((timeMeasure t).prod P)` seminorm of `H · 1_{(s, t]}`, without path continuity of `W`. -/
theorem eLpNorm_sub_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (I t - I s) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (H · p.2) p.1) 2
        ((timeMeasure t).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hsub : eLpNorm (I t - I s) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioi s).indicator (H · p.2) p.1) 2 ((timeMeasure t).prod P) := by
    simpa only [Pi.sub_def, Function.uncurry_def, min_eq_left hst] using
      (hI.indicator_Ioi hW s).eLpNorm_eq hW (hH.indicator_Ioi s) t
  exact hsub.trans (eLpNorm_congr_ae (indicator_Ioi_ae_eq_indicator_Ioc_timeMeasure_prod H s t))

/-- The `L²(P)` distance between the elementary gains of a left-measurable `L²` simple strategy on
a nondecreasing grid and an Itô integral of `K` equals the `L²((timeMeasure T).prod P)` distance
between their integrands, without assuming path continuity of `W`. -/
theorem eLpNorm_simpleGains_sub_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hK : BrownianIntegrable ℱ P K) (hI : IsItoIntegral ℱ P W K I)
    {n : ℕ} {γ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} (hγ : MonotoneOn γ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (γ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    eLpNorm (Finance.simpleGains γ n a W T - I T) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding γ n a p.1 p.2 - K p.1 p.2) 2
        ((timeMeasure T).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [← Lp.edist_toLp_toLp _ _ (hW.memLp_simpleGains hγ ha ha₂ T) (hI.memLp hW hK T),
    ← hW.l2Integral_simpleHolding hγ ha T
      (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T)
      (hW.memLp_simpleGains hγ ha ha₂ T),
    hI.toLp_eq_l2Integral hW hK T, (hW.l2Integral T).isometry.edist_eq, Lp.edist_toLp_toLp,
    ℱ.eLpNorm_predictableMeasure P
      ((Finance.isStronglyPredictable_simpleHolding ha).sub hK.isStronglyPredictable) T 2]
  simp only [Function.uncurry_def, Pi.sub_def]

/-- **Polarized Itô isometry**: `E[I T · J T] = E[∫_{(0, T]} H K]` for `BrownianIntegrable`
integrands `H` and `K`, without assuming path continuity of `W`. -/
theorem integral_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P := by
  have hmap := (hW.l2Integral T).inner_map_map
    ((hK.memLp_predictableMeasure T).toLp (Function.uncurry K))
    ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))
  rw [← hJ.toLp_eq_l2Integral hW hK T, ← hI.toLp_eq_l2Integral hW hH T,
    L2.inner_def, L2.inner_def] at hmap
  simp only [RCLike.inner_apply, conj_trivial] at hmap
  rw [← integral_congr_ae (((hI.memLp hW hH T).coeFn_toLp.and (hJ.memLp hW hK T).coeFn_toLp).mono
      fun _ ⟨h1, h2⟩ ↦ congrArg₂ (· * ·) h1 h2), hmap,
    integral_congr_ae (((hH.memLp_predictableMeasure T).coeFn_toLp.and
      (hK.memLp_predictableMeasure T).coeFn_toLp).mono fun _ ⟨h1, h2⟩ ↦ congrArg₂ (· * ·) h1 h2)]
  exact ℱ.integral_predictableMeasure P (hH.isStronglyPredictable.mul hK.isStronglyPredictable) T

/-- **`(s, t]`-increment Bochner-integral Itô isometry**: for `s ≤ t`,
`E[(I t - I s)²] = E[∫_{(s, t]} H²]`, without assuming path continuity of `W`. -/
theorem integral_sub_sq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p, (Ioc s t).indicator (H · p.2) p.1 ^ 2 ∂(timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have heq : ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p, (Ioi s).indicator (H · p.2) p.1 ^ 2 ∂(timeMeasure t).prod P := by
    simpa only [min_eq_left hst] using
      (hI.indicator_Ioi hW s).integral_sq hW (hH.indicator_Ioi s) t
  exact heq.trans (integral_congr_ae
    ((indicator_Ioi_ae_eq_indicator_Ioc_timeMeasure_prod H s t).mono fun _ hp ↦
      congrArg (· ^ 2) hp))

end IsItoIntegral

end TauCeti.Probability
