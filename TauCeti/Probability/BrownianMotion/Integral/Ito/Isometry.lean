/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.BrownianMotion.Integral.Process
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.MaximalInequality.Lp

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W`, identifies `IsItoIntegral` with the terminal
`L²` construction `l2Integral`, and proves the Itô isometry.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral_approx` and
  `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale, approximated simultaneously on every
  finite horizon by one sequence of bounded simple strategies in `L²`, uniformly in probability on
  `[0, T]`, and along a subsequence a.s. uniformly on `[0, T]`.
* `TauCeti.Probability.IsItoIntegral.ae_eq_l2Integral`, `ae_eq_l2Integral_of_memLp`, and
  `TauCeti.Probability.IsItoIntegral.toLp_eq_l2Integral`: every Itô integral of `H` agrees almost
  surely (and in `L²(P)`) at each horizon `T` with `hW.l2Integral T`.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsItoIntegral.memLp`, `memLp_of_memLp`, `eLpNorm_eq`, `eLpNorm_eq_of_memLp`,
  `integral_sq`, `integral_sq_of_memLp`, `eLpNorm_sub_eq`, `eLpNorm_simpleGains_sub_eq`,
  `integral_mul`, `integral_sub_sq`: `L²(P)` membership and the Itô isometry (in `L²` norm,
  Bochner square, polarized, `(s, t]`-increment, and elementary-strategy comparison forms).
* `TauCeti.Probability.IsItoIntegral.tendsto_eLpNorm_iSup_eNorm_simpleGains_sub`: when `W`
  has almost surely continuous paths and `H` is square integrable on `(0, T] × Ω`, elementary
  gains of simple holdings converging to `H` in `L²((timeMeasure T).prod P)` converge uniformly
  on `[0, T]` in `L²(P)` to `I`.

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
isometry, `l2Integral` identification, and martingale property; only existence and uniform `L²`
approximation use continuous paths. Adaptedness is needed for the martingale property because an
Itô integral is determined only up to indistinguishability, and an arbitrary indistinguishable
version need not be adapted to a raw filtration.

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

private structure SimpleHoldingApprox {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W H : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) where
  n : ℕ → ℕ
  τ : ℕ → ℕ → ℝ≥0
  a : ℕ → ℕ → Ω → ℝ
  C : ℕ → ℝ
  tau_zero : ∀ m, τ m 0 = 0
  strictMonoOn : ∀ m, StrictMonoOn (τ m) (Iic (n m))
  stronglyMeasurable : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)
  norm_le : ∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m
  martingale : ∀ m, Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P
  memLp : ∀ m T, MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P
  tendsto_holding : ∀ T, Tendsto (fun m ↦ eLpNorm
    (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
      ((timeMeasure T).prod P)) atTop (𝓝 0)
  tendsto_l2Integral : ∀ T, Tendsto (fun m ↦ (memLp m T).toLp
    (Finance.simpleGains (τ m) (n m) (a m) W T)) atTop
    (𝓝 (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))))

private theorem SimpleHoldingApprox.tendsto_energy
    {hW : IsFilteredPreBrownianReal ℱ W P} {hH : BrownianIntegrable ℱ P H}
    (h : SimpleHoldingApprox ℱ P W H hW hH) (T : ℝ≥0) (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤ ∫⁻ s,
      ‖Finance.simpleHolding (h.τ m) (h.n m) (h.a m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
      atTop (𝓝 0) :=
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  IsStronglyPredictable.tendsto_measure_lintegral_enorm_sub_sq_of_tendsto_eLpNorm
    (fun m ↦ Finance.isStronglyPredictable_simpleHolding (h.stronglyMeasurable m))
    (fun _ ↦ hH.isStronglyPredictable) (h.tendsto_holding T) hε

private theorem SimpleHoldingApprox.tendstoInMeasure_l2Integral
    {hW : IsFilteredPreBrownianReal ℱ W P} {hH : BrownianIntegrable ℱ P H}
    (h : SimpleHoldingApprox ℱ P W H hW hH) (T : ℝ≥0) :
    TendstoInMeasure P (fun m ↦ Finance.simpleGains (h.τ m) (h.n m) (h.a m) W T) atTop
      (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) :=
  (MeasureTheory.tendstoInMeasure_of_tendsto_Lp (h.tendsto_l2Integral T)).congr_left
    fun m ↦ (h.memLp m T).coeFn_toLp

private theorem exists_simpleHoldingApprox
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    Nonempty (SimpleHoldingApprox ℱ P W H hW hH) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  refine ⟨⟨n, τ, a, C, hτ₀, hτ, ha, hb,
    fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb m j hj ω⟩,
    fun m T ↦ hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T, herr, fun T ↦ ?_⟩⟩
  have hu : Tendsto (fun m ↦ (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).toLp
      (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))) atTop
      (𝓝 ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine (herr T).congr fun m ↦ ?_
    rw [Lp.edist_toLp_toLp, ℱ.eLpNorm_predictableMeasure P
      ((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable) T 2]
    simp only [Function.uncurry_def, Pi.sub_def]
  exact (((hW.l2Integral T).continuous.tendsto _).comp hu).congr fun m ↦
    hW.l2Integral_simpleHolding (hτ m).monotoneOn (ha m) T
      (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T)
      (hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T)

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
  obtain ⟨h⟩ := exists_simpleHoldingApprox hW hH
  obtain ⟨I, hIm, hIp, hIlim, hIunif, φ, hφ, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp h.martingale
      (fun _ ↦ hcont.mono fun _ hω ↦ Finance.continuous_simpleGains hω) h.memLp
      fun T ↦ (h.tendsto_l2Integral T).cauchySeq
  have hIto : IsItoIntegral ℱ P W H I :=
    ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦
      ⟨h.n, h.τ, h.a, fun m ↦ (h.strictMonoOn m).monotoneOn, h.stronglyMeasurable,
        h.tendsto_energy t, tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hIlim t).2⟩⟩
  exact ⟨⟨I, h, hIto, hIp, hIm, fun T ↦ (hIlim T).2, hIunif, φ, hφ, hIpath.mono fun _ h ↦ h.2⟩⟩

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
    h.approx.stronglyMeasurable, h.approx.norm_le, h.approx.tendsto_holding,
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

/-- Against a filtered pre-Brownian motion, every Itô integral of an integrand with finite expected
square energy on `(0, t]` agrees almost surely at `t` with `hW.l2Integral t`. -/
theorem IsItoIntegral.ae_eq_l2Integral_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH).toLp
        (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  choose n τ a _ _ hτ ha _ herr using fun m : ℕ ↦
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t hI.isStronglyPredictable hH
      (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  have hhold := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun m ↦ (herr m).le
  exact tendstoInMeasure_ae_unique
    (hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero hhold hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hI.isStronglyPredictable hH
        (fun m ↦ (hτ m).monotoneOn) ha hhold))

/-- Every Itô integral of a `BrownianIntegrable` integrand agrees `P`-a.s. at horizon `T`
with `hW.l2Integral T`, without assuming path continuity of `W`. -/
theorem IsItoIntegral.ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨h⟩ := exists_simpleHoldingApprox hW hH
  exact hI.ae_eq_of_tendstoInMeasure hW (fun m ↦ (h.strictMonoOn m).monotoneOn)
    h.stronglyMeasurable (h.tendsto_energy T) (h.tendstoInMeasure_l2Integral T)

/-- **The martingale property of the Itô integral.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral of a Brownian-integrable integrand is a martingale.
Neither path continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨h⟩ := exists_simpleHoldingApprox hW hH
  obtain ⟨Z, hZ, hZlim⟩ := exists_martingale_of_cauchySeq_Lp h.martingale h.memLp
    fun t ↦ (h.tendsto_l2Integral t).cauchySeq
  refine hZ.congr hIa fun t ↦ (tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hZlim t).2)
    (h.tendstoInMeasure_l2Integral t)).trans (hI.ae_eq_l2Integral hW hH t).symm

/-- Restricting an integrand in `L²((timeMeasure t).prod P)` to `(0, t]` produces a
`BrownianIntegrable` integrand and preserves the Itô integral up to `t`. -/
private theorem IsItoIntegral.ite_le_brownianIntegrable
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0)
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    IsItoIntegral ℱ P W (H - fun s ω ↦ if t < s then H s ω else 0)
        (I - fun s ω ↦ I s ω - I (min t s) ω) ∧
      BrownianIntegrable ℱ P (H - fun s ω ↦ if t < s then H s ω else 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let H_t : ℝ≥0 → Ω → ℝ := H - fun s ω ↦ if t < s then H s ω else 0
  let I_t : ℝ≥0 → Ω → ℝ := I - fun s ω ↦ I s ω - I (min t s) ω
  have hIt_ito : IsItoIntegral ℱ P W H_t I_t := by
    simpa only [one_mul] using
      hI.sub (hI.ite_lt_mul hW t (ξ := fun _ ↦ 1) stronglyMeasurable_const)
  refine ⟨hIt_ito, hIt_ito.isStronglyPredictable, fun S ↦ ?_⟩
  rw [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
  have hm := (hIt_ito.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
    (μ := (timeMeasure S).prod P)
  rw [hm.memLp_two_iff_lintegral_enorm_sq_lt_top, lintegral_prod _ (hm.eNorm.pow_const 2)]
  calc
    _ = ∫⁻ s, ∫⁻ ω, (if s ≤ t then ‖H s ω‖ₑ ^ 2 else 0) ∂P ∂timeMeasure S := by
      refine lintegral_congr fun s ↦ lintegral_congr fun ω ↦ ?_
      simp only [Function.uncurry, H_t, Pi.sub_apply]
      by_cases hs : t < s
      · simp [hs, hs.not_ge]
      · simp [hs, not_lt.1 hs]
    _ = ∫⁻ s in Ioc 0 t, ∫⁻ ω, ‖H s ω‖ₑ ^ 2 ∂P ∂timeMeasure S := by
      rw [← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr_ae ((ae_mem_Ioc_timeMeasure S).mono fun s hs ↦ ?_)
      by_cases hle : s ≤ t
      · simp [hle, hs.1]
      · simp [hle]
    _ = ∫⁻ s, ∫⁻ ω, ‖H s ω‖ₑ ^ 2 ∂P ∂timeMeasure (min t S) := by
      rw [timeMeasure_restrict]
    _ ≤ ∫⁻ s, ∫⁻ ω, ‖H s ω‖ₑ ^ 2 ∂P ∂timeMeasure t :=
      lintegral_mono' (timeMeasure_mono (min_le_left t S)) le_rfl
    _ = ∫⁻ p, ‖H p.1 p.2‖ₑ ^ 2 ∂(timeMeasure t).prod P :=
      (lintegral_prod _ (hH.aestronglyMeasurable.eNorm.pow_const 2)).symm
    _ < ∞ := hH.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 hH

/-- An Itô integral of an integrand with finite expected square energy on `(0, t]` is square
integrable at `t`. -/
theorem IsItoIntegral.memLp_of_memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral_of_memLp hW hH).symm

/-- An Itô integral of a Brownian-integrable integrand against a pre-Brownian motion relative to
the filtration is square integrable at every time. -/
theorem IsItoIntegral.memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    MemLp (I t) 2 P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH t).symm

/-- **The Itô isometry**, in `L²` norms, at a single horizon `t`. Against a pre-Brownian motion
relative to the filtration, the `L²(P)` norm at time `t` of an Itô integral of an integrand with
finite expected square energy on `(0, t]` is the `L²` norm of the integrand for Lebesgue time on
`(0, t]` times `P`. -/
theorem IsItoIntegral.eLpNorm_eq_of_memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hHp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH
  have hnorm : (eLpNorm (hW.l2Integral t (hHp.toLp (Function.uncurry H))) 2 P).toReal =
      (eLpNorm (hHp.toLp (Function.uncurry H)) 2 (ℱ.predictableMeasure P t)).toReal := by
    simpa only [Lp.norm_def] using (hW.l2Integral t).norm_map (hHp.toLp (Function.uncurry H))
  rw [eLpNorm_congr_ae (hI.ae_eq_l2Integral_of_memLp hW hH),
    (ENNReal.toReal_eq_toReal_iff' (Lp.memLp _).eLpNorm_ne_top (Lp.memLp _).eLpNorm_ne_top).1
      hnorm,
    eLpNorm_congr_ae hHp.coeFn_toLp, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod hI.isStronglyPredictable]

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

/-- **The Itô isometry**, at a single horizon `t`. Against a pre-Brownian motion relative to the
filtration, an Itô integral `I` of an integrand `H` with finite expected square energy on `(0, t]`
satisfies `E[I_t²] = E ∫_(0,t] H_s² ds`. -/
theorem IsItoIntegral.integral_sq_of_memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  have h := congrArg (fun x ↦ x.toReal ^ 2) (hI.eLpNorm_eq_of_memLp hW hH)
  simp only [← integral_norm_sq_eq_toReal_eLpNorm_sq
      (hI.memLp_of_memLp hW hH).aestronglyMeasurable,
    ← integral_norm_sq_eq_toReal_eLpNorm_sq hH.aestronglyMeasurable, Real.norm_eq_abs, sq_abs] at h
  exact h

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

/-- **Finite-horizon uniform `L²` convergence of elementary approximants.** Against an almost
surely continuous filtered pre-Brownian motion `W`, any family of left-measurable simple holdings
converging in `L²((timeMeasure T).prod P)` to a square-integrable integrand `H` has elementary
gains whose running supremum error on `[0, T]` converges to zero in `L²(P)`. -/
theorem tendsto_eLpNorm_iSup_eNorm_simpleGains_sub
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {ι : Type*} {l : Filter ι} {T : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P))
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hlim : Tendsto (fun i ↦ eLpNorm
      (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i)) - Function.uncurry H) 2
        ((timeMeasure T).prod P)) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun ω ↦
      ⨆ t ≤ T, ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖ₑ) 2 P) l (𝓝 0) := by
  classical
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨hIt_ito, hHt_bi⟩ := hI.ite_le_brownianIntegrable hW T hH
  obtain ⟨Y, hY_ito, -, hY_mart⟩ := hHt_bi.exists_isItoIntegral hW hWc
  have hIY_ind : (I - fun s ω ↦ I s ω - I (min T s) ω) ≡ᵐ[P] Y :=
    isItoIntegral_unique hW hIt_ito hY_ito
  have hIY : ∀ᵐ ω ∂P, ∀ t ≤ T, I t ω = Y t ω :=
    hIY_ind.mono fun ω hω t ht ↦ by simpa [ht] using hω t
  have hMem : ∀ i, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M ℱ P ∧ (∀ᵐ ω ∂P, Continuous fun t ↦ M t ω) ∧
      (MemLp (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))) 2
          ((timeMeasure T).prod P) →
        ∀ t ≤ T, ∀ ω, M t ω = Finance.simpleGains (τ i) (n i) (a i) W t ω) := fun i ↦ by
    by_cases hK : MemLp (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))) 2
        ((timeMeasure T).prod P)
    · obtain ⟨M, hM, hMc, hMeq⟩ :=
        hW.exists_martingale_simpleGains_eq_on_Iic hWc (hτ i) (ha i) hK
      exact ⟨M, hM, hMc, fun _ ↦ hMeq⟩
    · exact ⟨0, martingale_zero _ ℱ P, .of_forall fun _ ↦ continuous_const, fun h ↦ absurd h hK⟩
  choose M hM_mart hM_cont hM_eq using hMem
  have hK_ev : ∀ᶠ i in l, MemLp (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))) 2
      ((timeMeasure T).prod P) :=
    eventually_memLp_of_tendsto_eLpNorm_sub ENNReal.zero_ne_top hH hlim
  have hterm : Tendsto (fun i ↦ eLpNorm (M i T - Y T) 2 P) l (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [hK_ev] with i hK_mem
    have hGI : eLpNorm (Finance.simpleGains (τ i) (n i) (a i) W T - I T) 2 P =
        eLpNorm (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i)) -
          Function.uncurry H) 2 ((timeMeasure T).prod P) :=
      ((isItoIntegral_simpleGains hWc (hτ i) (ha i)).sub hI).eLpNorm_eq_of_memLp hW (hK_mem.sub hH)
    refine hGI.symm.trans (eLpNorm_congr_ae ?_)
    filter_upwards [hIY] with ω hω
    simp [hM_eq i hK_mem T le_rfl ω, hω T le_rfl]
  have hdoob := MeasureTheory.Martingale.tendsto_eLpNorm_iSup_eNorm_sub hY_mart hM_mart
    (hY_ito.ae_continuous.mono fun _ hc t _ ↦ hc.continuousAt.continuousWithinAt)
    (fun i ↦ (hM_cont i).mono fun _ hc t _ ↦ hc.continuousAt.continuousWithinAt)
    (by norm_num : (1 : ℝ≥0∞) < 2) (by norm_num) hterm
  refine hdoob.congr' ?_
  filter_upwards [hK_ev] with i hK_mem
  refine eLpNorm_congr_ae (hIY.mono fun ω hω ↦ ?_)
  refine iSup_congr fun t ↦ iSup_congr fun ht ↦ ?_
  rw [hM_eq i hK_mem t ht ω, hω t ht]

end IsItoIntegral

end TauCeti.Probability
