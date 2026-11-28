/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Ito.Substitution
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Integral.Square
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.Probability.Process.TimeIntegral

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W` and proves the Itô isometry.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral_approx` and
  `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale, approximated simultaneously on every
  finite horizon by one sequence of bounded simple strategies in `L²`, uniformly in probability on
  `[0, T]`, and along a subsequence a.s. uniformly on `[0, T]`.
* `TauCeti.Probability.IsItoIntegral.ae_eq_l2Integral` and
  `TauCeti.Probability.IsItoIntegral.toLp_eq_l2Integral`: every Itô integral of `H` agrees almost
  surely (and in `L²(P)`) at each horizon `T` with `hW.l2Integral T`.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq`,
  `TauCeti.Probability.IsItoIntegral.integral_sq`, `eLpNorm_sub_eq`,
  `eLpNorm_simpleGains_sub_eq`, `integral_mul`, `integral_sub_sq`,
  `eq_predictableMeasure_withDensity_iff`: `L²(P)` membership, the Itô isometry (in `L²` norm,
  Bochner square, polarized, `(s, t]`-increment, and elementary-strategy comparison forms), and the
  uniqueness characterization of the finite predictable measure
  `(ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)` by its increment energy on
  predictable rectangles.

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

/-- Converse `L²` characterization: any almost surely continuous modification of
`t ↦ hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))` satisfies
`IsItoIntegral`, without assuming path continuity of `W`. -/
theorem of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI_cont : ∀ᵐ ω ∂P, Continuous fun t ↦ I t ω)
    (hI : ∀ t, letI := (hW.hasLaw_eval 0).isProbabilityMeasure
      I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) :
    IsItoIntegral ℱ P W H I := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨h⟩ := exists_simpleHoldingApprox hW hH
  exact ⟨hH.isStronglyPredictable, hI_cont, fun t ↦
    ⟨h.n, h.τ, h.a, fun k ↦ (h.strictMonoOn k).monotoneOn, h.stronglyMeasurable,
      h.tendsto_energy t, (h.tendstoInMeasure_l2Integral t).congr_right (hI t).symm⟩⟩

/-- **Square-compensation martingale of the Brownian Itô integral**: for a `BrownianIntegrable`
integrand `H` and a strongly adapted Itô integral `I`, `I_t² - ∫_{(0, t]} H_s² ds` is a true
martingale on the original raw filtration, without assuming path continuity of `W`. -/
theorem martingale_sq_sub_integral (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  let M (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 -
      ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t
  have hM (m : ℕ) : Martingale (M m) ℱ P := by
    convert hW.martingale_sq_simpleGains_sub (hτ m).monotoneOn (ha m) (ha₂ m) using 1
    ext t ω; dsimp only [M]
    rw [Finance.integral_sq_simpleHolding_timeMeasure (hτ m).monotoneOn t ω]
  have hcomp_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) := by
    simpa only [sq] using (hH.isStronglyPredictable.mul
      hH.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
  refine martingale_of_tendsto_eLpNorm_one hM (fun t ↦ ((hIa t).pow 2).sub (hcomp_adapt t))
    fun t ↦ ?_
  have hG_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hI.memLp hW hH t).eLpNorm_ne_top <|
      (herr t).congr fun m ↦ (hI.eLpNorm_simpleGains_sub_eq hW hH
        (hτ m).monotoneOn (ha m) (ha₂ m) t).symm
  have hA_lim := TauCeti.tendsto_eLpNorm_one_integral_sq_sub (hH.memLp_timeMeasure t)
    (.of_forall fun m ↦ (BrownianIntegrable.simpleHolding (ha m) (ha₂ m)).memLp_timeMeasure t)
    (herr t)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hG_lim.add hA_lim) (fun _ ↦ bot_le) fun m ↦ ?_
  have heq : (M m t - fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) =
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) -
        fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t := by
    ext ω; dsimp only [M, Pi.sub_apply]; ring
  rw [heq]
  exact eLpNorm_sub_le le_rfl

/-- **Set-integral increment energy of the Brownian Itô integral**: for `s ≤ t` and any `ℱ s`-
measurable event `A`, the set integral of `(I t - I s)²` over `A` equals the expected square energy
of `H` over `(s, t] × A`, without assuming path continuity of `W` or adaptedness of `I`. -/
theorem setIntegral_sq_sub (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p in Ioc s t ×ˢ A, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ξ : Ω → ℝ := A.indicator 1
  have hξ : StronglyMeasurable[ℱ s] ξ := stronglyMeasurable_const.indicator hA
  have hIξ := hI.indicator_Ioi_mul hW s hξ
  have hHξ : BrownianIntegrable ℱ P (fun t ω ↦ (Ioi s).indicator (fun _ ↦ ξ ω) t * H t ω) := by
    refine ⟨hIξ.isStronglyPredictable, fun T ↦ ?_⟩
    refine ((hH.indicator_Ioi s).memLp T).mono ?_ (.of_forall fun ⟨r, ω⟩ ↦ ?_)
    · exact (hIξ.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
    · by_cases hrs : s < r <;> by_cases hω : ω ∈ A <;> simp [ξ, hrs, hω]
  have hsq := hIξ.integral_sq hW hHξ t
  have hL : (fun ω ↦ (ξ ω * (I t ω - I (min s t) ω)) ^ 2) =
      A.indicator (fun ω ↦ (I t ω - I s ω) ^ 2) := by
    ext ω; by_cases hω : ω ∈ A <;> simp [ξ, hω, min_eq_left hst]
  have hR : (fun p : ℝ≥0 × Ω ↦ ((Ioi s).indicator (fun _ ↦ ξ p.2) p.1 * H p.1 p.2) ^ 2) =ᵐ[
      (timeMeasure t).prod P] (Ioc s t ×ˢ A).indicator fun p ↦ H p.1 p.2 ^ 2 := by
    filter_upwards [indicator_Ioi_ae_eq_indicator_Ioc_timeMeasure_prod
      (fun _ ω ↦ ξ ω) s t] with ⟨u, ω⟩ hu
    dsimp only at hu
    rw [hu]
    by_cases hus : u ∈ Ioc s t <;> by_cases hω : ω ∈ A <;> simp [ξ, hus, hω]
  rw [hL, integral_indicator (ℱ.le s A hA)] at hsq
  rw [hsq, integral_congr_ae hR,
    integral_indicator ((measurableSet_Ioc (a := s) (b := t)).prod (ℱ.le s A hA))]

/-- On any predictable set `S`, the `H²`-weighted predictable measure equals the `ℝ≥0∞`-embedded
set integral of `H²` over `S` under `(timeMeasure T).prod P`. -/
theorem _root_.TauCeti.BrownianIntegrable.predictableMeasure_withDensity_apply
    (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0)
    {S : Set (ℝ≥0 × Ω)} (hS : MeasurableSet[ℱ.predictable] S) :
    ((ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)) S =
      ENNReal.ofReal (∫ p in S, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rw [withDensity_apply _ hS]
  have hint : IntegrableOn (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) S (ℱ.predictableMeasure P T) :=
    ((hH.memLp_predictableMeasure T).integrable_sq).integrableOn
  have hpt (p : ℝ≥0 × Ω) : ‖H p.1 p.2‖ₑ ^ 2 = ENNReal.ofReal (H p.1 p.2 ^ 2) := by
    rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ sq_nonneg _)]
  congr 1
  rw [← integral_indicator hS, ← integral_indicator (ℱ.predictable_le_prod S hS)]
  exact ℱ.integral_predictableMeasure P ((hH.isStronglyPredictable.pow 2).indicator hS) T

/-- For any `BrownianIntegrable` integrand `H`, weighting `ℱ.predictableMeasure P T` by `H²`
gives a finite measure on `ℱ.predictable`. -/
theorem _root_.TauCeti.BrownianIntegrable.isFiniteMeasure_predictableMeasure_withDensity
    (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    @IsFiniteMeasure (ℝ≥0 × Ω) ℱ.predictable
      ((ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)) :=
  @IsFiniteMeasure.mk _ ℱ.predictable _ <| by
    rw [hH.predictableMeasure_withDensity_apply T (@MeasurableSet.univ _ ℱ.predictable)]
    exact ENNReal.ofReal_lt_top

/-- **Predictable-measure characterization of the Brownian Itô integral**: on the predictable
σ-algebra up to horizon `T`, `(ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)`
is the unique measure assigning zero mass to `{0} ×ˢ univ` and `(T, ∞) ×ˢ univ` and assigning to
every predictable rectangle `(s, t] ×ˢ A` (`s ≤ t ≤ T`, `A ∈ ℱ s`) the increment energy
`∫ ω in A, (I t ω - I s ω) ^ 2 ∂P`. -/
theorem eq_predictableMeasure_withDensity_iff (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable) :
    μ = (ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2) ↔
      μ ({0} ×ˢ univ) = 0 ∧ μ (Ioi T ×ˢ univ) = 0 ∧
        ∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T → ∀ ⦃A : Set Ω⦄, MeasurableSet[ℱ s] A →
          μ (Ioc s t ×ˢ A) = ENNReal.ofReal (∫ ω in A, (I t ω - I s ω) ^ 2 ∂P) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ν : @Measure (ℝ≥0 × Ω) ℱ.predictable :=
    (ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)
  have : IsFiniteMeasure ν := hH.isFiniteMeasure_predictableMeasure_withDensity T
  have hν0 : ν ({0} ×ˢ univ) = 0 := by
    have h0meas : MeasurableSet[ℱ.predictable] ({0} ×ˢ (univ : Set Ω)) := by
      simpa only [NNReal.bot_eq_zero] using
        measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ) MeasurableSet.univ
    rw [withDensity_apply _ h0meas,
      Measure.restrict_eq_zero.mpr
        (ℱ.predictableMeasure_singleton_zero_prod P T MeasurableSet.univ),
      lintegral_zero_measure]
  have hνT : ν (Ioi T ×ˢ univ) = 0 := by
    have hTmeas : MeasurableSet[ℱ.predictable] (Ioi T ×ˢ (univ : Set Ω)) :=
      measurableSet_predictable_Ioi_prod MeasurableSet.univ
    have hnull : ℱ.predictableMeasure P T (Ioi T ×ˢ univ) = 0 := by
      have hempty : Ioi T ∩ Ioc 0 T = ∅ :=
        Set.eq_empty_of_forall_notMem fun _ hx ↦ hx.1.not_ge hx.2.2
      rw [ℱ.predictableMeasure_apply P T hTmeas, Measure.prod_prod,
        timeMeasure_def, Measure.restrict_apply measurableSet_Ioi,
        hempty, measure_empty, zero_mul]
    rw [withDensity_apply _ hTmeas, Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
  have hνIoc : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T → ∀ ⦃A : Set Ω⦄, MeasurableSet[ℱ s] A →
      ν (Ioc s t ×ˢ A) = ENNReal.ofReal (∫ ω in A, (I t ω - I s ω) ^ 2 ∂P) := by
    intro s t hst ht A hA
    have hres_time : (timeMeasure T).restrict (Ioc s t) = (timeMeasure t).restrict (Ioc s t) := by
      rw [← timeMeasure_restrict_of_le ht, Measure.restrict_restrict measurableSet_Ioc,
        Ioc_inter_Ioc, max_eq_left zero_le, min_self]
    have hres : ((timeMeasure T).prod P).restrict (Ioc s t ×ˢ A) =
        ((timeMeasure t).prod P).restrict (Ioc s t ×ˢ A) := by
      rw [← Measure.prod_restrict (Ioc s t) A, ← Measure.prod_restrict (Ioc s t) A, hres_time]
    rw [hH.predictableMeasure_withDensity_apply T (measurableSet_predictable_Ioc_prod s t hA),
      hres, hI.setIntegral_sq_sub hW hH hst hA]
  constructor
  · rintro rfl
    exact ⟨hν0, hνT, hνIoc⟩
  · rintro ⟨hμ0, hμT, hμIoc⟩
    symm
    refine MeasureTheory.ext_of_generate_finite ℱ.elementarySets
      ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets ?_ ?_
    · rintro u hu
      rcases (ℱ.mem_elementarySets_iff).1 hu with ⟨A, _, rfl⟩ | ⟨s, t, A, hA, rfl⟩
      · have hsub : ({⊥} ×ˢ A : Set (ℝ≥0 × Ω)) ⊆ {0} ×ˢ univ :=
          prod_mono (by simp) (subset_univ A)
        have h1 : ν ({⊥} ×ˢ A) = 0 := measure_mono_null hsub hν0
        have h2 : μ ({⊥} ×ˢ A) = 0 := measure_mono_null hsub hμ0
        exact h1.trans h2.symm
      · by_cases hst : s ≤ t
        · by_cases hsT : s ≤ T
          · have hsplit : Ioc s t ×ˢ A = (Ioc s (min t T) ×ˢ A) ∪ (Ioc (min t T) t ×ˢ A) := by
              ext ⟨r, ω⟩
              simp only [mem_prod, mem_Ioc, mem_union]
              grind
            have hdisj : Disjoint (Ioc s (min t T) ×ˢ A) (Ioc (min t T) t ×ˢ A) :=
              disjoint_prod.mpr (Or.inl (Set.disjoint_iff.mpr fun _ ⟨h1, h2⟩ ↦ h2.1.not_ge h1.2))
            have h2 : MeasurableSet[ℱ.predictable] (Ioc (min t T) t ×ˢ A) :=
              measurableSet_predictable_Ioc_prod (min t T) t
                (ℱ.mono (le_min hst hsT) _ hA)
            have hsub2 : Ioc (min t T) t ×ˢ A ⊆ Ioi T ×ˢ (univ : Set Ω) := by
              rintro ⟨r, ω⟩ ⟨hr, _⟩
              refine ⟨?_, trivial⟩
              by_cases htT : t ≤ T
              · rw [min_eq_left htT] at hr
                exact (hr.1.trans_le hr.2).false.elim
              · rw [min_eq_right (not_le.mp htT).le] at hr
                exact hr.1
            have hν1 : ν (Ioc s t ×ˢ A) = ν (Ioc s (min t T) ×ˢ A) := by
              rw [hsplit, measure_union hdisj h2, measure_mono_null hsub2 hνT, add_zero]
            have hμ1 : μ (Ioc s t ×ˢ A) = μ (Ioc s (min t T) ×ˢ A) := by
              rw [hsplit, measure_union hdisj h2, measure_mono_null hsub2 hμT, add_zero]
            rw [hν1, hμ1, hνIoc (le_min hst hsT) (min_le_right t T) hA,
              hμIoc (le_min hst hsT) (min_le_right t T) hA]
          · have hsub : Ioc s t ×ˢ A ⊆ Ioi T ×ˢ (univ : Set Ω) :=
              prod_mono (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (not_le.mp hsT).le))
                (subset_univ A)
            exact (measure_mono_null hsub hνT).trans (measure_mono_null hsub hμT).symm
        · rw [Ioc_eq_empty (lt_asymm (not_le.mp hst)), empty_prod, measure_empty, measure_empty]
    · have huniv : (univ : Set (ℝ≥0 × Ω)) =
          ({0} ×ˢ univ) ∪ (Ioc 0 T ×ˢ univ) ∪ (Ioi T ×ˢ univ) := by
        ext ⟨r, ω⟩
        simp only [mem_univ, mem_union, mem_prod, mem_singleton_iff, mem_Ioc, mem_Ioi,
          and_true, true_iff]
        rcases eq_or_ne r 0 with rfl | hr0
        · exact Or.inl (Or.inl rfl)
        · by_cases hrT : r ≤ T
          · exact Or.inl (Or.inr ⟨bot_lt_iff_ne_bot.mpr hr0, hrT⟩)
          · exact Or.inr (not_le.mp hrT)
      have hm1 : MeasurableSet[ℱ.predictable] (Ioc 0 T ×ˢ (univ : Set Ω)) :=
        measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ
      have hm2 : MeasurableSet[ℱ.predictable] (Ioi T ×ˢ (univ : Set Ω)) :=
        measurableSet_predictable_Ioi_prod MeasurableSet.univ
      have hd1 : Disjoint ({0} ×ˢ (univ : Set Ω)) (Ioc 0 T ×ˢ (univ : Set Ω)) :=
        disjoint_prod.mpr (Or.inl (by simp))
      have hd2 : Disjoint (({0} ×ˢ (univ : Set Ω)) ∪ (Ioc 0 T ×ˢ (univ : Set Ω)))
          (Ioi T ×ˢ (univ : Set Ω)) :=
        Disjoint.union_left
          (disjoint_prod.mpr (Or.inl (by simp)))
          (disjoint_prod.mpr (Or.inl Ioc_disjoint_Ioi_same))
      have hνu : ν univ = ν (Ioc 0 T ×ˢ univ) := by
        rw [huniv, measure_union hd2 hm2, measure_union hd1 hm1, hν0, hνT, zero_add, add_zero]
      have hμu : μ univ = μ (Ioc 0 T ×ˢ univ) := by
        rw [huniv, measure_union hd2 hm2, measure_union hd1 hm1, hμ0, hμT, zero_add, add_zero]
      rw [hνu, hμu, hνIoc zero_le le_rfl MeasurableSet.univ,
        hμIoc zero_le le_rfl MeasurableSet.univ]

/-- **Conditional increment isometry of the Brownian Itô integral**: for `s ≤ t`,
`E[(I t - I s)² | ℱ s] = E[∫_(s, t] H u ^ 2 du | ℱ s]` almost surely, without assuming path
continuity of `W` or adaptedness of `I`. -/
theorem condExp_sq_sub (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ (I t ω - I s ω) ^ 2 | ℱ s] =ᵐ[P]
      P[fun ω ↦ ∫ u in Ioc s t, H u ω ^ 2 ∂timeMeasure t | ℱ s] := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hI_mem : MemLp (fun ω ↦ I t ω - I s ω) 2 P :=
    (hI.memLp hW hH t).sub (hI.memLp hW hH s)
  have hH₂ : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P) := hH.memLp_timeMeasure t
  have hprod_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod P) :=
    hH₂.integrable_sq.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    hI_mem.integrable_sq (fun _ _ _ ↦ integrable_condExp.integrableOn)
    (fun A hA _ ↦ ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hA_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod (P.restrict A)) :=
    hprod_int.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [setIntegral_condExp (ℱ.le s) hprod_int.integral_prod_right hA,
    hI.setIntegral_sq_sub hW hH hst hA, ← Measure.prod_restrict (Ioc s t) A,
    integral_prod_symm _ hA_int]

/-- **Deterministic-integrand comparison with the Wiener integral**: an Itô integral of a
deterministic `L²(timeMeasure T)` integrand `f` agrees almost surely at time `T` with its
deterministic Wiener integral, without assuming path continuity of `W`. -/
theorem ae_eq_wienerIntegral {f : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun t _ ↦ f t) I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} (hf : MemLp f 2 (timeMeasure T)) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    I T =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral T (hf.toLp f) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨_, hω⟩ := hI.locallyBrownianIntegrable.ae_memLp.exists
  have hH : BrownianIntegrable ℱ P (fun t _ ↦ f t) :=
    ⟨hI.isStronglyPredictable, fun t ↦ (hω t).comp_fst P⟩
  refine (hI.ae_eq_l2Integral hW hH T).trans ?_
  rw [← hW.l2Integral_compMeasurePreserving_fst T (hf.toLp f),
    Lp.toLp_compMeasurePreserving hf (ℱ.measurePreserving_fst_predictableMeasure P T)]
  rfl

end IsItoIntegral

/-- Characterization of `IsItoIntegral` on `BrownianIntegrable` integrands: a process `I` is an
Itô integral of `H` against `W` if and only if it has almost surely continuous paths and agrees
almost everywhere at every time `t` with `hW.l2Integral t`. -/
theorem isItoIntegral_iff_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) :
    IsItoIntegral ℱ P W H I ↔ (∀ᵐ ω ∂P, Continuous fun t ↦ I t ω) ∧
      ∀ t, letI := (hW.hasLaw_eval 0).isProbabilityMeasure
        I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :=
  ⟨fun hI ↦ ⟨hI.ae_continuous, fun t ↦ hI.ae_eq_l2Integral hW hH t⟩,
    fun ⟨hIc, hI⟩ ↦ IsItoIntegral.of_ae_eq_l2Integral hW hH hIc hI⟩

end TauCeti.Probability
