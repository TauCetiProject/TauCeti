/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The continuous Brownian Itô integral on the expected square-energy domain

For `H` in `TauCeti.BrownianIntegrable ℱ P H`, this module constructs a predictable continuous
martingale `I` with `TauCeti.IsItoIntegral ℱ P W H I` whenever `W` is a filtered pre-Brownian
motion with a.s. continuous paths, and shows that every continuous Itô integral of `H` against any
filtered pre-Brownian motion agrees with `hW.l2Integral T`, has zero expectation, satisfies the
polarized Itô isometry, and is a martingale when strongly adapted.

## Main results

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: predictable continuous martingale Itô integral
  for `BrownianIntegrable` integrands.
* `TauCeti.IsItoIntegral.ae_eq_l2Integral`, `memLp`, `toLp_eq_l2Integral`: identification of `I T`
  with `hW.l2Integral T` in `L²(P)`.
* `TauCeti.IsItoIntegral.eLpNorm_eq`, `integral_eq_zero`, `integral_mul`, `integral_sq`: zero
  expectation and the polarized and quadratic Itô isometries.
* `TauCeti.IsItoIntegral.martingale`: strongly adapted `L²` Itô integrals are martingales.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

private theorem exists_simpleHolding_tendsto_l2Integral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
      (_ : ∀ m, StrictMonoOn (τ m) (Iic (n m)))
      (_ : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
      (_ : ∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m)
      (_ : ∀ m, Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P)
      (hmem : ∀ m T, MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P),
      (∀ T, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ T, Tendsto (fun m ↦ (hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T)) atTop
        (𝓝 (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)))) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (.of_forall (hb m j hj))
  refine ⟨n, τ, a, C, hτ, ha, hb,
    fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb m j hj ω⟩,
    fun m T ↦ hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T, herr, fun T ↦ ?_⟩
  have hu : Tendsto (fun m ↦ (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).toLp
      (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))) atTop
      (𝓝 ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
    rw [tendsto_iff_edist_tendsto_0]
    exact (herr T).congr fun m ↦ by
      rw [Lp.edist_toLp_toLp, ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod
        ((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable)]; rfl
  exact (((hW.l2Integral T).continuous.tendsto _).comp hu).congr fun m ↦
    hW.l2Integral_toLp_simpleHolding (hτ m).monotoneOn (ha m) (ha₂ m) T

/-- **Existence of the continuous `L²` Brownian Itô integral**: every `BrownianIntegrable`
integrand against a filtered pre-Brownian motion `W` with a.s. continuous paths admits a
predictable continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨n, τ, a, C, hτ, ha, hb, hMm, hmem, herr, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  obtain ⟨I, hIm, hIp, hIlim, -, _, -, hIpath⟩ := exists_continuous_martingale_of_cauchySeq_Lp hMm
    (fun _ ↦ hcont.mono fun _ hω ↦ by simp only [Finance.simpleGains_def]; fun_prop) hmem
    fun T ↦ (hlim T).cauchySeq
  refine ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦
    ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun m j hj ↦ ⟨C m, hb m j hj⟩,
      fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
        (.of_forall fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
        (herr t) hε,
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2⟩⟩, hIp, hIm⟩

namespace IsItoIntegral

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand agrees `P`-a.s. at horizon `T`
with `hW.l2Integral T`, without assuming path continuity of `W`. -/
theorem ae_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hτ, ha, -, -, hmem, herr, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  have hl2 : Tendsto (fun m ↦ eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T -
      (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) : Ω → ℝ)) 2 P)
      atTop (𝓝 0) := (tendsto_iff_edist_tendsto_0.mp (hlim T)).congr fun m ↦ by
    rw [Lp.edist_def]; exact eLpNorm_congr_ae (((hmem m T).coeFn_toLp).sub .rfl)
  exact hI.ae_eq_of_approx hW (fun m ↦ (hτ m).monotoneOn) ha
    (fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (.of_forall fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (herr T) hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hl2)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand belongs to `L²(P)` at each
finite horizon, without assuming path continuity of `W`. -/
theorem memLp (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    MemLp (I T) 2 P :=
  (Lp.memLp (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)))).ae_eq
    (hI.ae_eq_l2Integral hW hH T).symm

/-- At every horizon `T`, the `L²(P)` class of `I T` equals `hW.l2Integral T` applied to `H`,
without assuming path continuity of `W`. -/
theorem toLp_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    (hI.memLp hW hH T).toLp (I T) =
      hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) :=
  Lp.ext ((hI.memLp hW hH T).coeFn_toLp.trans (hI.ae_eq_l2Integral hW hH T))

/-- **`L²`-seminorm Itô isometry**: `eLpNorm (I T) 2 P` equals the `L²((timeMeasure T).prod P)`
seminorm of `H` at every horizon `T`, without assuming path continuity of `W`. -/
theorem eLpNorm_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    eLpNorm (I T) 2 P =
      eLpNorm (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  have hnorm : ‖(hI.memLp hW hH T).toLp (I T)‖ =
      ‖(hH.memLp_predictableMeasure T).toLp (Function.uncurry H)‖ := by
    rw [hI.toLp_eq_l2Integral hW hH T, (hW.l2Integral T).norm_map]
  simp only [Lp.norm_toLp, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod hH.isStronglyPredictable] at hnorm
  exact (ENNReal.toReal_eq_toReal_iff' (hI.memLp hW hH T).eLpNorm_lt_top.ne
    (hH.memLp_timeMeasure T).eLpNorm_lt_top.ne).mp hnorm

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

/-- **Polarized Itô isometry**: `E[I T · J T] = E[∫_{(0, T]} H K]` for `BrownianIntegrable`
integrands `H` and `K`, without assuming path continuity of `W`. -/
theorem integral_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(Probability.timeMeasure T).prod P := by
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

/-- **Bochner-integral Itô isometry**: `E[(I T)²] = E[∫_{(0, T]} H²]` for `BrownianIntegrable`
`H`, without assuming path continuity of `W`. -/
theorem integral_sq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure T).prod P := by
  simpa only [sq] using hI.integral_mul hW hH hH hI T

/-- Every strongly adapted continuous Itô integral of a `BrownianIntegrable` integrand is a true
martingale on the raw filtration, without assuming path continuity of `W`. -/
theorem martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨_, _, _, -, -, -, -, hMm, hmem, -, hlim⟩ := exists_simpleHolding_tendsto_l2Integral hW hH
  obtain ⟨Z, hZm, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hMm hmem fun T ↦ (hlim T).cauchySeq
  refine hZm.congr hI_adap fun T ↦ ?_
  have heq : (hZlim T).1.toLp (Z T) = (hI.memLp hW hH T).toLp (I T) :=
    (tendsto_nhds_unique (tendsto_iff_edist_tendsto_0.mpr <| by
      simpa only [Lp.edist_toLp_toLp] using (hZlim T).2) (hlim T)).trans
      (hI.toLp_eq_l2Integral hW hH T).symm
  exact ((heq ▸ (hZlim T).1.coeFn_toLp).symm).trans (hI.memLp hW hH T).coeFn_toLp

end IsItoIntegral

end TauCeti
