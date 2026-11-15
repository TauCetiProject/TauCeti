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

For a predictable integrand `H` in `TauCeti.BrownianIntegrable ℱ P H`, this module constructs a
predictable continuous martingale `I` satisfying `TauCeti.IsItoIntegral ℱ P W H I` whenever `W` is
a filtered pre-Brownian motion with almost-surely continuous paths, identifies every continuous Itô
integral of `H` at horizon `T` with the terminal predictable-`L²` isometric map
`IsFilteredPreBrownianReal.l2Integral`, and derives zero expectation, the polarized and quadratic
Itô isometries, and the martingale property.

Except for `BrownianIntegrable.exists_isItoIntegral`, which selects a continuous representative
from elementary Brownian gains and therefore uses sample-path continuity of `W`, all properties of
a given Itô integral (`ae_eq_l2Integral`, `memLp`, `toLp_eq_l2Integral`, `eLpNorm_eq`,
`integral_eq_zero`, `integral_mul`, `integral_sq`, and `martingale`) hold for any
`IsFilteredPreBrownianReal ℱ W P` on a raw filtration without assuming path continuity of `W`,
completeness, or right continuity of `ℱ`.

## Main results

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: existence of a predictable continuous
  martingale Itô integral for `BrownianIntegrable` integrands.
* `TauCeti.IsItoIntegral.ae_eq_l2Integral`, `memLp`, `toLp_eq_l2Integral`: identification of `I T`
  with `hW.l2Integral T` in `L²(P)` at every finite horizon.
* `TauCeti.IsItoIntegral.eLpNorm_eq`, `integral_eq_zero`, `integral_mul`, `integral_sq`: zero
  expectation and the polarized and quadratic Itô isometries at every finite horizon.
* `TauCeti.IsItoIntegral.martingale`: every strongly adapted continuous Itô integral of a
  `BrownianIntegrable` integrand against a filtered pre-Brownian motion is a true martingale.

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
  have hMm (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb m j hj ω⟩
  have hmem (m : ℕ) (T : ℝ≥0) : MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P :=
    hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T
  refine ⟨n, τ, a, C, hτ, ha, hb, hMm, hmem, herr, fun T ↦ ?_⟩
  let u (m : ℕ) := (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).toLp
    (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))
  let uH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  have hu : Tendsto u atTop (𝓝 uH) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine (herr T).congr fun m ↦ ?_
    have hs : StronglyMeasurable[ℱ.predictable]
        (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)) - Function.uncurry H) :=
      (Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable
    rw [Lp.edist_toLp_toLp, ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hs]
    rfl
  have hmap := ((hW.l2Integral T).continuous.tendsto uH).comp hu
  refine hmap.congr fun m ↦ ?_
  exact hW.l2Integral_toLp_simpleHolding (hτ m).monotoneOn (ha m) (ha₂ m) T

/-- **Existence of the continuous `L²` Brownian Itô integral**: every `BrownianIntegrable`
integrand against a filtered pre-Brownian motion `W` with almost-surely continuous paths admits a
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
  have hcm (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω) := by
    filter_upwards [hcont] with ω hω
    simp only [Finance.simpleGains_def]
    fun_prop
  obtain ⟨I, hIm, hIp, hIlim, -, _φ, -, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp hMm hcm hmem fun T ↦ (hlim T).cauchySeq
  refine ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦ ?_⟩, hIp, hIm⟩
  refine ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun m j hj ↦ ⟨C m, hb m j hj⟩, ?_, ?_⟩
  · exact fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (.of_forall fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (herr t) hε
  · exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2

namespace IsItoIntegral

/-- Every continuous Itô integral `I` of a `BrownianIntegrable` integrand `H` against a filtered
pre-Brownian motion `W` agrees `P`-almost surely at horizon `T` with the terminal predictable-`L²`
Brownian integral `hW.l2Integral T`, without assuming path continuity of `W`. -/
theorem ae_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hτ, ha, -, -, hmem, herr, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  let v := hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))
  have hl2 : Tendsto (fun m ↦ eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T - (v : Ω → ℝ)) 2 P)
      atTop (𝓝 0) := by
    have hed : Tendsto (fun m ↦ edist ((hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T))
        v) atTop (𝓝 0) := tendsto_iff_edist_tendsto_0.mp (hlim T)
    refine hed.congr fun m ↦ ?_
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae (((hmem m T).coeFn_toLp).sub .rfl)
  exact hI.ae_eq_of_approx hW (fun m ↦ (hτ m).monotoneOn) ha
    (fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (.of_forall fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (herr T) hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hl2)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand against a filtered
pre-Brownian motion `W` belongs to `L²(P)` at each finite horizon, without assuming path continuity
of `W`. -/
theorem memLp (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    MemLp (I T) 2 P :=
  (Lp.memLp (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)))).ae_eq
    (hI.ae_eq_l2Integral hW hH T).symm

/-- At every finite horizon `T`, the `L²(P)` class of a continuous Itô integral `I` of a
`BrownianIntegrable` integrand `H` against a filtered pre-Brownian motion `W` equals
`hW.l2Integral T` applied to the predictable-`L²` class of `H`, without assuming path continuity of
`W`. -/
theorem toLp_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    (hI.memLp hW hH T).toLp (I T) =
      hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) :=
  Lp.ext ((hI.memLp hW hH T).coeFn_toLp.trans (hI.ae_eq_l2Integral hW hH T))

/-- **`L²`-seminorm Itô isometry**: for any continuous Itô integral `I` of a `BrownianIntegrable`
integrand `H` against a filtered pre-Brownian motion `W`, the `L²(P)` seminorm of `I T` equals the
`L²((timeMeasure T).prod P)` seminorm of `H` at every finite horizon `T`, without assuming path
continuity of `W`. -/
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

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand against a filtered
pre-Brownian motion `W` has expectation zero at every finite horizon, without assuming path
continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

/-- **Polarized Itô isometry**: for continuous Itô integrals `I` of `H` and `J` of `K` against a
filtered pre-Brownian motion `W` with `H` and `K` in `BrownianIntegrable ℱ P`,
`E[I T · J T] = E[∫_{(0, T]} H K]` at every finite horizon `T`, without assuming path continuity of
`W`. -/
theorem integral_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(Probability.timeMeasure T).prod P := by
  let uH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  let uK := (hK.memLp_predictableMeasure T).toLp (Function.uncurry K)
  have hmap := (hW.l2Integral T).inner_map_map uK uH
  rw [← hJ.toLp_eq_l2Integral hW hK T, ← hI.toLp_eq_l2Integral hW hH T,
    L2.inner_def, L2.inner_def] at hmap
  have h1 := integral_congr_ae (((hI.memLp hW hH T).coeFn_toLp).mul ((hJ.memLp hW hK T).coeFn_toLp))
  have h2 := integral_congr_ae
    (((hH.memLp_predictableMeasure T).coeFn_toLp).mul ((hK.memLp_predictableMeasure T).coeFn_toLp))
  simp only [RCLike.inner_apply, conj_trivial] at hmap
  simp only [Pi.mul_apply] at h1 h2
  rw [← h1, hmap, h2]
  exact ℱ.integral_predictableMeasure P
    (hH.isStronglyPredictable.mul hK.isStronglyPredictable) T

/-- **Bochner-integral Itô isometry**: for any continuous Itô integral `I` of a
`BrownianIntegrable` integrand `H` against a filtered pre-Brownian motion `W`,
`E[(I T)²] = E[∫_{(0, T]} H²]` at every finite horizon `T`, without assuming path continuity of
`W`. -/
theorem integral_sq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure T).prod P := by
  simpa only [sq] using hI.integral_mul hW hH hH hI T

/-- Every strongly adapted continuous Itô integral of a `BrownianIntegrable` integrand against a
filtered pre-Brownian motion `W` is a true martingale on the raw filtration, without assuming path
continuity of `W`. -/
theorem martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨n, τ, a, -, -, -, -, hMm, hmem, -, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  obtain ⟨Z, hZm, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hMm hmem fun T ↦ (hlim T).cauchySeq
  refine hZm.congr hI_adap fun T ↦ ?_
  have hZ_toLp : Tendsto (fun m ↦ (hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T))
      atTop (𝓝 ((hZlim T).1.toLp (Z T))) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp] using (hZlim T).2
  have heq : (hZlim T).1.toLp (Z T) = (hI.memLp hW hH T).toLp (I T) :=
    (tendsto_nhds_unique hZ_toLp (hlim T)).trans (hI.toLp_eq_l2Integral hW hH T).symm
  have hcoe := (hZlim T).1.coeFn_toLp
  rw [heq] at hcoe
  exact hcoe.symm.trans (hI.memLp hW hH T).coeFn_toLp

end IsItoIntegral

end TauCeti
