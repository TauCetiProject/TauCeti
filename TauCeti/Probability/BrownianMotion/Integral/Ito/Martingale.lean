/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import Mathlib.Probability.Martingale.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The square-integrable Itô integral process and Itô's isometry

At any fixed deterministic horizon `t` where an integrand `H` has finite expected square energy
`MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)`, this file bridges
`TauCeti.IsItoIntegral` with the terminal-time Hilbert-space isometry
`IsFilteredPreBrownianReal.l2Integral`. For integrands in the all-horizons domain
`TauCeti.BrownianIntegrable ℱ P H`, it deduces the martingale property and constructs a predictable
almost surely continuous martingale Itô integral process on raw filtrations:

* `IsItoIntegral.ae_eq_l2Integral`: against a filtered pre-Brownian motion `W`, any Itô integral
  `I` of `H` agrees almost surely at horizon `t` with `hW.l2Integral t`.
* `IsItoIntegral.memLp_two`, `IsItoIntegral.integral_eq_zero`, `IsItoIntegral.integral_mul`,
  `IsItoIntegral.integral_sq`: fixed-horizon `L²` membership (`MemLp (I t) 2 P`), zero expectation,
  cross-covariance identity, and Itô's `L²` isometry, assuming finite expected square energy only
  at `t` and requiring neither path continuity of `W` nor adaptation of `I`.
* `IsItoIntegral.martingale`: any strongly adapted Itô integral of a `BrownianIntegrable`
  integrand against a filtered pre-Brownian motion satisfies `Martingale I ℱ P`.
* `BrownianIntegrable.exists_isItoIntegral`: against a filtered pre-Brownian motion `W` with almost
  surely continuous paths, every `BrownianIntegrable` integrand admits a predictable almost surely
  continuous martingale Itô integral.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

namespace IsItoIntegral

/-- Against a filtered pre-Brownian motion, every Itô integral of an integrand with finite expected
square energy on `(0, t]` agrees almost surely at `t` with the terminal-time predictable `L²`
integral `hW.l2Integral t`. Neither path continuity of `W` nor adaptation of `I` is needed. -/
theorem ae_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH).toLp
        (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hex (m : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t
    hI.isStronglyPredictable hH (ε := (m : ℝ≥0∞)⁻¹)
    (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  choose n τ a C _ hτ ha hb herr using hex
  have hhold : Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure t).prod P)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun m ↦ (herr m).le
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  have h1 := hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun _ hε ↦
    TauCeti.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm hhold hε
  have h2 := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (hW.tendsto_eLpNorm_simpleGains_l2Integral hI.isStronglyPredictable hH
      (fun m ↦ (hτ m).monotoneOn) ha ha₂ hhold)
  exact tendstoInMeasure_ae_unique h1 h2

/-- Against a filtered pre-Brownian motion, every Itô integral whose integrand has finite expected
square energy on `(0, t]` belongs to `L²(P)` at horizon `t`. -/
theorem memLp_two (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH).symm

/-- Against a filtered pre-Brownian motion, every Itô integral whose integrand has finite expected
square energy on `(0, t]` has expectation zero at horizon `t`. -/
theorem integral_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH)).trans (hW.integral_l2Integral t _)

/-- **Itô's covariance identity.** Against a filtered pre-Brownian motion, the inner product of
two Itô integrals at horizon `t` whose integrands have finite expected square energy on `(0, t]`
equals the time-product integral of the product of their integrands on `(0, t] × Ω`. -/
theorem integral_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P))
    (hK : MemLp (Function.uncurry K) 2 ((Probability.timeMeasure t).prod P)) :
    ∫ ω, I t ω * J t ω ∂P =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(Probability.timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hHp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH
  let hKp := (ℱ.memLp_predictableMeasure_iff P hJ.isStronglyPredictable t 2).2 hK
  let fH := hHp.toLp (Function.uncurry H)
  let fK := hKp.toLp (Function.uncurry K)
  have hlhs : ∫ ω, I t ω * J t ω ∂P = ⟪hW.l2Integral t fH, hW.l2Integral t fK⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hI.ae_eq_l2Integral hW hH, hJ.ae_eq_l2Integral hW hK] with ω hIω hJω
    simp [fH, fK, hIω, hJω, mul_comm]
  rw [hlhs, (hW.l2Integral t).inner_map_map, L2.inner_def]
  have hrhs : ∫ p, ⟪fH p, fK p⟫_ℝ ∂ℱ.predictableMeasure P t =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂ℱ.predictableMeasure P t := by
    refine integral_congr_ae ?_
    filter_upwards [hHp.coeFn_toLp, hKp.coeFn_toLp] with p hpH hpK
    simp [fH, fK, hpH, hpK, Function.uncurry, mul_comm]
  exact hrhs.trans
    (ℱ.integral_predictableMeasure P (hI.isStronglyPredictable.mul hJ.isStronglyPredictable) t)

/-- **Itô's `L²` isometry.** Against a filtered pre-Brownian motion, the second moment of an Itô
integral at horizon `t` whose integrand has finite expected square energy on `(0, t]` equals its
expected square energy on `(0, t] × Ω`. -/
theorem integral_sq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure t).prod P := by
  simpa only [sq] using hI.integral_mul hW hI hH hH

/-- Against a filtered pre-Brownian motion, any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a true martingale on the raw filtration. -/
theorem martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H)
    (hAdapt : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hhold⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hM (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  refine martingale_of_tendsto_eLpNorm_one hM hAdapt fun t ↦ ?_
  have hgains := hW.tendsto_eLpNorm_simpleGains_l2Integral hH.isStronglyPredictable
    (hH.memLp_timeMeasure t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (hhold t)
  refine MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≤ 2) ?_
  refine hgains.congr fun m ↦ ?_
  exact eLpNorm_congr_ae
    (EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hW (hH.memLp_timeMeasure t)).symm)

end IsItoIntegral

/-- **Existence of the `L²` Brownian Itô integral process.** Against a filtered pre-Brownian
motion `W` with almost surely continuous paths, every `BrownianIntegrable` integrand admits a
predictable almost surely continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hhold⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have hM (m : ℕ) : Martingale (M m) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  have hcM (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ M m t ω) :=
    hcont.mono fun _ hω ↦ hω.simpleGains
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) (ha₂ m) t)
  have hcau (t : ℝ≥0) : CauchySeq (fun m ↦ (hmem m t).toLp (M m t)) := by
    let g := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
    refine Tendsto.cauchySeq (x := (Lp.memLp g).toLp g) ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun m ↦ M m t) (fun m ↦ hmem m t)
      g (Lp.memLp g)).2 <| hW.tendsto_eLpNorm_simpleGains_l2Integral hH.isStronglyPredictable
        (hH.memLp_timeMeasure t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (hhold t)
  obtain ⟨I, hImart, hIpred, hIlim, _, _, _, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2) hM hcM hmem hcau
  refine ⟨I, ⟨hH.isStronglyPredictable, Filter.Eventually.mono hIpath fun _ h ↦ h.1,
    fun t ↦ ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm (hhold t) hε,
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hIlim t).2⟩⟩,
    hIpred, hImart⟩

end TauCeti
