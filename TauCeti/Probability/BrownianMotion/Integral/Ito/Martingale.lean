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

At any horizon `t` where `MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)`, this
file identifies `TauCeti.IsItoIntegral` almost surely with `IsFilteredPreBrownianReal.l2Integral`
(`ae_eq_l2Integral`) and deduces `L²` membership (`memLp_two`), zero expectation
(`integral_eq_zero`), covariance (`integral_mul`), and Itô's isometry (`integral_sq`), requiring
neither path continuity of `W` nor adaptation of `I`. For `TauCeti.BrownianIntegrable` integrands,
every strongly adapted Itô integral is a martingale (`martingale`), and when `W` has almost surely
continuous paths there exists a predictable almost surely continuous martingale Itô integral
(`BrownianIntegrable.exists_isItoIntegral`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §3.2.B–C.
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
square energy on `(0, t]` agrees almost surely at `t` with `hW.l2Integral t`. -/
theorem ae_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH).toLp
        (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  choose n τ a C _ hτ ha hb herr using fun m : ℕ ↦
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t hI.isStronglyPredictable hH
      (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  have hhold : Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure t).prod P)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun m ↦ (herr m).le
  exact tendstoInMeasure_ae_unique
    (hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm hhold hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hI.isStronglyPredictable hH
        (fun m ↦ (hτ m).monotoneOn) ha
        (fun m j hj ↦ .of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
          (.of_forall (hb m j hj))) hhold))

/-- Against a filtered pre-Brownian motion, every Itô integral whose integrand has finite expected
square energy on `(0, t]` belongs to `L²(P)` at horizon `t`. -/
theorem memLp_two (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) : MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH).symm

/-- Against a filtered pre-Brownian motion, every Itô integral whose integrand has finite expected
square energy on `(0, t]` has expectation zero at horizon `t`. -/
theorem integral_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH)).trans (hW.integral_l2Integral t _)

/-- **Itô's covariance identity.** Against a filtered pre-Brownian motion, the inner product of two
Itô integrals at horizon `t` with finite expected square energy on `(0, t]` equals the time-product
integral of `H * K` on `(0, t] × Ω`. -/
theorem integral_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P))
    (hK : MemLp (Function.uncurry K) 2 ((Probability.timeMeasure t).prod P)) :
    ∫ ω, I t ω * J t ω ∂P =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(Probability.timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hHp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH
  let hKp := (ℱ.memLp_predictableMeasure_iff P hJ.isStronglyPredictable t 2).2 hK
  have hlhs : ∫ ω, I t ω * J t ω ∂P =
      ⟪hW.l2Integral t (hHp.toLp _), hW.l2Integral t (hKp.toLp _)⟫_ℝ := by
    rw [L2.inner_def]; refine integral_congr_ae ?_
    filter_upwards [hI.ae_eq_l2Integral hW hH, hJ.ae_eq_l2Integral hW hK] with ω hIω hJω
    simp [hIω, hJω, mul_comm]
  rw [hlhs, (hW.l2Integral t).inner_map_map, L2.inner_def]
  refine (integral_congr_ae ?_).trans
    (ℱ.integral_predictableMeasure P (hI.isStronglyPredictable.mul hJ.isStronglyPredictable) t)
  filter_upwards [hHp.coeFn_toLp, hKp.coeFn_toLp] with p hpH hpK
  simp [hpH, hpK, Function.uncurry, mul_comm]

/-- **Itô's `L²` isometry.** Against a filtered pre-Brownian motion, the second moment of an Itô
integral at horizon `t` with finite expected square energy on `(0, t]` equals its expected square
energy on `(0, t] × Ω`. -/
theorem integral_sq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure t).prod P := by
  simpa only [sq] using hI.integral_mul hW hI hH hH

/-- Against a filtered pre-Brownian motion, any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a true martingale on the raw filtration. -/
theorem martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H)
    (hAdapt : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hhold⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  refine martingale_of_tendsto_eLpNorm_one
    (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩) hAdapt fun t ↦
    MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≤ 2) <|
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hH.isStronglyPredictable (hH.memLp_timeMeasure t)
        (fun m ↦ (hτ m).monotoneOn) ha
        (fun m j hj ↦ .of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
          (.of_forall (hb m j hj))) (hhold t)).congr fun _ ↦
        eLpNorm_congr_ae
          (EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hW (hH.memLp_timeMeasure t)).symm)

end IsItoIntegral

/-- **Existence of the `L²` Brownian Itô integral process.** Against a filtered pre-Brownian motion
`W` with almost surely continuous paths, every `BrownianIntegrable` integrand admits a predictable
almost surely continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hhold⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    .of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (.of_forall (hb m j hj))
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) (ha₂ m) t)
  obtain ⟨I, hImart, hIpred, hIlim, _, _, _, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2)
      (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
        ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
      (fun _ ↦ hcont.mono fun _ hω ↦ hω.simpleGains) hmem fun t ↦ by
        let g := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
        exact Tendsto.cauchySeq (x := (Lp.memLp g).toLp g) <|
          (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun m ↦ M m t) (fun m ↦ hmem m t) g (Lp.memLp g)).2
            (hW.tendsto_eLpNorm_simpleGains_l2Integral hH.isStronglyPredictable
              (hH.memLp_timeMeasure t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (hhold t))
  exact ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦
    ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm (hhold t) hε,
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hIlim t).2⟩⟩,
    hIpred, hImart⟩

end TauCeti
