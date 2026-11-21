/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Simple
public import TauCeti.Probability.BrownianMotion.Integral.Wiener
public import Mathlib.Probability.Martingale.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.BrownianMotion.Integral.Deterministic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The square-integrable Itô integral process and Itô's isometry

Where `MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)`, this file identifies
`TauCeti.Probability.IsItoIntegral` almost surely with `IsFilteredPreBrownianReal.l2Integral`
(`ae_eq_l2Integral`) and deduces `L²` membership (`memLp_two`), zero expectation
(`integral_eq_zero`), covariance (`integral_mul`), Itô's isometry (`integral_sq`), and for
deterministic `L²` integrands identification with `wienerIntegral` (`ae_eq_wienerIntegral`) and its
centered Gaussian law (`hasLaw_gaussianReal`). For `TauCeti.BrownianIntegrable` integrands, every
strongly adapted Itô integral is a martingale (`martingale`), and when `W` has a.s. continuous
paths a predictable a.s. continuous martingale Itô integral exists (`exists_isItoIntegral`).

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

namespace Probability.IsItoIntegral

/-- Against a filtered pre-Brownian motion, every Itô integral of an integrand with finite expected
square energy on `(0, t]` agrees almost surely at `t` with `hW.l2Integral t`. -/
theorem ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH).toLp
        (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  choose n τ a C _ hτ ha hb herr using fun m : ℕ ↦
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t hI.isStronglyPredictable hH
      (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  have hhold := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun m ↦ (herr m).le
  exact tendstoInMeasure_ae_unique
    (hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero hhold hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hI.isStronglyPredictable hH
        (fun m ↦ (hτ m).monotoneOn) ha
        (fun m j hj ↦ .of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
          (.of_forall (hb m j hj))) hhold))

/-- Against a filtered pre-Brownian motion, every Itô integral of a deterministic `L²` integrand
`u` agrees almost surely at horizon `t` with `hW.toIsPreBrownianReal.wienerIntegral`. -/
theorem ae_eq_wienerIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {u : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ u s) I) {t : ℝ≥0}
    (hu : MemLp u 2 (timeMeasure t)) :
    I t =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral t (hu.toLp u) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h := hI.ae_eq_l2Integral hW (hu.comp_measurePreserving measurePreserving_fst)
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rwa [← hW.l2Integral_compMeasurePreserving_fst t (hu.toLp u),
    Lp.toLp_compMeasurePreserving hu (ℱ.measurePreserving_fst_predictableMeasure P t)]

/-- Against a filtered pre-Brownian motion, every Itô integral of a deterministic `L²` integrand
`u` is centered Gaussian at horizon `t` with variance `∫ s, u s ^ 2 ∂Probability.timeMeasure t`. -/
theorem hasLaw_gaussianReal (hW : IsFilteredPreBrownianReal ℱ W P) {u : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ u s) I) {t : ℝ≥0}
    (hu : MemLp u 2 (timeMeasure t)) :
    HasLaw (I t) (gaussianReal 0 (Real.toNNReal (∫ s, u s ^ 2 ∂timeMeasure t))) P := by
  have hvar : ‖hu.toLp u‖₊ ^ 2 = Real.toNNReal (∫ s, u s ^ 2 ∂timeMeasure t) :=
    NNReal.eq <| by
      simpa only [NNReal.coe_pow, coe_nnNorm, Real.norm_eq_abs, sq_abs, hu.norm_toLp_sq] using
        (Real.coe_toNNReal _ (integral_nonneg fun _ ↦ sq_nonneg _)).symm
  exact hvar ▸ (hW.toIsPreBrownianReal.hasLaw_wienerIntegral t (hu.toLp u)).congr
    (hI.ae_eq_wienerIntegral hW hu)

/-- Every Itô integral with finite expected square energy on `(0, t]` lies in `L²(P)`. -/
theorem memLp_two (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH).symm

/-- Every Itô integral against `W` with finite expected square energy on `(0, t]` has zero mean. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH)).trans (hW.integral_l2Integral t _)

/-- **Itô's covariance identity.** Against a filtered pre-Brownian motion, the inner product of two
Itô integrals at horizon `t` with finite expected square energy on `(0, t]` equals the time-product
integral of `H * K` on `(0, t] × Ω`. -/
theorem integral_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P))
    (hK : MemLp (Function.uncurry K) 2 ((timeMeasure t).prod P)) :
    ∫ ω, I t ω * J t ω ∂P =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hHp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH
  let hKp := (ℱ.memLp_predictableMeasure_iff P hJ.isStronglyPredictable t 2).2 hK
  have hlhs : ∫ ω, I t ω * J t ω ∂P =
      ⟪hW.l2Integral t (hHp.toLp _), hW.l2Integral t (hKp.toLp _)⟫_ℝ :=
    (integral_congr_ae <| (hI.ae_eq_l2Integral hW hH).mp <| (hJ.ae_eq_l2Integral hW hK).mono
      fun _ h₂ h₁ ↦ by simp [h₁, h₂, mul_comm]).trans (L2.inner_def _ _).symm
  rw [hlhs, (hW.l2Integral t).inner_map_map, L2.inner_def]
  exact (integral_congr_ae <| hHp.coeFn_toLp.mp <|
    hKp.coeFn_toLp.mono fun _ h₂ h₁ ↦ by simp [h₁, h₂, Function.uncurry, mul_comm]).trans
    (ℱ.integral_predictableMeasure P (hI.isStronglyPredictable.mul hJ.isStronglyPredictable) t)

/-- **Itô's `L²` isometry.** The second moment of an Itô integral at horizon `t` with finite
expected square energy on `(0, t]` equals its expected square energy on `(0, t] × Ω`. -/
theorem integral_sq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  simpa only [sq] using hI.integral_mul hW hI hH hH

/-- Against a filtered pre-Brownian motion, any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a true martingale on the raw filtration. -/
theorem martingale (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H)
    (hAdapt : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hhold⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  refine martingale_of_tendsto_eLpNorm_one
    (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩) hAdapt fun t ↦
    MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≤ 2) <|
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hH.isStronglyPredictable (hH.memLp_timeMeasure t)
        (fun m ↦ (hτ m).monotoneOn) ha (fun m j hj ↦ .of_bound
          ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (.of_forall (hb m j hj)))
        (hhold t)).congr fun _ ↦ eLpNorm_congr_ae
          (EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hW (hH.memLp_timeMeasure t)).symm)

end Probability.IsItoIntegral

/-- **Existence of the `L²` Brownian Itô integral process.** Against a filtered pre-Brownian motion
`W` with almost surely continuous paths, every `BrownianIntegrable` integrand admits a predictable
almost surely continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, Probability.IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hhold⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    .of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (.of_forall (hb m j hj))
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (Finance.simpleGains (τ m) (n m) (a m) W t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) t
      (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) t))
  obtain ⟨I, hImart, hIpred, hIlim, _, _, _, hIpath⟩ := exists_continuous_martingale_of_cauchySeq_Lp
    (p := 2) (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
    (fun _ ↦ hcont.mono fun _ hω ↦ Finance.continuous_simpleGains hω) hmem fun t ↦
      let g := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
      Tendsto.cauchySeq (x := (Lp.memLp g).toLp g) <|
        (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun m ↦ hmem m t) g (Lp.memLp g)).2
          (hW.tendsto_eLpNorm_simpleGains_l2Integral hH.isStronglyPredictable
            (hH.memLp_timeMeasure t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (hhold t))
  exact ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦
    ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero (hhold t) hε,
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hIlim t).2⟩⟩,
    hIpred, hImart⟩

end TauCeti
