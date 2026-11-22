/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Square
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
public import TauCeti.Probability.Process.AccumulatedEnergy
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

/-!
# L² theory of the Itô stochastic integral

For a `TauCeti.BrownianIntegrable` integrand `H` and a filtered pre-Brownian motion `W`, any
Itô integral `I` satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I` agrees almost surely at
each finite horizon `T` with the terminal L² integral `hW.l2Integral T`. In particular, `I T` has
mean zero, satisfies the cross-isometry against the time-product inner product, and—when strongly
adapted to `ℱ`—has `I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` as a true martingale on the raw
filtration. None of these identification, moment, or martingale properties require path continuity
of `W` or usual conditions on `ℱ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace

namespace TauCeti.BrownianIntegrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

/-- A Brownian-integrable process belongs to `L²` of the finite-horizon predictable measure. -/
theorem memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr (hH.memLp_timeMeasure T)

end TauCeti.BrownianIntegrable

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

/-- Pathwise Bochner square energy on `timeMeasure t` equals the real part of the `nnvolume`
accumulated energy. -/
theorem integral_sq_timeMeasure_eq_toReal_accumulatedEnergy
    (hH : IsStronglyPredictable ℱ H) (t : ℝ≥0) (ω : Ω) :
    (∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) =
      (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal := by
  have hHmeas : Measurable (fun s ↦ H s ω) :=
    ((hH.mono ℱ.predictable_le_prod).comp_measurable measurable_prodMk_right).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (hHmeas.pow_const 2).aestronglyMeasurable,
    TauCeti.nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc,
    TauCeti.Probability.timeMeasure_def, ← TauCeti.nnvolume_def]
  congr 1
  refine lintegral_congr fun s ↦ ?_
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]

/-- The elapsed pathwise Bochner square energy of a predictable process is again predictable. -/
theorem isStronglyPredictable_integral_sq_timeMeasure (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) := by
  have hpred : IsStronglyPredictable ℱ
      (fun t ω ↦ (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal) :=
    (ENNReal.measurable_toReal.comp
      (hH.isStronglyProgressive.isStronglyPredictable_accumulatedEnergy
        TauCeti.nnvolume).measurable).stronglyMeasurable
  have hfun : (fun t ω ↦ ∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) =
      fun t ω ↦ (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal :=
    funext fun t ↦ funext fun ω ↦ hH.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy t ω
  rwa [hfun]

end MeasureTheory.IsStronglyPredictable

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H K I J : ℝ≥0 → Ω → ℝ}

/-! ### Identification with the terminal L² integral and moments -/

private theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω -
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.fst p.snd - H p.fst p.snd) 2
        ((timeMeasure T).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let fK := (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
    (Function.uncurry (Finance.simpleHolding τ n a))
  let fH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  calc eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω - hW.l2Integral T fH ω) 2 P
      = edist (hW.l2Integral T fK) (hW.l2Integral T fH) := by
        rw [Lp.edist_def]
        exact eLpNorm_congr_ae
          ((hW.coeFn_l2Integral_simpleHolding hτ ha T
            (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T)).symm.sub EventuallyEq.rfl)
    _ = eLpNorm (⇑fK - ⇑fH) 2 (ℱ.predictableMeasure P T) := by
        rw [(hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
    _ = eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.fst p.snd - H p.fst p.snd) 2
          (ℱ.predictableMeasure P T) :=
        eLpNorm_congr_ae ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp.sub
          (hH.memLp_predictableMeasure T).coeFn_toLp)
    _ = eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.fst p.snd - H p.fst p.snd) 2
          ((timeMeasure T).prod P) := by
        rw [ℱ.predictableMeasure_def]
        exact eLpNorm_trim ℱ.predictable_le_prod
          ((Finance.isStronglyPredictable_simpleHolding ha).sub hH.isStronglyPredictable)

private theorem exists_simpleHolding_approx (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      (∀ k j, j < n k → MemLp (a k j) 2 P) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦
          Finance.simpleHolding (τ k) (n k) (a k) p.fst p.snd - H p.fst p.snd)
          2 ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      (∀ T ε, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
          ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
          atTop (𝓝 0)) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W T ω -
          hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) ω) 2 P)
          atTop (𝓝 0)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  refine ⟨n, τ, a, C, fun k ↦ (hτ k).monotoneOn, ha, hb, ha₂, hlim,
    fun T ε hε ↦ TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm
      (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (hlim T) hε,
    fun T ↦ by
      simpa only [fun k ↦
        hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) T] using hlim T⟩

/-- **Agreement with the terminal L² integral.** For a Brownian-integrable integrand, any Itô
integral agrees almost surely at each finite horizon `T` with `hW.l2Integral T`. Path continuity
of `W` is not required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  obtain ⟨n, τ, a, -, hτ, ha, -, -, -, hE, hL2⟩ := hW.exists_simpleHolding_approx hH
  exact hI.ae_eq_of_tendstoInMeasure hW hτ ha (hE T)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hL2 T))

/-- **L² characterization of Itô integrals.** For a Brownian-integrable integrand `H`, an almost
surely continuous process `I` is an Itô integral of `H` if and only if `I T` agrees almost surely
with the terminal `L²` integral `hW.l2Integral T` at every horizon `T`. Path continuity of `W` is
not required. -/
theorem isItoIntegral_iff_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) :
    IsItoIntegral ℱ P W H I ↔
      ∀ T : ℝ≥0, I T =ᵐ[P]
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  refine ⟨fun hI T ↦ hW.ae_eq_l2Integral_of_isItoIntegral hH hI T, fun hT ↦ ?_⟩
  obtain ⟨n, τ, a, -, hτ, ha, -, -, -, hE, hL2⟩ := hW.exists_simpleHolding_approx hH
  refine ⟨hH.isStronglyPredictable, hIcont, fun T ↦
    ⟨n, τ, a, hτ, ha, hE T,
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        ((hL2 T).congr fun k ↦ eLpNorm_congr_ae (EventuallyEq.rfl.sub (hT T).symm))⟩⟩

/-- Every Itô integral of a Brownian-integrable process has expectation zero at each horizon. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Itô cross-isometry.** The covariance of two Brownian-integrable Itô integrals at horizon `t`
equals the time-product inner product of their integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (t : ℝ≥0) :
    ∫ ω, I t ω * J t ω ∂P = ∫ p, H p.fst p.snd * K p.fst p.snd ∂(timeMeasure t).prod P := by
  let f := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let g := (hK.memLp_predictableMeasure t).toLp (Function.uncurry K)
  calc ∫ ω, I t ω * J t ω ∂P
      = ⟪hW.l2Integral t f, hW.l2Integral t g⟫_ℝ := by
        rw [real_inner_comm, L2.inner_def]
        exact integral_congr_ae <| (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).mp <|
          (hW.ae_eq_l2Integral_of_isItoIntegral hK hJ t).mono fun _ hJω hIω ↦ by
            simp [f, g, hIω, hJω]
    _ = ∫ p, H p.fst p.snd * K p.fst p.snd ∂ℱ.predictableMeasure P t := by
        rw [(hW.l2Integral t).inner_map_map, real_inner_comm, L2.inner_def]
        exact integral_congr_ae <| (hH.memLp_predictableMeasure t).coeFn_toLp.mp <|
          (hK.memLp_predictableMeasure t).coeFn_toLp.mono fun _ hpK hpH ↦ by
            simp only [RCLike.inner_apply, conj_trivial, f, g, hpH, hpK]; rfl
    _ = ∫ p, H p.fst p.snd * K p.fst p.snd ∂(timeMeasure t).prod P :=
        ℱ.integral_predictableMeasure P
          (hH.isStronglyPredictable.mul hK.isStronglyPredictable) t

/-! ### L² square compensation -/

private theorem simpleHolding_energy_eq_integral_sq {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n)) (t : ℝ≥0) (ω : Ω) :
    (∑ j ∈ Finset.range n, a j ω ^ 2 * (↑(min (τ (j + 1)) t) - ↑(min (τ j) t))) =
      ∫ s, Finance.simpleHolding τ n a s ω ^ 2 ∂timeMeasure t := by
  have hKmeas : Measurable (fun s ↦ Finance.simpleHolding τ n a s ω) := by
    simp only [Finance.simpleHolding_def]
    exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (hKmeas.pow_const 2).aestronglyMeasurable,
    lintegral_congr fun s ↦ by
      rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm],
    Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hτ,
    ENNReal.toReal_sum (fun _ _ ↦
      ENNReal.mul_ne_top (ENNReal.pow_ne_top eNorm_ne_top) ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hle : τ j ≤ τ (j + 1) := hτ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, Real.norm_eq_abs, sq_abs]
  by_cases hT : τ j ≤ t
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_min hle hT))),
      min_eq_left hT]
  · have hT' : t ≤ τ j := (not_le.mp hT).le
    rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr
      ((min_le_right _ _).trans hT')))]
    simp [min_eq_right hT', min_eq_right (hT'.trans hle)]

/-- **L² Itô square compensation (quadratic variation bracket).** For a Brownian-integrable
integrand and a strongly adapted Itô integral `I`, the process
`I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a true martingale on the raw filtration.
Path continuity of `W` is not required. -/
theorem martingale_sq_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
      |>.isStronglyProgressive.stronglyAdapted
  obtain ⟨n, τ, a, -, hτ, ha, -, ha₂, hlim, -, hL2⟩ := hW.exists_simpleHolding_approx hH
  let B (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j ∈ Finset.range (n k), a k j ω ^ 2 * (↑(min (τ k (j + 1)) t) - ↑(min (τ k j) t))
  refine martingale_of_tendsto_eLpNorm_one
    (fun k ↦ hW.martingale_sq_simpleGains_sub (hτ k) (ha k) (ha₂ k))
    (fun t ↦ (hI_adapt t).pow 2 |>.sub (hA_adapt t)) fun t ↦ ?_
  have hsq_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_sq_sub_one (hI.memLp hW hH t).eLpNorm_ne_top <|
      (hL2 t).congr fun k ↦
        eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm)
  have henergy_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    have hHmem : MemLp (fun p : ℝ≥0 × Ω ↦ H p.fst p.snd) 2 ((timeMeasure t).prod P) :=
      hH.memLp_timeMeasure t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_sq_sub_one hHmem.eLpNorm_ne_top (hlim t)) (fun _ ↦ zero_le)
      fun k ↦ ?_
    simp_rw [B, simpleHolding_energy_eq_integral_sq (hτ k) t]
    have hBA_sm : AEStronglyMeasurable
        (fun ω ↦ (∫ s, Finance.simpleHolding (τ k) (n k) (a k) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha k))
        |>.isStronglyPredictable_integral_sq_timeMeasure.isStronglyProgressive.stronglyAdapted t
        |>.mono (ℱ.le t)).sub ((hA_adapt t).mono (ℱ.le t)))).aestronglyMeasurable
    have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ k) (n k) (a k) p.fst p.snd ^ 2 - H p.fst p.snd ^ 2) :=
      (((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
        ℱ.predictable_le_prod).pow 2).sub
        ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).pow 2)
    rw [eLpNorm_one_eq_lintegral_eNorm hBA_sm,
      eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
      lintegral_prod_symm _ hdiff_sm.measurable.eNorm.aemeasurable]
    refine lintegral_mono_ae <| hH.locallyBrownianIntegrable.ae_memLp.mono fun ω hω ↦ ?_
    have hH2 : MemLp (fun s ↦ H s ω) 2 (timeMeasure t) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using hω t
    have hK2 : MemLp (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) 2 (timeMeasure t) := by
      simp only [Finance.simpleHolding_def]
      exact memLp_finsetSum _ fun j _ ↦
        (memLp_const (a k j ω)).indicator measurableSet_Ioc.nullMeasurableSet
    rw [← integral_sub hK2.integrable_sq hH2.integrable_sq]
    exact eNorm_integral_le_lintegral_eNorm _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hsq_lim.add henergy_lim) (fun _ ↦ zero_le) fun k ↦ ?_
  have hsplit : ((fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - B k t ω) -
      (fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t)) =
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) -
        (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) := by ext ω; simp; ring
  rw [hsplit]; exact eLpNorm_sub_le le_rfl

end TauCeti.Probability.IsFilteredPreBrownianReal
