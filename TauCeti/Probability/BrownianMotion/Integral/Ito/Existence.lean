/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.OptionalStopping
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.LocalProperty
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping

/-!
# Existence and properties of the continuous-time Brownian Itô integral

For a filtration-relative Brownian motion `W` with almost surely continuous paths and a locally
square-integrable predictable integrand `H` (`TauCeti.LocallyBrownianIntegrable ℱ P H`), this file
proves linearity, vanishing at `0`, existence, local-martingale regularity, optional stopping, and
local pathwise congruence for `TauCeti.Probability.IsItoIntegral` on the original raw filtration.

Directly from the `IsItoIntegral` specification, every Itô integral vanishes almost surely at `0`
(`IsItoIntegral.ae_eval_zero`) and the relation is closed under linear combinations
(`IsItoIntegral.add`, `IsItoIntegral.const_mul`, `IsItoIntegral.neg`, `IsItoIntegral.sub`).

Existence (`exists_isItoIntegral`) localizes `H` by closed-level hits of its repaired energy clock
(`TauCeti.nnvolume.energyLocalizer`), constructs continuous martingale stages via
`exists_continuous_l2Integral`, verifies stage compatibility via `stoppedProcess_ae_eq_l2Integral`,
patches the stages without enlarging the filtration, and upgrades the patched local martingale to
an indistinguishable strongly predictable version. Stopping an Itô integral at any raw stopping
time `σ` represents `H` cut off to `⟦0, σ⟧` (`itoIntegral_stoppedProcess`), yielding local
congruence on stochastic intervals (`itoIntegral_local_congr`) and recovering the global `L²`
isometry and martingale properties when `H` is `BrownianIntegrable`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

section Spec

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

/-- The zero process is an Itô integral of the zero integrand. -/
theorem IsItoIntegral.zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := .of_forall fun _ ↦ continuous_const
  exists_approx t := ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0,
    fun _ _ _ _ _ _ ↦ le_rfl, fun _ _ h ↦ (Nat.not_lt_zero _ h).elim,
    fun ε hε ↦ tendsto_const_nhds.congr fun _ ↦ by
      simp [Finance.simpleHolding_def, not_le.mpr hε],
    fun ε hε ↦ by simp [Finance.simpleGains_def, not_le.mpr hε]⟩

/-- Product-almost-everywhere replacement of a predictable integrand on every finite horizon
preserves `IsItoIntegral`. -/
theorem IsItoIntegral.congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure t).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_approx t
    have hae_ω : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω) :=
      (Measure.ae_ae_comm (p := fun s ω ↦ H s ω = K s ω) (measurableSet_eq_fun
        (hI.isStronglyPredictable.mono ℱ.predictable_le_prod).measurable
        (hK.mono ℱ.predictable_le_prod).measurable)).mp (Measure.ae_ae_of_ae_prod (hHK t))
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hen ε hε).congr' (.of_forall fun k ↦
      measure_congr (hae_ω.mono fun ω hω ↦ ?_)), hg⟩
    simp only [mem_ofPred_eq]
    rw [lintegral_congr_ae (hω.mono fun s (hs : H s ω = K s ω) ↦ by rw [hs])]

/-- Every process satisfying `IsItoIntegral` vanishes almost surely at `0`, directly from the
elementary-approximation specification without Brownian, continuity, or integrability
hypotheses. -/
theorem IsItoIntegral.ae_eval_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨_, _, _, _, _, _, hg⟩ := hI.exists_approx 0
  exact tendstoInMeasure_ae_unique hg fun ε hε ↦ by simp [Finance.simpleGains_def, not_le.mpr hε]

/-- Scalar multiplication preserves `IsItoIntegral`. -/
theorem IsItoIntegral.const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.const_mul c
  ae_continuous := hI.ae_continuous.mono fun _ hc ↦ continuous_const.mul hc
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_approx t
    refine ⟨n, τ, fun k i ω ↦ c * a k i ω, hτ, fun k i hi ↦ (ha k i hi).const_mul c,
      fun ε hε ↦ ?_, (hg.const_smul c).congr_left fun k ↦ .of_forall fun ω ↦ by
        simp only [Finance.simpleGains_def, smul_eq_mul, Finset.mul_sum, mul_assoc]⟩
    have hhold (k : ℕ) (s : ℝ≥0) (ω : Ω) :
        Finance.simpleHolding (τ k) (n k) (fun i ω' ↦ c * a k i ω') s ω - c * H s ω =
          c * (Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω) := by
      simp only [Finance.simpleHolding_def, mul_sub, Finset.mul_sum]
      congr 1; exact sum_congr rfl fun i _ ↦ by
        by_cases hs : s ∈ Ioc (τ k i) (τ k (i + 1)) <;> simp [hs]
    by_cases hc : c = 0
    · subst hc
      exact tendsto_const_nhds.congr fun k ↦ (by simp_rw [hhold]; simp [not_le.mpr hε])
    · have hc2_ne0 : ‖c‖ₑ ^ 2 ≠ 0 := pow_ne_zero 2 (eNorm_ne_zero.mpr hc)
      have hc2_top : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
      refine (hen _ (ENNReal.div_pos hε.ne' hc2_top)).congr fun k ↦ congrArg P (Set.ext fun ω ↦ ?_)
      simp_rw [mem_ofPred_eq, hhold, eNorm_mul, mul_pow, lintegral_const_mul' _ _ hc2_top,
        ENNReal.div_le_iff' hc2_ne0 hc2_top]

/-- Negation preserves `IsItoIntegral`. -/
theorem IsItoIntegral.neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

private theorem exists_sum_simpleStrategy
    {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (ha₁ : ∀ i < n₁, StronglyMeasurable[ℱ (τ₁ i)] (a₁ i))
    (hτ₂ : MonotoneOn τ₂ (Iic n₂)) (ha₂ : ∀ i < n₂, StronglyMeasurable[ℱ (τ₂ i)] (a₂ i)) :
    ∃ (M : ℕ) (σ : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn σ (Iic M) ∧ (∀ j < M, StronglyMeasurable[ℱ (σ j)] (b j)) ∧
      (∀ s ω, Finance.simpleHolding σ M b s ω =
        Finance.simpleHolding τ₁ n₁ a₁ s ω + Finance.simpleHolding τ₂ n₂ a₂ s ω) ∧
      ∀ W t ω, Finance.simpleGains σ M b W t ω =
        Finance.simpleGains τ₁ n₁ a₁ W t ω + Finance.simpleGains τ₂ n₂ a₂ W t ω := by
  let l : Fin n₁ ⊕ Fin n₂ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ i) (fun j ↦ τ₂ j)
  let u : Fin n₁ ⊕ Fin n₂ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ (i + 1)) (fun j ↦ τ₂ (j + 1))
  let c : Fin n₁ ⊕ Fin n₂ → Ω → ℝ := Sum.elim (fun i ↦ a₁ i) (fun j ↦ a₂ j)
  have hc : ∀ x ∈ (Finset.univ : Finset (Fin n₁ ⊕ Fin n₂)), StronglyMeasurable[ℱ (l x)] (c x) := by
    rintro (i | j) _
    · exact ha₁ i i.isLt
    · exact ha₂ j j.isLt
  obtain ⟨M, σ, b, _, hσ, hb, _, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u c hc
  refine ⟨M, σ, b, hσ.monotoneOn, hb, fun s ω ↦ ?_, fun W t ω ↦ ?_⟩
  · rw [hhold s ω, Fintype.sum_sum_type, Finance.simpleHolding_def, Finance.simpleHolding_def,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]; rfl
  · rw [hgain W t ω, Fintype.sum_sum_type, Finance.simpleGains_def, Finance.simpleGains_def,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    exact congrArg₂ (· + ·)
      (sum_congr rfl fun i _ ↦ ite_eq_left
        (hτ₁ (mem_Iic.mpr i.isLt.le) (mem_Iic.mpr i.isLt) i.val.le_succ))
      (sum_congr rfl fun j _ ↦ ite_eq_left
        (hτ₂ (mem_Iic.mpr j.isLt.le) (mem_Iic.mpr j.isLt) j.val.le_succ))

private theorem tendsto_meas_ge_lintegral_of_le_two_mul_add {t : ℝ≥0}
    {f₁ f₂ g : ℕ → ℝ≥0 → Ω → ℝ}
    (hf₁ : ∀ k ω, Measurable fun s ↦ ‖f₁ k s ω‖ₑ ^ 2)
    (hle : ∀ k s ω, ‖g k s ω‖ₑ ^ 2 ≤ 2 * ‖f₁ k s ω‖ₑ ^ 2 + 2 * ‖f₂ k s ω‖ₑ ^ 2)
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖f₁ k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖f₂ k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  have hε4 : (0 : ℝ≥0∞) < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (h₁ _ hε4).add (h₂ _ hε4)) (fun _ ↦ bot_le) fun k ↦
    (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  have htri : ε ≤ 2 * (∫⁻ s, ‖f₁ k s ω‖ₑ ^ 2 ∂timeMeasure t) +
      2 * ∫⁻ s, ‖f₂ k s ω‖ₑ ^ 2 ∂timeMeasure t :=
    hω.trans ((lintegral_mono (hle k · ω)).trans (by
      rw [lintegral_add_left ((hf₁ k ω).const_mul 2),
        lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
        lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]))
  by_contra hnot
  obtain ⟨h1, h2⟩ := not_or.mp hnot
  simp only [mem_ofPred_eq, not_le] at h1 h2
  have hlt := ENNReal.add_lt_add
    (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top h1)
    (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top h2)
  have h4 : (2 : ℝ≥0∞) * (ε / 4) + 2 * (ε / 4) = ε := by
    calc (2 : ℝ≥0∞) * (ε / 4) + 2 * (ε / 4) = 4 * (ε / 4) := by ring
      _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  exact (h4 ▸ hlt).not_ge htri

/-- Addition preserves `IsItoIntegral`. -/
theorem IsItoIntegral.add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω + K t ω) (fun t ω ↦ I t ω + J t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hJ.ae_continuous] with _ hcI hcJ; exact hcI.add hcJ
  exists_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hG₁⟩ := hI.exists_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hJ.exists_approx t
    choose M σ b hσ hb hhold hgain using fun k ↦
      exists_sum_simpleStrategy (hτ₁ k) (ha₁ k) (hτ₂ k) (ha₂ k)
    refine ⟨M, σ, b, hσ, hb, fun ε hε ↦
      tendsto_meas_ge_lintegral_of_le_two_mul_add (fun k ω ↦ ?_) (fun k s ω ↦ ?_) hE₁ hE₂ hε,
      (hG₁.add hG₂).congr_left fun k ↦ .of_forall fun ω ↦ (hgain k W t ω).symm⟩
    · exact ((((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub
        hI.isStronglyPredictable).mono ℱ.predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)).eNorm.pow_const 2
    · rw [hhold k s ω]
      have hpt : Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω +
            Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - (H s ω + K s ω) =
          (Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω) -
            (-(Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - K s ω)) := by ring
      rw [hpt]
      simpa only [sub_zero, eNorm_neg, mul_add] using
        TauCeti.eNorm_sub_sq_le_two_mul
          (Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω)
          (-(Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - K s ω)) 0

/-- Subtraction preserves `IsItoIntegral`. -/
theorem IsItoIntegral.sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω - K t ω) (fun t ω ↦ I t ω - J t ω) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

end Spec

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H K I J : ℝ≥0 → Ω → ℝ}

private theorem tendsto_meas_ge_lintegral_eNorm_sq_of_eLpNorm [SFinite P]
    {g : ℕ → ℝ≥0 × Ω → ℝ} (hg : ∀ k, StronglyMeasurable (g k)) (t : ℝ≥0)
    (hlim : Tendsto (fun k ↦ eLpNorm (g k) 2 ((timeMeasure t).prod P)) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  have hm (k : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ ‖g k p‖ₑ ^ 2) := (hg k).eNorm.pow_const 2
  have hint (k : ℕ) : ∫⁻ ω, ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t ∂P =
      eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2 := by
    rw [← lintegral_prod_symm _ (hm k).aemeasurable,
      TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (by decide) (hg k).aestronglyMeasurable]
    simp only [Nat.cast_ofNat]
  have hsq : Tendsto (fun k ↦ eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0)] using
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hlim
  by_cases htop : ε = ∞
  · subst htop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsq.eventually (gt_mem_nhds zero_lt_one)] with k hk
    have hae := ae_lt_top (hm k).lintegral_prod_left'
      ((hint k).trans_lt (hk.trans ENNReal.one_lt_top)).ne
    simpa only [not_lt, top_le_iff] using (ae_iff.mp hae).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hsq (Or.inr (ENNReal.inv_ne_top.mpr hε.ne')))
      (fun _ ↦ bot_le) fun k ↦ ?_
    calc P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}
      _ = ε⁻¹ * (ε * P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hε.ne' htop, one_mul]
      _ ≤ ε⁻¹ * eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2 := mul_le_mul_right
          ((mul_meas_ge_le_lintegral (hm k).lintegral_prod_left' ε).trans_eq (hint k)) _

/-- Any almost surely continuous modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)`
satisfies the elementary-approximation specification `IsItoIntegral`. -/
theorem isItoIntegral_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    IsItoIntegral ℱ P W H I where
  isStronglyPredictable := hH.isStronglyPredictable
  ae_continuous := hI_cont
  exists_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
    refine ⟨n, τ, a, fun k ↦ (hτ k).monotoneOn, ha, fun _ hε ↦
      tendsto_meas_ge_lintegral_eNorm_sq_of_eLpNorm
        (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod) t (herr t) hε,
      tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_⟩
    exact hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
      (fun _ ↦ hH) (fun _ ↦ hI t) (fun k ↦ (hτ k).monotoneOn) ha ha₂ (herr t)

private theorem isItoIntegral_of_localized_stages
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : IsStronglyPredictable ℱ H)
    {X : ℝ≥0 → Ω → ℝ} (hX_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} (hloc : IsLocalizingSequence ℱ τ P)
    {Hstage : ℕ → ℝ≥0 → Ω → ℝ} (hHstage : ∀ k, BrownianIntegrable ℱ P (Hstage k))
    {U : ℕ → ℝ≥0 → Ω → ℝ}
    (hUae : ∀ k t, U k t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t))
    (hstop : ∀ k, stoppedProcess X (τ k) ≡ᵐ[P] U k)
    (hstage_eq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ k, (t : WithTop ℝ≥0) < τ k ω →
      EqOn (fun s ↦ Hstage k s ω) (fun s ↦ H s ω) (Iic t)) :
    IsItoIntegral ℱ P W H X where
  isStronglyPredictable := hH
  ae_continuous := hX_cont
  exists_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    choose n grid a C _ hgrid ha hb herr using fun k : ℕ ↦
      ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t (hHstage k).isStronglyPredictable
        ((hHstage k).memLp_timeMeasure t) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (k + 1)))
    have herr_lim : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2) 2
          ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
        (fun _ ↦ bot_le) fun k ↦ (herr k).le
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
    refine ⟨n, grid, a, fun k ↦ (hgrid k).monotoneOn, ha, fun _ hε ↦
      hloc.tendsto_measure_of_ae_imp_of_lt t
        (tendsto_meas_ge_lintegral_eNorm_sq_of_eLpNorm
          (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
            (hHstage k).isStronglyPredictable).mono ℱ.predictable_le_prod) t herr_lim hε)
        fun k ↦ (hstage_eq t).mono fun ω hgood hlt hω ↦ ?_,
      tendstoInMeasure_iff_norm.mpr fun ε hε ↦ ?_⟩
    · have heq_int : (∫⁻ s, ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - Hstage k s ω‖ₑ ^ 2
          ∂timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t := by
        rw [timeMeasure_def]
        exact setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
          have hs_eq : Hstage k s ω = H s ω := hgood k hlt hs.2; rw [hs_eq]
      simpa only [mem_ofPred_eq, Pi.sub_apply, Function.uncurry_apply_pair, heq_int] using hω
    · have hG_stage : TendstoInMeasure P
          (fun k ω ↦ Finance.simpleGains (grid k) (n k) (a k) W t ω - U k t ω) atTop 0 := by
        refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
        simpa only [Pi.sub_def, sub_zero] using
          hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
            hHstage (fun k ↦ hUae k t) (fun k ↦ (hgrid k).monotoneOn) ha ha₂ herr_lim
      have hG_ε := (tendstoInMeasure_iff_norm.mp hG_stage) ε hε
      simp only [Pi.zero_apply, sub_zero] at hG_ε
      exact hloc.tendsto_measure_of_ae_imp_of_lt t hG_ε fun k ↦
        ((hstop k).ae_eq_eval t).mono fun ω heq_u hlt hω ↦ by
          simpa only [mem_ofPred_eq, ← heq_u, stoppedProcess_eq_of_le (u := X) hlt.le] using hω

private theorem exists_patched_energyLocalizer_process
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    letI := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
    ∃ (X : ℝ≥0 → Ω → ℝ) (U : ℕ → ℝ≥0 → Ω → ℝ),
      IsStronglyProgressive ℱ X ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) ∧
      Locally (fun Z ↦ Martingale Z ℱ P) ℱ X P ∧
      IsItoIntegral ℱ P W H X ∧
      (∀ m, IsStronglyPredictable ℱ (U m)) ∧
      (∀ m, ∀ᵐ ω ∂P, Continuous (fun t ↦ U m t ω)) ∧
      (∀ m t, U m t =ᵐ[P] hW.l2Integral t
        ((hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
          (P := P) ((m : ℝ≥0) + 1)).toPredictableLp t)) ∧
      ∀ m : ℕ, stoppedProcess X (TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)) ≡ᵐ[P] U m := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let τ (m : ℕ) := TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)
  have hloc := hH.isLocalizingSequence_energyLocalizer
  let hHstage (m : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((m : ℝ≥0) + 1)
  choose U hUp hUm hUcont hUae using fun m ↦ hW.exists_continuous_l2Integral hcont (hHstage m)
  have hcompat (n m : ℕ) (hnm : n ≤ m) : stoppedProcess (U m) (τ n) ≡ᵐ[P] U n := by
    refine TauCeti.indist_of_ae_continuous
      ((hUcont m).mono fun _ hc ↦ hc.stoppedProcess) (hUcont n) fun t ↦ ?_
    have hstop_ae := hW.stoppedProcess_ae_eq_l2Integral (hHstage m) (hUp m).stronglyAdapted
      ((hUcont m).mono fun _ hc _ ↦ hc.continuousWithinAt) (hUae m) (hloc.isStoppingTime n) t
    have hlp_eq : ((hHstage m).ite_le (hloc.isStoppingTime n)).toPredictableLp t =
        (hHstage n).toPredictableLp t := by
      refine BrownianIntegrable.toPredictableLp_congr _ _ (.of_forall fun ⟨s, ω⟩ ↦ ?_)
      have hτ_le : τ n ω ≤ τ m ω := TauCeti.nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
      dsimp only [Function.uncurry_apply_pair, τ] at *
      by_cases hs : (s : WithTop ℝ≥0) ≤ TauCeti.nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω
      · rw [ite_eq_left hs, ite_eq_left (hs.trans hτ_le), ite_eq_left hs]
      · rw [ite_eq_right hs, ite_eq_right hs]
    exact hstop_ae.trans (hlp_eq ▸ (hUae n t).symm)
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ :=
    TauCeti.exists_isStronglyProgressive_patch_stoppedProcess hloc.tendsto_top
      (fun m ↦ (hUp m).isStronglyProgressive) hUcont hcompat
  have hX_loc : Locally (fun Z ↦ Martingale Z ℱ P) ℱ X P := by
    refine hX_prog.locally_martingale_of_ae_stopped_eq hloc hUm fun n t ↦ ?_
    have hX_ind : (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < τ n ω}.indicator (X s)) = X := by
      ext s ω
      have hpos : (⊥ : WithTop ℝ≥0) < τ n ω :=
        TauCeti.nnvolume.energyLocalizer_pos H (C := (n : ℝ≥0) + 1) (by positivity) ω
      exact indicator_of_mem hpos _
    rw [hX_ind]
    exact (hX_stop n).symm.ae_eq_eval t
  have hX_ito : IsItoIntegral ℱ P W H X :=
    hW.isItoIntegral_of_localized_stages hH.isStronglyPredictable hX_cont hloc
      hHstage hUae hX_stop fun t ↦ hH.ae_accumulatedEnergy_lt_top.mono fun ω hfin k hlt s hs ↦ by
        have hle : (s : WithTop ℝ≥0) ≤ τ k ω :=
          (WithTop.coe_le_coe.mpr (mem_Iic.mp hs)).trans hlt.le
        dsimp only [τ] at hle
        simpa only [ite_eq_left hle] using TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
  exact ⟨X, U, hX_prog, hX_cont, hX_loc, hX_ito, hUp, hUcont, hUae, hX_stop⟩

/-- **Existence of the continuous-time Brownian Itô integral.** For a filtration-relative Brownian
motion `W` with almost surely continuous paths and a `LocallyBrownianIntegrable` integrand `H`,
there exists a strongly predictable native local martingale `I` on the original raw filtration
satisfying `IsItoIntegral ℱ P W H I`. -/
theorem exists_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P ∧
      IsItoIntegral ℱ P W H I := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨X, _, _, hX_cont, hX_loc, hX_ito, _⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  obtain ⟨I, hI_pred, hIX, hI_loc⟩ :=
    hX_loc.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hX_cont.mono fun _ hc _ ↦ hc.continuousWithinAt)
  exact ⟨I, hI_pred, hI_loc, hX_ito.congr hIX.symm⟩

/-- **Local-martingale property of the Brownian Itô integral.** Any strongly progressive process
satisfying `IsItoIntegral` for a `LocallyBrownianIntegrable` integrand is a native local
martingale on the original raw filtration. -/
theorem itoIntegral_localMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI_prog : IsStronglyProgressive ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  obtain ⟨J, _, hJ_loc, hJ_ito⟩ := hW.exists_isItoIntegral hcont hH
  exact hI_prog.locally_martingale_of_indist hJ_loc (isItoIntegral_unique hW hJ_ito hI)

/-- **Optional stopping of the Brownian Itô integral.** Stopping an Itô integral of a
`LocallyBrownianIntegrable` integrand `H` at any raw stopping time `σ` yields an Itô integral of
`H` cut off to `⟦0, σ⟧`. -/
theorem itoIntegral_stoppedProcess
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess I σ) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨X, U, _, hX_cont, _, hX_ito, hUp, hUcont, hUae, hX_stop⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  let τ (k : ℕ) := TauCeti.nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  let hHstage (k : ℕ) :=
    (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P)
      ((k : ℝ≥0) + 1)).ite_le hσ
  have hUσ_ae (k : ℕ) (t : ℝ≥0) :
      stoppedProcess (U k) σ t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t) :=
    hW.stoppedProcess_ae_eq_l2Integral _ (hUp k).stronglyAdapted
      ((hUcont k).mono fun _ hc _ ↦ hc.continuousWithinAt) (hUae k) hσ t
  have hXσ_stop (k : ℕ) :
      stoppedProcess (stoppedProcess X σ) (τ k) ≡ᵐ[P] stoppedProcess (U k) σ := by
    rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
    exact (hX_stop k).stoppedProcess σ
  have hXσ_ito : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess X σ) := by
    refine hW.isItoIntegral_of_localized_stages (hH.isStronglyPredictable.ite_le hσ)
      (hX_cont.mono fun _ hc ↦ hc.stoppedProcess)
      hH.isLocalizingSequence_energyLocalizer
      hHstage hUσ_ae hXσ_stop fun t ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top] with ω hfin k hlt s hs
    have hle : (s : WithTop ℝ≥0) ≤ τ k ω := (WithTop.coe_le_coe.mpr (mem_Iic.mp hs)).trans hlt.le
    have hcut : TauCeti.nnvolume.finiteEnergyCutoff H s ω = H s ω :=
      TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
    dsimp only [τ] at hle ⊢
    rw [ite_eq_left hle, hcut]
  exact hXσ_ito.congr ((isItoIntegral_unique hW hX_ito hI).stoppedProcess σ)

/-- **Local congruence of the Brownian Itô integral.** If two `LocallyBrownianIntegrable`
integrands agree product-almost-everywhere on `⟦0, σ⟧` over every finite horizon for a raw stopping
time `σ`, their Itô integrals agree up to indistinguishability when stopped at `σ`. -/
theorem itoIntegral_local_congr
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) (hK : LocallyBrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ)
    (hHK : ∀ t : ℝ≥0,
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0) =ᵐ[
        (timeMeasure t).prod P]
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then K s ω else 0)) :
    stoppedProcess I σ ≡ᵐ[P] stoppedProcess J σ := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hIσ := (hW.itoIntegral_stoppedProcess hcont hH hI hσ).congr_integrand
    (hK.isStronglyPredictable.ite_le hσ) hHK
  exact isItoIntegral_unique hW hIσ (hW.itoIntegral_stoppedProcess hcont hK hJ hσ)

/-- When `H` has finite expected square energy on every finite horizon (`BrownianIntegrable`), any
process `I` satisfying `IsItoIntegral ℱ P W H I` agrees almost everywhere at each time `t` with
`hW.l2Integral t (hH.toPredictableLp t)`. -/
theorem itoIntegral_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  obtain ⟨J, _, _, hJ_cont, hJ_ae⟩ := hW.exists_continuous_l2Integral hcont hH
  exact ((isItoIntegral_unique hW hI
    (hW.isItoIntegral_of_ae_eq_l2Integral hH hJ_cont hJ_ae)).ae_eq_eval t).trans (hJ_ae t)

/-- **Cross-isometry of the Brownian Itô integral** on `BrownianIntegrable` integrands. -/
theorem itoIntegral_mul_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P :=
  hW.integral_mul_of_ae_eq_l2Integral hH hK
    (hW.itoIntegral_ae_eq_l2Integral hcont hH hI)
    (hW.itoIntegral_ae_eq_l2Integral hcont hK hJ) T

/-- **Itô isometry** for any process satisfying `IsItoIntegral` of a `BrownianIntegrable`
integrand. -/
theorem itoIntegral_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P := by
  simpa only [sq] using hW.itoIntegral_mul_isometry hcont hH hH hI hI T

/-- Any strongly adapted Itô integral of a `BrownianIntegrable` integrand is a true martingale on
the original raw filtration, with square-compensation martingale `I_t² - ∫_{(0, t]} H_s² ds`. -/
theorem itoIntegral_martingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H)
    (hI_adapt : StronglyAdapted ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Martingale I ℱ P ∧
      Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P :=
  ⟨hW.martingale_of_ae_eq_l2Integral hH hI_adapt (hW.itoIntegral_ae_eq_l2Integral hcont hH hI),
    hW.martingale_sq_sub_integral_of_ae_eq_l2Integral hH hI_adapt
      (hW.itoIntegral_ae_eq_l2Integral hcont hH hI)⟩

end IsFilteredPreBrownianReal

end TauCeti.Probability
