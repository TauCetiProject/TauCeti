/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.Topology.Instances.NNReal.Lemmas
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Predictable.Basic

/-!
# Itô integrals against Brownian motion: definition, algebra, and uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings, with heights known at the left endpoints of
their intervals, approximate `H` on `(0,t]` in square energy in probability, while their
elementary integrals at `t` converge in probability to `I t`. Square energy is a lower Lebesgue
integral, so an infinite energy is never read as the default value zero of a divergent Bochner
integral. The heights need not be bounded; bounded approximants are a special case.

Every Itô integral automatically starts at zero almost surely and forces its integrand to be
locally Brownian integrable, with no assumption on `W` or finiteness of `P`. The predicate is
closed under indistinguishability of the integral (`TauCeti.Probability.IsItoIntegral.congr`),
product-almost-everywhere replacement of the predictable integrand, fixed-time almost-everywhere
replacement of the integrator, filtration enlargement, addition, scaling, and negation, and holds
for elementary holdings and constants.

Against a pre-Brownian motion relative to the filtration, any limit in probability of the
elementary integrals of simple holdings approximating the integrand on `(0,t]` in square energy
in probability agrees almost surely with the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`). Such a sequence and the one
witnessing the Itô integral are compared on one common grid. Their difference has square energy
converging to zero in probability, so its elementary integral at `t` converges to zero in
probability by the energy estimate
`TauCeti.Probability.IsFilteredPreBrownianReal.tendstoInMeasure_simpleGains_of_energy`. Hence
the predicate determines the integral up to indistinguishability
(`TauCeti.Probability.isItoIntegral_unique`): two integrals agree almost surely at each time,
and continuity of their paths makes them indistinguishable. Neither path continuity of `W` nor
usual conditions on the filtration are needed. Conversely, the predicate is invariant under
indistinguishability (`TauCeti.Probability.IsItoIntegral.congr`), so it determines its
integrals exactly up to indistinguishability (`TauCeti.Probability.isItoIntegral_iff_indist`).

The elementary integral of a simple holding is its Itô integral against every process with
almost surely continuous paths (`TauCeti.Probability.isItoIntegral_simpleGains`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W W' H K I J : ℝ≥0 → Ω → ℝ}

/-- `I` is an **Itô integral** of the integrand `H` against `W`. The integrand is predictable,
almost every path of `I` is continuous, and at every time `t` there are simple holdings with
heights known at the left endpoints of their intervals such that
`∫_(0,t] |Kₖ - H|² ds → 0` in probability while their elementary integrals at `t` converge to
`I t` in probability. The square energy is a lower Lebesgue integral, so it is infinite rather
than zero when the square error is not integrable. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W H I : ℝ≥0 → Ω → ℝ) :
    Prop where
  /-- The integrand is predictable, so its square errors are measurable in time. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every path of the integral is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous fun t ↦ I t ω
  /-- At each time `t`, simple holdings approximate the integrand on `(0,t]` in square energy
  in probability, and their elementary integrals at `t` converge to `I t` in probability. -/
  exists_approx (t : ℝ≥0) : ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
    (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
    (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-! ### Private helpers for `timeMeasure` square energy and common simple-holding grids -/

/-- Two sequences of predictable processes approximating the same predictable process in
square energy in probability on `(0,t]` approximate each other there. -/
private theorem tendsto_measure_le_lintegral_sub (hH : IsStronglyPredictable ℱ H)
    {K L : ℕ → ℝ≥0 → Ω → ℝ} (hK : ∀ k, IsStronglyPredictable ℱ (K k)) (t : ℝ≥0)
    (hKH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖K k s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L k s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖K k s ω - L k s ω‖ₑ ^ 2 ∂timeMeasure t})
      atTop (𝓝 0) := by
  set η := ε / 4
  have hη : 0 < η := ENNReal.div_pos hε.ne' (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using (hKH η hη).add (hLH η hη)) (fun _ ↦ bot_le) fun k ↦ ?_
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  simp only [not_or, not_le] at hcon
  have hmeas : Measurable fun s ↦ ‖K k s ω - H s ω‖ₑ ^ 2 :=
    ((((hK k).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).comp
      (measurable_id.prodMk measurable_const)
  have hlt := ENNReal.add_lt_add hcon.left hcon.right
  refine (hω.trans (lintegral_enorm_sub_sq_le_two_mul hmeas.aemeasurable)).not_gt ?_
  calc
    _ < 2 * (η + η) := by
      rw [two_mul, two_mul]
      exact ENNReal.add_lt_add hlt hlt
    _ = 4 * (ε / 4) := by ring
    _ ≤ ε := ENNReal.mul_div_le

private theorem measurable_simpleHolding (τ : ℕ → ℝ≥0) (n : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) :
    Measurable (fun s ↦ Finance.simpleHolding τ n a s ω) := by
  simp only [Finance.simpleHolding_def]
  exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc

private theorem lintegral_eNorm_sq_le_of_add {f g : ℝ≥0 → ℝ} (t : ℝ≥0) (hf : Measurable f) :
    (∫⁻ s, ‖f s + g s‖ₑ ^ 2 ∂timeMeasure t) ≤
      2 * (∫⁻ s, ‖f s‖ₑ ^ 2 ∂timeMeasure t) + 2 * (∫⁻ s, ‖g s‖ₑ ^ 2 ∂timeMeasure t) := by
  simpa only [Pi.zero_apply, Pi.neg_apply, sub_neg_eq_add, sub_zero, eNorm_neg, mul_add] using
    lintegral_enorm_sub_sq_le_two_mul (μ := timeMeasure t) (f := f) (g := -g) (h := 0)
      (by simpa only [Pi.zero_apply, sub_zero] using (hf.eNorm.pow_const 2).aemeasurable)

private theorem tendsto_measure_lintegral_add_sq {f g h : ℕ → ℝ≥0 → Ω → ℝ} (t : ℝ≥0)
    (hf : ∀ k ω, Measurable (fun s ↦ f k s ω))
    (hpt : ∀ k ω s, h k s ω = f k s ω + g k s ω)
    (hf0 : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hg0 : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖h k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  wlog htop : ε ≠ ∞ generalizing ε
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (this zero_lt_one ENNReal.one_ne_top) (fun _ ↦ zero_le) fun k ↦
      measure_mono fun _ hω ↦ (le_top : (1 : ℝ≥0∞) ≤ ∞).trans (by rwa [not_not.mp htop] at hω)
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  have hsum : 2 * (ε / 4) + 2 * (ε / 4) = ε := by
    rw [← two_mul, ← mul_assoc]; norm_num
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hsub (k : ℕ) :
      {ω | ε ≤ ∫⁻ s, ‖h k s ω‖ₑ ^ 2 ∂timeMeasure t} ⊆
        {ω | ε / 4 ≤ ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t} ∪
          {ω | ε / 4 ≤ ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t} := by
    intro ω hω; by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
    have hlt : 2 * (∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t) +
        2 * (∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t) < ε :=
      (ENNReal.add_lt_add (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnot.left)
        (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnot.right)).trans_eq hsum
    exact hlt.not_ge (hω.trans <| by
      simp_rw [hpt k ω]; exact lintegral_eNorm_sq_le_of_add t (hf k ω))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (hf0 _ hε4).add (hg0 _ hε4)) (fun _ ↦ zero_le) fun k ↦
    (measure_mono (hsub k)).trans (measure_union_le _ _)

private theorem exists_simpleHolding_add_common
    {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Iic n₂))
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j)) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ s ω, Finance.simpleHolding τ n b s ω =
        Finance.simpleHolding τ₁ n₁ a₁ s ω + Finance.simpleHolding τ₂ n₂ a₂ s ω) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) s ω, Finance.simpleGains τ n b X s ω =
        Finance.simpleGains τ₁ n₁ a₁ X s ω + Finance.simpleGains τ₂ n₂ a₂ X s ω := by
  obtain ⟨n, τ, b, -, hτ, hb, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ hτ₁ hτ₂ ha₁
      (b := (-1 : ℝ) • a₂) (fun j hj ↦ (ha₂ j hj).const_mul (-1))
  refine ⟨n, τ, b, hτ.monotoneOn, hb, fun s ω ↦ ?_, fun X s ω ↦ ?_⟩
  · simpa only [sub_eq_add_neg, Finance.simpleHolding_smul, neg_one_mul, neg_neg] using
      hhold s ω
  · simpa only [sub_eq_add_neg, Finance.simpleGains_smul, neg_one_mul, neg_neg] using
      hgain X s ω

/-! ### Uniqueness, basic properties, and closure of `IsItoIntegral` -/

/-- **Identification of the Itô integral at a time.** Against a pre-Brownian motion relative
to the filtration, if simple holdings with heights known at the left endpoints of their
intervals approximate the integrand on `(0,t]` in square energy in probability, then every
limit in probability of their elementary integrals at `t` agrees almost surely with the Itô
integral at `t`. -/
theorem IsItoIntegral.ae_eq_of_tendstoInMeasure (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {m : ℕ → ℕ} {σ : ℕ → ℕ → ℝ≥0}
    {b : ℕ → ℕ → Ω → ℝ} {X : Ω → ℝ} (hσ : ∀ k, MonotoneOn (σ k) (Iic (m k)))
    (hb : ∀ k j, j < m k → StronglyMeasurable[ℱ (σ k j)] (b k j))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0))
    (hLX : TendstoInMeasure P (fun k ↦ Finance.simpleGains (σ k) (m k) (b k) W t) atTop X) :
    I t =ᵐ[P] X := by
  obtain ⟨n, τ, a, hτ, ha, hKH, hKI⟩ := hI.exists_approx t
  choose N ρ c _ hρ hc hhold hgain using fun k ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ k) (hσ k) (ha k) (hb k)
  -- On a common grid, the difference of the approximations has vanishing elementary integral.
  have hdiff : TendstoInMeasure P (fun k ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω -
      Finance.simpleGains (σ k) (m k) (b k) W t ω) atTop (fun _ ↦ 0) := by
    have henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (ρ k) (N k) (c k) s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0) := by
      simp_rw [hhold]
      exact tendsto_measure_le_lintegral_sub hI.isStronglyPredictable
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k)) t hKH hLH
    exact (hW.tendstoInMeasure_simpleGains_of_energy (fun k ↦ (hρ k).monotoneOn) hc t
      henergy).congr_left fun k ↦ ae_of_all _ fun ω ↦ hgain k W t ω
  -- Compare almost surely convergent subsequences of the three sequences.
  obtain ⟨ns, hns, hK⟩ := hKI.exists_seq_tendsto_ae
  obtain ⟨ns', hns', hL⟩ := (hLX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ns'', hns'', hD⟩ :=
    ((hdiff.comp hns.tendsto_atTop).comp hns'.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hK, hL, hD] with ω hKω hLω hDω
  have hsub := (hKω.comp (hns'.tendsto_atTop.comp hns''.tendsto_atTop)).sub
    (hLω.comp hns''.tendsto_atTop)
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hDω)

/-- **Uniqueness of the Itô integral.** Against a pre-Brownian motion relative to the
filtration, two Itô integrals of the same integrand are indistinguishable. Neither path
continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) : I ≡ᵐ[P] J := by
  refine indist_of_forall_ae_eq hI.ae_continuous hJ.ae_continuous fun t ↦ ?_
  obtain ⟨m, σ, b, hσ, hb, hLH, hLJ⟩ := hJ.exists_approx t
  exact hI.ae_eq_of_tendstoInMeasure hW hσ hb hLH hLJ

/-- An Itô integral may be replaced by any indistinguishable process. -/
theorem IsItoIntegral.congr (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hω hIJω
    exact hω.congr hIJω
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, ha, hE, hG.congr_right (hIJ.ae_eq_eval t)⟩

/-- Against a pre-Brownian motion relative to the filtration, the Itô integrals of an integrand
are exactly the processes indistinguishable from one of them. -/
theorem isItoIntegral_iff_indist (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W H J ↔ I ≡ᵐ[P] J :=
  ⟨isItoIntegral_unique hW hI, hI.congr⟩

/-- The elementary integral of a simple holding with heights known at the left endpoints of its
intervals is its Itô integral against every process with almost surely continuous paths. -/
theorem isItoIntegral_simpleGains {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := by
    filter_upwards [hW] with ω hω
    exact Finance.continuous_simpleGains hω
  exists_approx _ := ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha,
    fun ε hε ↦ by simp [hε.ne'], fun ε hε ↦ by simp [hε.ne']⟩

namespace IsItoIntegral

/-- Every Itô integral starts at zero almost surely, with no assumptions on the integrator
or sample measure. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, -, -, -, hlim⟩ := hI.exists_approx 0
  have hzero (k : ℕ) : Finance.simpleGains (τ k) (n k) (a k) W 0 = 0 := by
    ext ω; simp [Finance.simpleGains_def]
  exact tendstoInMeasure_ae_unique (by simpa only [hzero] using hlim)
    fun _ hε ↦ by simp [hε.not_ge]

/-- Any integrand admitting an Itô integral has finite pathwise square energy on every finite
horizon outside one common null set. Neither a Brownian law nor finiteness of `P` is needed. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun m ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, -, henergy, -⟩ := hI.exists_approx m
  have hHmeas := hI.isStronglyPredictable.mono ℱ.predictable_le_prod
  have hfinite : ∀ᵐ ω ∂P, ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure m < ∞ := by
    rw [ae_iff]
    have hsub (k : ℕ) : {ω | ¬ ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure m < ∞} ⊆
        {ω | (1 : ℝ≥0∞) ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure m} := by
      intro ω hω
      simp only [mem_ofPred_eq, not_lt, top_le_iff] at hω ⊢
      have hKfin : ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2
          ∂timeMeasure m < ∞ := by
        rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (hτ k)]
        exact ENNReal.sum_lt_top.2 fun _ _ ↦
          ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_ne_top.lt_top) ENNReal.ofReal_lt_top
      have hle := lintegral_eNorm_sq_le_of_add
        (g := fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) m
        ((hHmeas.comp_measurable (measurable_prodMk_right (y := ω))).measurable.sub
          (measurable_simpleHolding (τ k) (n k) (a k) ω))
      simp only [Pi.sub_apply, sub_add_cancel] at hle
      by_contra hlt
      have hfin : ∫⁻ s, ‖H s ω - Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2
          ∂timeMeasure m < ∞ := by
        simpa only [eNorm_sub_rev] using (not_le.mp hlt).trans ENNReal.one_lt_top
      exact (hle.trans_lt (ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top (by norm_num) hfin, ENNReal.mul_lt_top (by norm_num) hKfin⟩)).ne hω
    exact le_antisymm (ge_of_tendsto' (henergy 1 zero_lt_one) (fun k ↦ measure_mono (hsub k)))
      zero_le
  filter_upwards [hfinite] with ω hω
  have hmem := (hHmeas.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    |>.memLp_two_iff_lintegral_enorm_sq_lt_top.2 hω
  rwa [timeMeasure_def, ← NNReal.comap_volume_restrict_Ioc, NNReal.coe_natCast] at hmem

/-- Replacing the integrator by a process equal almost surely at each deterministic time
preserves `IsItoIntegral`. -/
theorem congr_noise (hI : IsItoIntegral ℱ P W H I) (hWW' : ∀ t, W t =ᵐ[P] W' t) :
    IsItoIntegral ℱ P W' H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hlim⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, ha, henergy, hlim.congr_left fun k ↦
      (ae_all_iff.2 fun j ↦ ae_all_iff.2 fun _ ↦ hWW' _).mono fun ω hω ↦
        Finance.simpleGains_congr_price ω hω⟩

/-- Product-almost-everywhere replacement of the integrand by a predictable process preserves
`IsItoIntegral`. -/
theorem congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hlim⟩ := hI.exists_approx t
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω) :=
      Measure.ae_ae_of_ae_prod
        ((Measure.measurePreserving_swap (μ := P) (ν := timeMeasure t)).quasiMeasurePreserving
          |>.ae_eq_comp (hHK t))
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ ?_, hlim⟩
    have hcongr (k : ℕ) :
        P {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2
          ∂timeMeasure t} =
        P {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t} :=
      measure_congr <| hsec.mono fun ω hω ↦ by
        have hint : (∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2
            ∂timeMeasure t) =
            ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t :=
          lintegral_congr_ae (hω.mono fun s hs ↦ by simp [hs])
        simp [hint]
    simpa only [hcongr] using henergy ε hε

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem mono_filtration {𝒢 : Filtration ℝ≥0 mΩ} (hI : IsItoIntegral ℱ P W H I) (h : ℱ ≤ 𝒢) :
    IsItoIntegral 𝒢 P W H I where
  isStronglyPredictable := hI.isStronglyPredictable.mono (Filtration.predictable_mono h)
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hlim⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, fun k j hj ↦ (ha k j hj).mono (h _), henergy, hlim⟩

/-- The zero process is an Itô integral of the zero integrand against any integrator. -/
theorem zero (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) :
    IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_zero
  ae_continuous := Eventually.of_forall fun _ ↦ continuous_const
  exists_approx _ := ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, fun _ ↦ monotoneOn_const,
    fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim,
    fun _ hε ↦ by simp [Finance.simpleHolding_def, hε.not_ge],
    fun _ hε ↦ by simp [Finance.simpleGains_def, hε.not_ge]⟩

/-- For an almost surely continuous integrator starting at zero almost surely, `c • W` is an
Itô integral of the constant integrand `c`. -/
theorem const (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hW0 : W 0 =ᵐ[P] 0) (c : ℝ) :
    IsItoIntegral ℱ P W (fun _ _ ↦ c) (fun t ω ↦ c * W t ω) where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := hcont.mono fun _ hω ↦ continuous_const.mul hω
  exists_approx t := by
    let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then 0 else t
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ _ _ ↦ c,
      fun _ i _ j _ hij ↦ by
        by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [τ, hi, hj]; omega,
      fun _ _ _ ↦ stronglyMeasurable_const, fun _ hε ↦ ?_, ?_⟩
    · have hzero (ω : Ω) :
          ∫⁻ s, ‖Finance.simpleHolding τ 1 (fun _ _ ↦ c) s ω - c‖ₑ ^ 2 ∂timeMeasure t = 0 :=
        (lintegral_eq_zero_iff' (((measurable_simpleHolding τ 1 (fun _ _ ↦ c) ω).sub
          measurable_const).eNorm.pow_const 2).aemeasurable).2 <|
          (ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by simp [Finance.simpleHolding_def, τ, hs]
      simp [hzero, hε.not_ge]
    · have hgain : Finance.simpleGains τ 1 (fun _ _ ↦ c) W t =ᵐ[P] fun ω ↦ c * W t ω :=
        hW0.mono fun ω hω ↦ by simp [Finance.simpleGains_def, τ, hω]
      exact TendstoInMeasure.congr_left (fun _ ↦ hgain.symm) fun _ hε ↦ by simp [hε.not_ge]

/-- Itô integrals are additive in the integrand and the integral process. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω + K t ω) (fun t ω ↦ I t ω + J t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := hI.ae_continuous.mp (hJ.ae_continuous.mono fun _ hJω hIω ↦ hIω.add hJω)
  exists_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hL₁⟩ := hI.exists_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hL₂⟩ := hJ.exists_approx t
    choose n τ b hτ hb hhold hgain using fun k ↦
      exists_simpleHolding_add_common (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    have hHmeas := hI.isStronglyPredictable.mono ℱ.predictable_le_prod
    refine ⟨n, τ, b, hτ, hb, fun _ hε ↦ ?_,
      by simpa only [funext fun k ↦ funext fun ω ↦ hgain k W t ω] using
        TendstoInMeasure.add hL₁ hL₂⟩
    refine tendsto_measure_lintegral_add_sq t (fun k ω ↦ ?_) (fun k ω s ↦ ?_) hE₁ hE₂ hε
    · exact (measurable_simpleHolding (τ₁ k) (n₁ k) (a₁ k) ω).sub
        (hHmeas.comp_measurable measurable_prodMk_right).measurable
    · rw [hhold k s ω]; ring

/-- Itô integrals scale linearly with real constants. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.const_mul c
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hL⟩ := hI.exists_approx t
    refine ⟨n, τ, fun k ↦ c • a k, hτ, fun k j hj ↦ (ha k j hj).const_mul c,
      fun ε hε ↦ ?_, ?_⟩
    · by_cases hc : c = 0
      · subst hc; simp_rw [Finance.simpleHolding_smul]; simp [hε.not_ge]
      · have hc2pos : 0 < ‖c‖ₑ ^ 2 := ENNReal.pow_pos (eNorm_pos.mpr hc) 2
        have hc2top : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
        convert hE (ε / ‖c‖ₑ ^ 2) (ENNReal.div_pos hε.ne' hc2top) using 2 with k
        congr 1; ext ω
        have hscale : ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (c • a k) s ω - c * H s ω‖ₑ ^ 2
            ∂timeMeasure t =
            ‖c‖ₑ ^ 2 * ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
              ∂timeMeasure t := by
          simp_rw [Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
          exact lintegral_const_mul' _ _ hc2top
        simp only [mem_ofPred_eq, hscale, ENNReal.div_le_iff_le_mul (.inl hc2pos.ne') (.inl hc2top),
          mul_comm]
    · have hpt : (fun k ↦ Finance.simpleGains (τ k) (n k) (c • a k) W t) =
          fun k ω ↦ c * Finance.simpleGains (τ k) (n k) (a k) W t ω :=
        funext fun k ↦ funext fun ω ↦ Finance.simpleGains_smul (τ k) (n k) c (a k) W t ω
      simpa only [hpt, smul_eq_mul] using TendstoInMeasure.const_smul hL c

/-- Negating the integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω - K t ω) (fun t ω ↦ I t ω - J t ω) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

end IsItoIntegral

/-! ### Fixed-time identification and integrand congruence against a filtered pre-Brownian motion -/

namespace IsFilteredPreBrownianReal

/-- **Product-a.e. integrand congruence.** Against a filtered pre-Brownian motion, Itô
integrals of predictable integrands that agree `dt × P`-almost everywhere on every finite
horizon are indistinguishable. Neither path continuity of `W` nor a separate local-energy
assumption is required. -/
theorem isItoIntegral_congr (hW : IsFilteredPreBrownianReal ℱ W P)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    I ≡ᵐ[P] J := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact isItoIntegral_unique hW (hI.congr_integrand hJ.isStronglyPredictable hHK) hJ

end IsFilteredPreBrownianReal

end TauCeti.Probability
