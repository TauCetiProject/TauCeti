/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.UsualFiltration
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.Indistinguishable

/-!
# Itô integrals against Brownian motion and their uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings, with heights known at the left endpoints of
their intervals, approximate `H` on `(0,t]` in square energy in probability, while their
elementary integrals at `t` converge in probability to `I t`. Square energy is a lower Lebesgue
integral, so an infinite energy is never read as the default value zero of a divergent Bochner
integral. The heights need not be bounded; bounded approximants are a special case.

Directly from the specification, every integrand admitting an Itô integral belongs to the
pathwise-energy domain (`TauCeti.Probability.IsItoIntegral.locallyBrownianIntegrable`), every
Itô integral vanishes almost surely at `0` (`TauCeti.Probability.IsItoIntegral.ae_eval_zero`), and
the relation is preserved under zero (`TauCeti.Probability.IsItoIntegral.zero`),
product-almost-everywhere integrand replacement
(`TauCeti.Probability.IsItoIntegral.congr_integrand`), scalar multiplication
(`TauCeti.Probability.IsItoIntegral.const_mul`), negation (`TauCeti.Probability.IsItoIntegral.neg`),
addition (`TauCeti.Probability.IsItoIntegral.add`), subtraction
(`TauCeti.Probability.IsItoIntegral.sub`), filtration enlargement
(`TauCeti.Probability.IsItoIntegral.mono`), and usual null/right-continuous augmentation
(`TauCeti.Probability.IsItoIntegral.nullAugment`,
`TauCeti.Probability.IsItoIntegral.rightCont_nullAugment`).

Against a pre-Brownian motion relative to the filtration, any limit in probability of the
elementary integrals of simple holdings approximating the integrand on `(0,t]` in square energy
in probability agrees almost surely with the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`). Such a sequence and the one
witnessing the Itô integral are compared on one common grid. Their difference has square energy
converging to zero in probability, so its elementary integral at `t` converges to zero in
probability by the energy estimate
`TauCeti.Probability.IsFilteredPreBrownianReal.tendstoInMeasure_simpleGains_of_energy`. Hence
the predicate determines the integral up to indistinguishability
(`TauCeti.Probability.isItoIntegral_unique`), identifies raw integrals with integrals constructed
on the usual augmentation (`TauCeti.Probability.isItoIntegral_indist_rightCont_nullAugment`), and
depends on the integrand only up to product-almost-everywhere equality on finite horizons
(`TauCeti.Probability.isItoIntegral_indist_of_ae_eq`): two integrals agree almost surely at each
time, and continuity of their paths makes them indistinguishable. Neither path continuity of `W`
nor usual conditions on the filtration are needed. Conversely, the predicate is invariant under
indistinguishability (`TauCeti.Probability.IsItoIntegral.congr`), so it determines its
integrals exactly up to indistinguishability (`TauCeti.Probability.isItoIntegral_iff_indist`).

The elementary integral of a simple holding is its Itô integral against every process with
almost surely continuous paths (`TauCeti.Probability.isItoIntegral_simpleGains`). Existence of
the integral for general locally square-integrable integrands is proved in
`TauCeti.Probability.BrownianMotion.Integral.Ito.Existence`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H K I J : ℝ≥0 → Ω → ℝ}

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

/-- Every integrand admitting an Itô integral belongs to the pathwise square-energy domain
`LocallyBrownianIntegrable`, directly from the elementary-approximation specification. -/
theorem IsItoIntegral.locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.mpr ⟨hI.isStronglyPredictable, fun n ↦ ?_⟩
  obtain ⟨m, τ, a, hτ, ha, hen, -⟩ := hI.exists_approx n
  let A (k : ℕ) : Set Ω := {ω | 1 ≤ ∫⁻ s,
    ‖Finance.simpleHolding (τ k) (m k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure n}
  have hinter : P (⋂ k, A k) = 0 := le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds (hen 1 zero_lt_one)
      fun k ↦ measure_mono (iInter_subset A k)) zero_le
  have hae : ∀ᵐ ω ∂P, ∃ k, ∫⁻ s,
      ‖Finance.simpleHolding (τ k) (m k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure n < 1 := by
    have hinter' : ∀ᵐ ω ∂P, ω ∉ ⋂ k, A k := compl_mem_ae_iff.mpr hinter
    filter_upwards [hinter'] with ω hω
    obtain ⟨k, hk⟩ := not_forall.mp (mt mem_iInter.mpr hω)
    exact ⟨k, not_le.mp hk⟩
  filter_upwards [hae] with ω ⟨k, hk⟩
  have hK_sm : AEStronglyMeasurable (fun s ↦ Finance.simpleHolding (τ k) (m k) (a k) s ω)
      ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) :=
    (((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
      ℱ.predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hK_fin : ∫⁻ s, ‖Finance.simpleHolding (τ k) (m k) (a k) s ω‖ₑ ^ 2
      ∂((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) < ∞ := by
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def,
      Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (hτ k)]
    exact ENNReal.sum_lt_top.mpr fun j _ ↦
      ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) ENNReal.ofReal_lt_top
  have hK_mem : MemLp (fun s ↦ Finance.simpleHolding (τ k) (m k) (a k) s ω) 2
      ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) :=
    hK_sm.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr hK_fin
  have hdiff_sm : AEStronglyMeasurable (fun s ↦
        Finance.simpleHolding (τ k) (m k) (a k) s ω - H s ω)
      ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) :=
    ((((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
      hI.isStronglyPredictable).mono ℱ.predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hdiff_fin : ∫⁻ s, ‖Finance.simpleHolding (τ k) (m k) (a k) s ω - H s ω‖ₑ ^ 2
      ∂((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) < ∞ := by
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
    exact hk.trans ENNReal.one_lt_top
  have hdiff_mem : MemLp (fun s ↦ Finance.simpleHolding (τ k) (m k) (a k) s ω - H s ω) 2
      ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) :=
    hdiff_sm.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr hdiff_fin
  convert hK_mem.sub hdiff_mem using 1
  ext s
  simp

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp]
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
      congr 1; exact Finset.sum_congr rfl fun i _ ↦ by
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

/-- Addition preserves `IsItoIntegral`. -/
theorem IsItoIntegral.add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω + K t ω) (fun t ω ↦ I t ω + J t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hJ.ae_continuous] with _ hcI hcJ; exact hcI.add hcJ
  exists_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hG₁⟩ := hI.exists_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hJ.exists_approx t
    choose M σ b _ hσ hb hhold hgain using fun k ↦
      Finance.exists_simpleHolding_simpleGains_eq_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    refine ⟨M, σ, b, fun k ↦ (hσ k).monotoneOn, hb, fun ε hε ↦
      TauCeti.tendsto_measure_le_lintegral_of_le_two_mul_add (fun k ω ↦ ?_) (fun k s ω ↦ ?_)
        hE₁ hE₂ hε,
      (hG₁.add hG₂).congr_left fun k ↦ .of_forall fun ω ↦ (hgain k W t ω).symm⟩
    · exact (((((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub
        hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const
          2).comp (measurable_id.prodMk measurable_const)).aemeasurable
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
      intro ε hε
      refine TauCeti.tendsto_measure_le_lintegral_of_le_two_mul_add
        (f₁ := fun k s ω ↦ ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2)
        (f₂ := fun k s ω ↦ ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2)
        (fun k ω ↦ (((((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const
            2).comp (measurable_id.prodMk measurable_const)).aemeasurable)
        (fun k s ω ↦ ?_) hKH hLH hε
      rw [hhold k s ω, ← mul_add]
      exact TauCeti.eNorm_sub_sq_le_two_mul _ _ (H s ω)
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
  refine TauCeti.indist_of_ae_continuous hI.ae_continuous hJ.ae_continuous fun t ↦ ?_
  obtain ⟨m, σ, b, hσ, hb, hLH, hLJ⟩ := hJ.exists_approx t
  exact hI.ae_eq_of_tendstoInMeasure hW hσ hb hLH hLJ

/-- Against a pre-Brownian motion relative to the filtration, two Itô integrals whose integrands
agree product-almost-everywhere on every finite horizon are indistinguishable. -/
theorem isItoIntegral_indist_of_ae_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure t).prod P] Function.uncurry K) :
    I ≡ᵐ[P] J := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  exact isItoIntegral_unique hW (hI.congr_integrand hJ.isStronglyPredictable hHK) hJ

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
  exists_approx t := ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha,
    fun ε hε ↦ by simp [hε.ne'], fun ε hε ↦ by simp [hε.ne']⟩

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem IsItoIntegral.mono {𝒢 : Filtration ℝ≥0 mΩ} (hI : IsItoIntegral ℱ P W H I)
    (hFG : ℱ ≤ 𝒢) : IsItoIntegral 𝒢 P W H I where
  isStronglyPredictable := hI.isStronglyPredictable.mono (Filtration.predictable_mono hFG)
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, fun k j hj ↦ (ha k j hj).mono (hFG _), hen, hg⟩

/-- Transporting `IsItoIntegral` to a larger filtration on the completed ambient space
`(NullMeasurableSpace Ω P, P.completion)`. -/
theorem IsItoIntegral.mono_completion (hI : IsItoIntegral ℱ P W H I)
    {𝒢 : Filtration ℝ≥0 (eventuallyMeasurableSpace mΩ (ae P))}
    (hFG : ∀ t, ℱ t ≤ 𝒢 t) :
    @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance 𝒢 P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.mono
    (measurableSpace_le_predictable_of_measurableSet
      (fun _ hA ↦ measurableSet_predictable_singleton_bot_prod (hFG ⊥ _ hA))
      (fun i _ hA ↦ measurableSet_predictable_Ioi_prod (i := i) (hFG i _ hA)))
  ae_continuous := hI.ae_continuous.filter_mono P.ae_completion.le
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_approx t
    refine ⟨n, τ, a, hτ, fun k j hj ↦ (ha k j hj).mono (hFG _), fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
    · exact (hen ε hε).congr fun k ↦ (Measure.completion_apply P _).symm
    · exact (hg ε hε).congr fun k ↦ (Measure.completion_apply P _).symm

/-- Completing the ambient space and adjoining all ambient null sets to the filtration preserves
`IsItoIntegral`. -/
theorem IsItoIntegral.nullAugment (hI : IsItoIntegral ℱ P W H I) :
    @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P) P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) :=
  hI.mono_completion (ℱ.le_nullAugment P)

/-- Passing to the usual right-continuous null augmentation preserves `IsItoIntegral`. -/
theorem IsItoIntegral.rightCont_nullAugment (hI : IsItoIntegral ℱ P W H I) :
    @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P).rightCont P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) :=
  @IsItoIntegral.mono (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P) P.completion _ _ _
    (ℱ.nullAugment P).rightCont hI.nullAugment ((ℱ.nullAugment P).le_rightCont)

/-- Against a filtered pre-Brownian motion with paths almost surely right-continuous at each
fixed time, any raw Itô integral is indistinguishable from any Itô integral constructed on the
usual right-continuous null augmentation `(ℱ.nullAugment P).rightCont`. -/
theorem isItoIntegral_indist_rightCont_nullAugment
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ s, ∀ᵐ ω ∂P, ContinuousWithinAt (W · ω) (Ioi s) s)
    (hI : IsItoIntegral ℱ P W H I)
    {J : ℝ≥0 → NullMeasurableSpace Ω P → ℝ}
    (hJ : @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance
      (ℱ.nullAugment P).rightCont P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω) J) :
    (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) ≡ᵐ[P.completion] J :=
  @isItoIntegral_unique (NullMeasurableSpace Ω P) inferInstance
    (ℱ.nullAugment P).rightCont P.completion
    (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
    (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
    (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) J
    (hW.rightCont_nullAugment hcont) hI.rightCont_nullAugment hJ

end TauCeti.Probability
