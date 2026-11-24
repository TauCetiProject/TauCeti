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
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE

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

Against a pre-Brownian motion relative to the filtration, the elementary integrals of any simple
holdings approximating the integrand on `(0,t]` in square energy in probability converge in
probability to the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains`), and also at every earlier
time (`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains_of_le`); so any limit in
probability of them agrees almost surely with the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`). Such approximants and the ones
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

Against an adapted integrator the Itô integral is almost everywhere strongly measurable at each
time (`TauCeti.Probability.IsItoIntegral.aestronglyMeasurable`).

The elementary integral of a simple holding is its Itô integral against every process with
almost surely continuous paths (`TauCeti.Probability.isItoIntegral_simpleGains`), and in
particular an `ℱ s`-measurable random height held on `(s, u]` integrates against `W` as
`ξ * (W (min u ·) - W (min s ·))` (`TauCeti.Probability.isItoIntegral_indicator_Ioc`).

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

/-! ### Private helper for `timeMeasure` square energy -/

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
      atTop (𝓝 0) :=
  TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_add (μ := timeMeasure t) (ν := P)
    (f := fun k s ω ↦ K k s ω - H s ω) (g := fun k s ω ↦ H s ω - L k s ω)
    (h := fun k s ω ↦ K k s ω - L k s ω)
    (fun k ω ↦ (((((hK k).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).comp
      (measurable_id.prodMk measurable_const)).aemeasurable)
    (fun _ _ _ ↦ (sub_add_sub_cancel _ _ _).symm)
    hKH (fun δ hδ ↦ by simpa only [eNorm_sub_rev] using hLH δ hδ) hε

/-! ### Uniqueness, basic properties, and closure of `IsItoIntegral` -/

/-- **Convergence to the Itô integral.** Against a pre-Brownian motion relative to the
filtration, if simple holdings with heights known at the left endpoints of their intervals
approximate the integrand on `(0,t]` in square energy in probability, then their elementary
integrals at `t` converge in probability to the Itô integral at `t`. -/
theorem IsItoIntegral.tendstoInMeasure_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {m : ℕ → ℕ} {σ : ℕ → ℕ → ℝ≥0}
    {b : ℕ → ℕ → Ω → ℝ} (hσ : ∀ k, MonotoneOn (σ k) (Iic (m k)))
    (hb : ∀ k j, j < m k → StronglyMeasurable[ℱ (σ k j)] (b k j))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (σ k) (m k) (b k) W t) atTop (I t) := by
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
  simpa using hKI.sub hdiff

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
    I t =ᵐ[P] X :=
  tendstoInMeasure_ae_unique (hI.tendstoInMeasure_simpleGains hW hσ hb hLH) hLX

/-- Simple holdings approximating the integrand on `(0,t]` in square energy in probability
also approximate it on `(0,s]` for every `s ≤ t`. So, against a pre-Brownian motion relative to
the filtration, their elementary integrals at `s` converge in probability to the Itô integral
at `s`. -/
theorem IsItoIntegral.tendstoInMeasure_simpleGains_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t) {m : ℕ → ℕ}
    {σ : ℕ → ℕ → ℝ≥0} {b : ℕ → ℕ → Ω → ℝ} (hσ : ∀ k, MonotoneOn (σ k) (Iic (m k)))
    (hb : ∀ k j, j < m k → StronglyMeasurable[ℱ (σ k j)] (b k j))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ u, ‖Finance.simpleHolding (σ k) (m k) (b k) u ω - H u ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (σ k) (m k) (b k) W s) atTop (I s) :=
  hI.tendstoInMeasure_simpleGains hW hσ hb fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hLH ε hε) (fun _ ↦ zero_le)
      fun k ↦ measure_mono fun ω hω ↦ by
        simp only [mem_ofPred_eq] at hω ⊢
        exact hω.trans (lintegral_mono' (timeMeasure_mono hst) le_rfl)

/-- Against an adapted integrator, an Itô integral is almost everywhere strongly measurable at
each time, as a limit in probability of elementary integrals. -/
theorem IsItoIntegral.aestronglyMeasurable (hW : Adapted ℱ W) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) : AEStronglyMeasurable (I t) P := by
  obtain ⟨n, τ, a, hτ, ha, -, hKI⟩ := hI.exists_approx t
  exact hKI.aestronglyMeasurable fun k ↦ ((Finance.stronglyAdapted_simpleGains (hτ k) (ha k)
    hW.stronglyAdapted t).mono (ℱ.le t)).aestronglyMeasurable

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

/-- An `ℱ s`-measurable random height held on `(s, u]` is an Itô integrand for
`ξ * (W (min u ·) - W (min s ·))` against every process with almost surely continuous paths. -/
theorem isItoIntegral_indicator_Ioc {s u : ℝ≥0} {ξ : Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) (hsu : s ≤ u)
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t)
      (fun t ω ↦ ξ ω * (W (min u t) ω - W (min s t) ω)) := by
  let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then s else u
  let a : ℕ → Ω → ℝ := fun _ ↦ ξ
  have hτ : MonotoneOn τ (Iic 1) := fun i _ j _ hij ↦ by
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [τ, hi, hj, hsu]; omega
  have ha : ∀ j < 1, StronglyMeasurable[ℱ (τ j)] (a j) := fun j hj ↦ by
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    simpa [τ] using hξ
  have hHold : Finance.simpleHolding τ 1 a = fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t := by
    ext t ω; simp [Finance.simpleHolding_def, τ, a]
  have hGain : Finance.simpleGains τ 1 a W = fun t ω ↦ ξ ω * (W (min u t) ω - W (min s t) ω) := by
    ext t ω; simp [Finance.simpleGains_def, τ, a]
  rw [← hHold, ← hGain]
  exact isItoIntegral_simpleGains hW hτ ha

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
      have hle := TauCeti.lintegral_enorm_add_sq_le_two_mul (μ := timeMeasure m)
        (f := fun s ↦ H s ω - Finance.simpleHolding (τ k) (n k) (a k) s ω)
        (g := fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω)
        ((((hHmeas.comp_measurable (measurable_prodMk_right (y := ω))).measurable.sub
          (Finance.measurable_simpleHolding (fun _ _ ↦ measurableSet_Ioc) ω)).eNorm.pow_const
            2).aemeasurable)
      simp only [sub_add_cancel] at hle
      by_contra hlt
      have hfin : ∫⁻ s, ‖H s ω - Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2
          ∂timeMeasure m < ∞ := by
        simpa only [eNorm_sub_rev] using (not_le.mp hlt).trans ENNReal.one_lt_top
      exact (hle.trans_lt (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.2 ⟨hfin, hKfin⟩))).ne hω
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
      Measure.ae_ae_eq_flip_of_ae_eq_uncurry (hHK t)
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
@[simp]
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
        (lintegral_eq_zero_iff' (((Finance.measurable_simpleHolding
          (fun _ _ ↦ measurableSet_Ioc) ω).sub measurable_const).eNorm.pow_const
            2).aemeasurable).2 <|
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
    choose n τ b _ hτ hb hhold hgain using fun k ↦
      Finance.exists_simpleHolding_simpleGains_eq_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    have hHmeas := hI.isStronglyPredictable.mono ℱ.predictable_le_prod
    refine ⟨n, τ, b, fun k ↦ (hτ k).monotoneOn, hb, fun _ hε ↦ ?_,
      by simpa only [funext fun k ↦ funext fun ω ↦ hgain k W t ω] using
        TendstoInMeasure.add hL₁ hL₂⟩
    refine TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_add (μ := timeMeasure t) (ν := P)
      (f := fun k s ω ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω)
      (g := fun k s ω ↦ Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - K s ω)
      (h := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (b k) s ω - (H s ω + K s ω))
      (fun k ω ↦ (((((Finance.measurable_simpleHolding (fun _ _ ↦ measurableSet_Ioc) ω).sub
        (hHmeas.comp_measurable measurable_prodMk_right).measurable).eNorm).pow_const
          2)).aemeasurable)
      (fun k s ω ↦ by rw [hhold k s ω]; ring) hE₁ hE₂ hε

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
