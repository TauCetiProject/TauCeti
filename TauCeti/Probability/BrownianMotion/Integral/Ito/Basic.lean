/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.Predictable.Basic
import TauCeti.Probability.Process.ContinuousAE

/-!
# Itô integrals against Brownian motion and their uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings, with heights known at the left endpoints of
their intervals, approximate `H` on `(0,t]` in square energy in probability, while their
elementary integrals at `t` converge in probability to `I t`. Square energy is a lower Lebesgue
integral, so an infinite energy is never read as the default value zero of a divergent Bochner
integral. The heights need not be bounded; bounded approximants are a special case.

Against a pre-Brownian motion relative to the filtration, the elementary integrals of any simple
holdings approximating the integrand on `(0,t]` in square energy in probability converge in
probability to the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains`), and also at every earlier
time (`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains_of_le`); so any limit in
probability of them agrees almost surely with the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`). Against an adapted integrator
the Itô integral is almost everywhere strongly measurable at each time
(`TauCeti.Probability.IsItoIntegral.aestronglyMeasurable`). Such a sequence and the one
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
almost surely continuous paths (`TauCeti.Probability.isItoIntegral_simpleGains`). Existence of
the integral is not proved here.

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
  {W H I J : ℝ≥0 → Ω → ℝ}

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
  have hlt := ENNReal.add_lt_add hcon.1 hcon.2
  refine (hω.trans (lintegral_enorm_sub_sq_le_two_mul hmeas.aemeasurable)).not_gt ?_
  calc
    _ < 2 * (η + η) := by
      rw [two_mul, two_mul]
      exact ENNReal.add_lt_add hlt hlt
    _ = 4 * (ε / 4) := by ring
    _ ≤ ε := ENNReal.mul_div_le

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
  exists_approx t := ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha,
    fun ε hε ↦ by simp [hε.ne'], fun ε hε ↦ by simp [hε.ne']⟩

end TauCeti.Probability
