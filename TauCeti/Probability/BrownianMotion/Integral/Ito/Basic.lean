/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Predictable.Basic

/-!
# Itô integrals against Brownian motion: specification, algebra, and uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings on nondecreasing deterministic grids (allowing
repeated dates), with heights known at the left endpoints of their intervals, approximate `H` on
`(0,t]` in square energy in probability, while their elementary integrals at `t` converge in
probability to `I t`. Square energy is a lower Lebesgue integral, so an infinite energy is never
read as the default value zero of a divergent Bochner integral. The heights need not be bounded;
bounded approximants are a special case.

Against a pre-Brownian motion relative to the filtration, the elementary integrals of any simple
holdings on nondecreasing deterministic grids (allowing repeated dates) with left-measurable heights
converging in pathwise square energy on `(0, T]` along a filter converge in probability at every
earlier horizon `v ≤ T` to `I v` (`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains`,
`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains_of_le`), so any limit in
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

Against an adapted integrator (or any integrator with almost-everywhere strongly measurable
marginals) the Itô integral is almost everywhere strongly measurable at each time
(`TauCeti.Probability.IsItoIntegral.aestronglyMeasurable`).

The elementary integral of a simple holding on a nondecreasing grid with left-measurable heights
is its Itô integral against every process with almost surely continuous paths
(`TauCeti.Probability.isItoIntegral_simpleGains`). Every integrand admitting an Itô integral
satisfies `LocallyBrownianIntegrable` (`IsItoIntegral.locallyBrownianIntegrable`), and
`IsItoIntegral` is closed under filtration enlargement (`IsItoIntegral.mono_filtration`),
integrand congruence (`IsItoIntegral.congr_integrand`, `IsItoIntegral.congr_ae`), linearity
(`IsItoIntegral.smul`, `IsItoIntegral.const_mul`, `IsItoIntegral.add`, `IsItoIntegral.sub`),
bounded initial and post-`u` multipliers (`IsItoIntegral.bdd_mul`,
`IsItoIntegral.indicator_Ioi_bdd_mul`), sequential limits (`IsItoIntegral.of_seq`), and against
a filtered pre-Brownian motion `W`, `(s, ∞)` multiplication by arbitrary `ℱ s`-measurable variables
(`IsItoIntegral.ite_lt_mul`). Against a filtered pre-Brownian integrator with almost surely
continuous paths, existence of the integral is proved in
`TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry` for square-integrable integrands and in
`TauCeti.Probability.BrownianMotion.Integral.Ito.Local` for localized integrands.

The predicate transfers to an absolutely continuous finite measure with the same driver
and approximants; this does not assert that the driver is still Brownian.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory TopologicalSpace
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W B H K I J : ℝ≥0 → Ω → ℝ}

/-- `I` is an **Itô integral** of the integrand `H` against `W`. The integrand is predictable,
almost every path of `I` is continuous, and at every time `t` there are simple holdings on
nondecreasing deterministic grids (repeated dates are allowed) with heights known at the left
endpoints of their intervals such that `∫_(0,t] |Kₖ - H|² ds → 0` in probability while their
elementary integrals at `t` converge to `I t` in probability. The square energy is a lower Lebesgue
integral, so it is infinite rather than zero when the square error is not integrable. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W H I : ℝ≥0 → Ω → ℝ) :
    Prop where
  /-- The integrand is predictable, so its square errors are measurable in time. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every path of the integral is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous fun t ↦ I t ω
  /-- At each time `t`, simple holdings on nondecreasing deterministic grids (repeated dates are
  allowed) with left-measurable heights approximate the integrand on `(0,t]` in square energy in
  probability, and their elementary integrals at `t` converge to `I t` in probability. -/
  exists_approx : ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
    (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
    (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-- An Itô integral with respect to a fixed driver is still an Itô integral under an
absolutely continuous finite measure. The same simple holdings witness the approximation. -/
theorem IsItoIntegral.mono_ac {Q : Measure Ω} [IsFiniteMeasure Q]
    (hI : IsItoIntegral ℱ P W H I) (hQP : Q ≪ P) : IsItoIntegral ℱ Q W H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hQP.ae_le hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, ha, fun ε hε ↦ hQP.tendsto_measure_zero (hE ε hε), hG.mono_ac hQP⟩

/-- Against a filtered pre-Brownian motion, **every** family of left-measurable simple holdings
whose pathwise square-energy error on `(0, t]` tends to zero in probability along `l` has
elementary gains at `t` converging in probability along `l` to `I t`. -/
theorem IsItoIntegral.tendstoInMeasure_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {ι : Type*} {l : Filter ι} {t : ℝ≥0}
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ↦ Finance.simpleGains (τ i) (n i) (a i) W t) l (I t) := by
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hI.exists_approx t
  choose N ρ c _ hρ hc hhold hgains using fun p : ι × ℕ ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ p.1) (hτ₂ p.2) (ha p.1) (ha₂ p.2)
  let lp : Filter (ι × ℕ) := l ×ˢ (atTop : Filter ℕ)
  have henergy : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun p : ι × ℕ ↦ P {ω | δ ≤
      ∫⁻ s, ‖Finance.simpleHolding (ρ p) (N p) (c p) s ω‖ₑ ^ 2 ∂timeMeasure t}) lp (𝓝 0) := by
    simp_rw [hhold]
    exact fun _ hδ ↦ tendsto_measure_lintegral_enorm_sub_sq (l := lp)
      (f := fun p ↦ Finance.simpleHolding (τ p.1) (n p.1) (a p.1))
      (g := fun p ↦ Finance.simpleHolding (τ₂ p.2) (n₂ p.2) (a₂ p.2)) (h := fun _ ↦ H)
      (.of_forall fun p ↦ .of_forall fun ω ↦
        (Finance.isStronglyPredictable_simpleHolding (ha p.1)).aemeasurable_enorm_sub_pow
          hI.isStronglyPredictable ω 2)
      (fun _ hε ↦ (hE _ hε).comp tendsto_fst) (fun _ hε ↦ (hE₂ _ hε).comp tendsto_snd) hδ
  have htot : TendstoInMeasure P
      (fun p : ι × ℕ ↦ Finance.simpleGains (τ p.1) (n p.1) (a p.1) W t) lp (I t) := by
    simpa only [sub_add_cancel, zero_add] using
      ((hW.tendstoInMeasure_simpleGains_of_energy (fun p ↦ (hρ p).monotoneOn) hc t
        henergy).congr_left fun p ↦ .of_forall fun ω ↦ hgains p W t ω).add
        (fun ε hε ↦ (hG₂ ε hε).comp tendsto_snd : TendstoInMeasure P _ lp (I t))
  intro ε hε; rw [← Filter.map_fst_prod l (atTop : Filter ℕ), tendsto_map'_iff]; exact htot ε hε

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

/-- The elementary integral of a simple holding on a nondecreasing grid with heights known at the
left endpoints of its intervals is its Itô integral against every process with almost surely
continuous paths. -/
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

namespace IsItoIntegral

/-! ### Congruence, filtration enlargement, initial value, and pathwise domain -/

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ s, W s =ᵐ[P] B s) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hgains⟩ := hI.exists_approx t
    refine ⟨n, τ, a, hτ, ha, henergy, hgains.congr_left fun k ↦ ?_⟩
    exact ((ae_ball_iff (finite_Iic (n k)).countable).2 fun j _ ↦ hWB (min (τ k j) t)).mono
      Finance.simpleGains_congr_price

/-- Replacing the integrand by a predictable representative agreeing a.e. in time on a.e. path
preserves `IsItoIntegral`. -/
theorem congr_ae (hI : IsItoIntegral ℱ P W H I) (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω)) :
    IsItoIntegral ℱ P W K I :=
  ⟨hK, hI.ae_continuous, fun t ↦
    let ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hE ε hε).congr fun m ↦ measure_congr <| (hHK t).mono fun ω hω ↦
      iff_of_eq <| congrArg (ε ≤ ·) <| lintegral_congr_ae <|
        hω.mono fun s (hs : H s ω = K s ω) ↦ by rw [hs], hG⟩⟩

/-- For an `SFinite` measure `P`, replacing the integrand by a predictable process agreeing
`(dt × P)`-a.e. on each finite horizon preserves `IsItoIntegral`. -/
theorem congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure t).prod P]
      Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hgains⟩ := hI.exists_approx t
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] fun s ↦ K s ω :=
      Measure.ae_ae_of_ae_prod <| (Measure.measurePreserving_swap (μ := P)
        (ν := timeMeasure t)).quasiMeasurePreserving.ae_eq_comp (hHK t)
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (henergy ε hε).congr fun k ↦ measure_congr ?_, hgains⟩
    filter_upwards [hsec] with ω hω
    rw [lintegral_congr_ae (hω.mono fun s hs ↦
      congrArg (‖Finance.simpleHolding (τ k) (n k) (a k) s ω - ·‖ₑ ^ 2) hs)]

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem mono_filtration {𝒢 : Filtration ℝ≥0 mΩ} (hI : IsItoIntegral ℱ P W H I) (hle : ℱ ≤ 𝒢) :
    IsItoIntegral 𝒢 P W H I where
  isStronglyPredictable := hI.isStronglyPredictable.mono (Filtration.predictable_mono hle)
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hgains⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, fun k i hi ↦ (ha k i hi).mono (hle (τ k i)), henergy, hgains⟩

/-- Every Itô integral vanishes almost surely at time `0`. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, hτ, -, -, hgains⟩ := hI.exists_approx 0
  exact tendstoInMeasure_ae_unique
    (hgains.congr_left fun k ↦ .of_forall fun ω ↦ Finance.simpleGains_of_le (hτ k) bot_le W ω)
    (tendstoInMeasure_const 0)

/-- Every integrand admitting an `IsItoIntegral` belongs to `LocallyBrownianIntegrable ℱ P`,
with no finiteness assumption on `P` or Brownian assumption on `W`. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun N ↦ ?_⟩
  obtain ⟨n, τ, a, -, ha, henergy, -⟩ := hI.exists_approx N
  let E (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure N
  have hnull : P {ω | ∀ k, 1 ≤ E k ω} = 0 :=
    nonpos_iff_eq_zero.mp <| ge_of_tendsto' (henergy 1 zero_lt_one) fun k ↦
      measure_mono (s := {ω | ∀ k, 1 ≤ E k ω}) fun _ hω ↦ hω k
  have hae : ∀ᵐ ω ∂P, ∃ k, E k ω < 1 := by
    rw [ae_iff]
    simpa [not_exists, not_lt] using hnull
  filter_upwards [hae] with ω ⟨k, hk⟩
  rw [← NNReal.coe_natCast N, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
  have hpred := Finance.isStronglyPredictable_simpleHolding (ha k)
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) 2 (timeMeasure N) :=
    MemLp.of_bound hpred.stronglyMeasurable_path.aestronglyMeasurable
      (∑ i ∈ range (n k), ‖a k i ω‖) (.of_forall fun s ↦ by
        rw [Finance.simpleHolding_def]
        exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_indicator_le_norm_self _ _))
  have hdiff : MemLp (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω) 2
      (timeMeasure N) :=
    ((hpred.stronglyMeasurable_path.sub
        hI.isStronglyPredictable.stronglyMeasurable_path).aestronglyMeasurable
      |>.memLp_two_iff_lintegral_enorm_sq_lt_top).mpr (lt_trans hk ENNReal.one_lt_top)
  exact (hL.sub hdiff).ae_eq (.of_forall fun _ ↦ sub_sub_cancel _ _)

/-- Every Itô integral against an integrator with almost-everywhere strongly measurable marginals
is almost-everywhere strongly measurable at each horizon, without assuming adaptation of `I`. -/
theorem aestronglyMeasurable_of_aestronglyMeasurable (hW : ∀ s, AEStronglyMeasurable (W s) P)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) : AEStronglyMeasurable (I t) P := by
  obtain ⟨n, g, a, _, ha, _, hG⟩ := hI.exists_approx t
  exact hG.aestronglyMeasurable fun m ↦ Finance.aestronglyMeasurable_simpleGains
    (fun j hj ↦ ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable) fun _ _ ↦ hW _

/-- Against an adapted integrator, an Itô integral is almost everywhere strongly measurable at
each time, as a limit in probability of elementary integrals. -/
theorem aestronglyMeasurable (hW : Adapted ℱ W) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) : AEStronglyMeasurable (I t) P :=
  hI.aestronglyMeasurable_of_aestronglyMeasurable
    (fun s ↦ ((hW.stronglyAdapted s).mono (ℱ.le s)).aestronglyMeasurable) t

/-! ### Elementary and constant integrands -/

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp]
theorem zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := .of_forall fun _ ↦ continuous_const
  exists_approx _ :=
    ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ _ _ _ ↦ le_rfl,
      fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim,
      fun _ hε ↦ by simp [Finance.simpleHolding_def, hε.not_ge],
      (tendstoInMeasure_const 0).congr_left fun _ ↦ .of_forall fun _ ↦ by
        simp [Finance.simpleGains_def]⟩

/-- An `ℱ u`-measurable `ξ` held on `(u, v]` (`u ≤ v`) has clipped increment gains
`ξ * (W (v ⊓ t) - W (u ⊓ t))` as its Itô integral when `W` is `P`-a.s. continuous. -/
theorem indicator_Ioc {u v : ℝ≥0} {ξ : Ω → ℝ} (huv : u ≤ v)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hξ : StronglyMeasurable[ℱ u] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ ξ ω) t)
      (fun t ω ↦ ξ ω * (W (min v t) ω - W (min u t) ω)) := by
  let τ : ℕ → ℝ≥0 := fun i ↦ if i = 0 then u else v
  have hτ : MonotoneOn τ (Iic 1) := fun i _ j _ hij ↦ by
    dsimp [τ]; split_ifs <;> first | exact le_rfl | exact huv | omega
  convert isItoIntegral_simpleGains (ℱ := ℱ) (P := P) (n := 1) (τ := τ) (a := fun _ ↦ ξ)
    hcont hτ (fun i hi ↦ by obtain rfl : i = 0 := (by omega); exact hξ) using 1 <;>
    (ext t ω; simp [Finance.simpleHolding_def, Finance.simpleGains_def, τ])

/-- A time-constant `ℱ 0`-measurable `ξ` has `t ↦ ξ * (W t - W 0)` as an Itô integral when `W`
is `P`-a.s. continuous, with no finiteness assumption on `P`, moment assumption on `ξ`, or
`W 0 = 0`. -/
theorem const_sub_initial {ξ : Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * (W t ω - W 0 ω)) where
  isStronglyPredictable :=
    ((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable
  ae_continuous := hcont.mono fun _ hω ↦ by fun_prop
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, henergy, hgains⟩ :=
      (indicator_Ioc (P := P) (zero_le : (0 : ℝ≥0) ≤ t) hcont hξ).exists_approx t
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (henergy ε hε).congr fun k ↦ by
      congr 1; ext ω; simp only [Set.mem_ofPred_eq]
      rw [lintegral_congr_ae ((ae_mem_Ioc_timeMeasure t).mono fun _ hs ↦ by
        rw [indicator_of_mem hs])],
      by simpa only [min_self, min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)] using hgains⟩

/-- When `W` is `P`-a.s. continuous with `W 0 =ᵐ[P] 0`, a time-constant `ℱ 0`-measurable `ξ` has
`t ↦ ξ * W t` as a continuous Itô integral. -/
theorem const {ξ : Ω → ℝ} (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hW₀ : W 0 =ᵐ[P] 0) (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * W t ω) :=
  (const_sub_initial hcont hξ).congr (hW₀.mono fun _ hω _ ↦ by simp [hω])

/-- For an a.s. continuous integrator vanishing a.s. at `0`, `W` is an Itô integral of `1`. -/
theorem one (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hW₀ : W 0 =ᵐ[P] 0) :
    IsItoIntegral ℱ P W 1 W := by
  simpa only [Pi.one_def, one_mul] using
    const (ℱ := ℱ) (ξ := fun _ ↦ (1 : ℝ)) hW hW₀ stronglyMeasurable_const

/-! ### Linearity and bounded initial multipliers -/

/-- Multiplying an integrand by a bounded `ℱ 0`-measurable random variable `ξ` multiplies its Itô
integral by `ξ`, on any measure `P` and for any integrator `W`. -/
theorem bdd_mul (hI : IsItoIntegral ℱ P W H I) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ ξ ω * H t ω) (fun t ω ↦ ξ ω * I t ω) := by
  obtain ⟨Cξ, hCξ⟩ := hb
  refine ⟨(((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable).mul
    hI.isStronglyPredictable, hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω,
    fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, henergy, hgains⟩ := hI.exists_approx t
  refine ⟨n, τ, fun k i ω ↦ ξ ω * a k i ω, hτ,
    fun k i hi ↦ (hξ.mono (ℱ.mono bot_le)).mul (ha k i hi),
    fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_bdd_mul
      (μ := timeMeasure t) (ν := P) hCξ henergy (fun k s ω ↦ ?_) hε,
    (hgains.bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ by
      rw [Finance.simpleGains_mul_left, smul_eq_mul]) .rfl⟩
  rw [Finance.simpleHolding_mul_left, ← mul_sub, eNorm_mul]

/-- Scaling an integrand by a constant scales its Itô integral. -/
theorem smul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (c • H) (c • I) :=
  hI.bdd_mul stronglyMeasurable_const ⟨‖c‖, fun _ ↦ le_rfl⟩

/-- Scaling an integrand by a constant scales its Itô integral (pointwise multiplication form). -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) :=
  hI.smul c

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (-H) (-I) := by
  simpa [neg_one_smul] using hI.smul (-1 : ℝ)

/-- Negating both the integrand and the integral process preserves `IsItoIntegral`. -/
@[simp] theorem neg_iff : IsItoIntegral ℱ P W (-H) (-I) ↔ IsItoIntegral ℱ P W H I :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

/-- Adding two integrands adds their Itô integrals. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H + K) (I + J) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := hI.ae_continuous.mp <| hJ.ae_continuous.mono fun _ hJω hIω ↦ hIω.add hJω
  exists_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, he₁, hg₁⟩ := hI.exists_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, he₂, hg₂⟩ := hJ.exists_approx t
    choose n τ b _ hτ hbm hhold hgains using fun k ↦
      Finance.exists_simpleHolding_simpleGains_eq_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    refine ⟨n, τ, b, fun k ↦ (hτ k).monotoneOn, hbm, fun ε hε ↦ ?_,
      (hg₁.add hg₂).congr (fun k ↦ .of_forall fun ω ↦ (hgains k W t ω).symm) .rfl⟩
    simp_rw [hhold, Pi.add_apply, add_sub_add_comm]
    exact MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
      (.of_forall fun k ω ↦
        (IsStronglyPredictable.measurable_enorm_sq_path
          (H := fun s ω ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω)
          ((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub
            hI.isStronglyPredictable)).aemeasurable)
      he₁ he₂ hε

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-- **Sequential closure of the Itô integral.** If Itô integrals `(H_seq k, U_seq k)` approximate a
predictable `H` in pathwise square energy in probability on every finite horizon and `U_seq k t`
converges in probability to `I t` for an a.s. continuous `I`, then `I` is an Itô integral of `H`. -/
theorem of_seq {H_seq : ℕ → ℝ≥0 → Ω → ℝ} {U_seq : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H) (hI : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hU : ∀ k, IsItoIntegral ℱ P W (H_seq k) (U_seq k))
    (hE : ∀ t : ℝ≥0, ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖H_seq k s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hG : ∀ t : ℝ≥0, TendstoInMeasure P (fun k ↦ U_seq k t) atTop (I t)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hI, fun t ↦ ?_⟩
  let δ (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ k
  have hδ_lim : Tendsto δ atTop (𝓝 0) := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hstep (k : ℕ) : ∃ N grid height, MonotoneOn grid (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (grid j)] (height j)) ∧
      P {ω | δ k ≤ ∫⁻ s, ‖Finance.simpleHolding grid N height s ω - H_seq k s ω‖ₑ ^ 2
        ∂timeMeasure t} ≤ δ k ∧
      P {ω | (2⁻¹ ^ k : ℝ) ≤ ‖Finance.simpleGains grid N height W t ω - U_seq k t ω‖} ≤ δ k :=
    let ⟨n, τ, a, hτ, ha, hEk, hGk⟩ := (hU k).exists_approx t
    let hδp : 0 < δ k := ENNReal.pow_pos (by simp) k
    let ⟨m, hm₁, hm₂⟩ := (((hEk (δ k) hδp).eventually (eventually_lt_nhds hδp)).and
      (((tendstoInMeasure_iff_norm.1 hGk) (2⁻¹ ^ k) (by positivity)).eventually
        (eventually_lt_nhds hδp))).exists
    ⟨n m, τ m, a m, hτ m, ha m, hm₁.le, hm₂.le⟩
  choose N grid height hgrid hheight hE_diag hG_diag using hstep
  refine ⟨N, grid, height, hgrid, hheight, fun _ hε ↦
    tendsto_measure_lintegral_enorm_sub_sq (h := H_seq)
      (.of_forall fun k ↦ .of_forall fun ω ↦
        (Finance.isStronglyPredictable_simpleHolding (hheight k)).aemeasurable_enorm_sub_pow
          (hU k).isStronglyPredictable ω 2)
      (fun _ hδ ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ_lim
        (.of_forall fun _ ↦ zero_le) ((hδ_lim.eventually (eventually_lt_nhds hδ)).mono fun k hk ↦
          (measure_mono fun _ hω ↦ hk.le.trans hω).trans (hE_diag k)))
      (fun _ hδ ↦ by simpa only [eNorm_sub_rev (H _ _)] using hE t _ hδ) hε, ?_⟩
  simpa only [sub_add_cancel, Pi.zero_apply, zero_add] using
    (tendstoInMeasure_of_tendsto_measure_rate_lt_dist
      (f := fun k ω ↦ Finance.simpleGains (grid k) (N k) (height k) W t ω - U_seq k t ω) (g := 0)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by positivity) (by norm_num))
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ_lim (fun _ ↦ zero_le)
        fun k ↦ (measure_mono fun _ hω ↦ by
          rw [mem_ofPred_eq, Pi.zero_apply, dist_zero_right] at hω; exact hω.le).trans
          (hG_diag k))).add (hG t)

/-- Against a filtered pre-Brownian motion, elementary holdings whose pathwise square-energy error
on `(0, T]` tends to zero in probability along `l` have gains converging in probability at every
earlier horizon `v ≤ T` to `I v`. -/
theorem tendstoInMeasure_simpleGains_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {ι : Type*} {l : Filter ι} {v T : ℝ≥0} (hv : v ≤ T)
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure T}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ↦ Finance.simpleGains (τ i) (n i) (a i) W v) l (I v) :=
  hI.tendstoInMeasure_simpleGains hW hτ ha fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE ε hε) (fun _ ↦ zero_le)
      fun _ ↦ measure_mono fun _ hω ↦ hω.trans <| lintegral_mono' (timeMeasure_mono hv) le_rfl

/-! ### Uniqueness, congruence, and post-`u` multipliers -/

/-- Multiplying an integrand after time `u` by a bounded `ℱ u`-measurable `ξ` yields the post-`u`
Itô integral `t ↦ ξ * (I t - I (min u t))`, without assuming path continuity of `W`. -/
theorem indicator_Ioi_bdd_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {u : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ u] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (fun s ↦ ξ ω * H s ω) t)
      (fun t ω ↦ ξ ω * (I t ω - I (min u t) ω)) := by
  obtain ⟨Cξ, hCξ⟩ := hb
  refine ⟨hI.isStronglyPredictable.indicator_Ioi_mul hξ,
    hI.ae_continuous.mono fun _ hω ↦ by fun_prop, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, henergy, hgains⟩ := hI.exists_approx t
  have hgains_min := hI.tendstoInMeasure_simpleGains (t := min u t) hW hτ ha fun ε hε ↦
    MeasureTheory.tendsto_measure_lintegral_mono (timeMeasure_mono (min_le_right u t)) henergy hε
  refine ⟨n, fun k i ↦ max (τ k i) u, fun k i ω ↦ ξ ω * a k i ω,
    fun k _ hi _ hj hij ↦ max_le_max_right u (hτ k hi hj hij),
    fun k i hi ↦ (hξ.mono (ℱ.mono (le_max_right _ _))).mul
      ((ha k i hi).mono (ℱ.mono (le_max_left _ _))),
    fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_bdd_mul
      (μ := timeMeasure t) (ν := P) hCξ henergy (fun k s ω ↦ by
        rw [Finance.simpleHolding_mul_left, Finance.simpleHolding_max_eq]
        by_cases hs : u < s
        · simp [Set.mem_Ioi.mpr hs, ← mul_sub, eNorm_mul]
        · simp [Set.mem_Ioi, hs]) hε,
    ((hgains.sub hgains_min).bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ by
      rw [Finance.simpleGains_mul_left, Finance.simpleGains_max_eq, smul_eq_mul]) .rfl⟩

/-- Restricting an integrand to `(u, ∞)` yields the post-`u` Itô integral
`t ↦ I t - I (min u t)`, without assuming path continuity of `W`. -/
theorem indicator_Ioi (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (u : ℝ≥0) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (H · ω) t)
      (fun t ω ↦ I t ω - I (min u t) ω) := by
  simpa only [one_mul] using hI.indicator_Ioi_bdd_mul hW (u := u) (ξ := fun _ ↦ 1)
    stronglyMeasurable_const ⟨1, fun _ ↦ by norm_num⟩

/-- **Predictable `ℱ s`-multiplier rule on `(s, ∞)`.** Against a filtered pre-Brownian motion,
multiplying `H` on `(s, ∞)` by an `ℱ s`-measurable `ξ` yields the Itô integral
`t ↦ ξ * (I t - I (min s t))`, with no path continuity on `W` or moment bounds on `ξ`. -/
theorem ite_lt_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if s < t then ξ ω * H t ω else 0)
      (fun t ω ↦ ξ ω * (I t ω - I (min s t) ω)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨by
      simpa only [indicator_apply, Set.mem_Ioi] using
        hI.isStronglyPredictable.indicator_Ioi_mul hξ,
    hI.ae_continuous.mono fun _ hc ↦
      continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id))), fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
  let τ' (m j : ℕ) := max s (τ m j); let a' (m j : ℕ) (ω : Ω) := ξ ω * a m j ω
  have hhold (m : ℕ) (u : ℝ≥0) (ω : Ω) : Finance.simpleHolding (τ' m) (n m) (a' m) u ω =
      if s < u then ξ ω * Finance.simpleHolding (τ m) (n m) (a m) u ω else 0 := by
    rw [Finance.simpleHolding_def, Finance.simpleHolding_def]; split_ifs with hu
    · rw [mul_sum]; refine sum_congr rfl fun j _ ↦ ?_
      have hmem : u ∈ Set.Ioc (τ' m j) (τ' m (j + 1)) ↔ u ∈ Set.Ioc (τ m j) (τ m (j + 1)) := by
        simp only [τ', Set.mem_Ioc, max_lt_iff, le_max_iff, hu, true_and, hu.not_ge, false_or]
      by_cases hj : u ∈ Set.Ioc (τ m j) (τ m (j + 1)) <;> simp [hmem, hj, a']
    · exact sum_eq_zero fun j _ ↦ indicator_of_notMem
        (fun (h : u ∈ Set.Ioc _ _) ↦ hu ((le_max_left s (τ m j)).trans_lt h.1)) _
  refine ⟨n, τ', a', fun m _ hi _ hj hij ↦ max_le_max_left s (hτ m hi hj hij),
    fun m j hj ↦ (hξ.mono (ℱ.mono (le_max_left _ _))).mul
      ((ha m j hj).mono (ℱ.mono (le_max_right _ _))), fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_ge_zero_mul_of_ae_lt_top ((hξ.mono (ℱ.le s)).aemeasurable.eNorm.pow_const 2)
        (.of_forall fun _ ↦ ENNReal.pow_lt_top eNorm_lt_top) hE hε)
      (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω (hω : ε ≤ _) ↦ Set.mem_ofPred.2 <| hω.trans <| by
        rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)]
        exact lintegral_mono fun u ↦ by
          rw [hhold m u ω]; by_cases hu : s < u <;> simp [hu, ← mul_sub, eNorm_mul, mul_pow], ?_⟩
  refine ((tendstoInMeasure_const (μ := P) (l := atTop) ξ).smul
    (hξ.mono (ℱ.le s)).aestronglyMeasurable
    ((hI.aestronglyMeasurable hW.adapted t).sub (hI.aestronglyMeasurable hW.adapted _))
    (hG.sub (hI.tendstoInMeasure_simpleGains_of_le hW (min_le_right s t) hτ ha hE))).congr_left
    fun m ↦ .of_forall fun ω ↦ ?_
  rw [smul_eq_mul, Finance.simpleGains_def, Finance.simpleGains_def, Finance.simpleGains_def,
    ← sum_sub_distrib, mul_sum]
  have hpt (z : ℝ≥0) : W (min (max s z) t) ω + W (min z (min s t)) ω =
      W (min z t) ω + W (min s t) ω := by
    rcases le_total z s with h | h <;>
      simp only [max_eq_left, max_eq_right, ← min_assoc, min_eq_left, min_eq_right, h, add_comm]
  refine sum_congr rfl fun j _ ↦ by
    dsimp only [a', τ']; rw [← mul_sub, mul_assoc]; congr 2
    linarith [hpt (τ m (j + 1)), hpt (τ m j)]

/-- **Filtration invariance.** If `ℱ ≤ 𝒢` and `W` remains filtered pre-Brownian on `𝒢`, any Itô
integral of `H` on `ℱ` is indistinguishable from any Itô integral of `H` on `𝒢`. -/
theorem indist_of_le {𝒢 : Filtration ℝ≥0 mΩ} (hW : IsFilteredPreBrownianReal 𝒢 W P)
    (hℱ𝒢 : ℱ ≤ 𝒢) (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral 𝒢 P W H J) : I ≡ᵐ[P] J :=
  isItoIntegral_unique hW (hI.mono_filtration hℱ𝒢) hJ

/-- Two Itô integrals whose integrands agree a.e. in time on a.e. path are indistinguishable. -/
theorem indist_of_ae_eq_section (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω)) :
    I ≡ᵐ[P] J :=
  isItoIntegral_unique hW (hI.congr_ae hJ.isStronglyPredictable hHK) hJ

/-- **Integrand congruence**: predictable integrands agreeing `(dt × P)`-a.e. on every finite
horizon have `P`-indistinguishable continuous Itô integrals against `W`. -/
theorem indist_of_ae_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure t).prod P]
      Function.uncurry K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact isItoIntegral_unique hW (hI.congr_integrand hJ.isStronglyPredictable hHK) hJ

end IsItoIntegral

/-- Against a pre-Brownian motion relative to the filtration, the Itô integrals of an integrand
are exactly the processes indistinguishable from one of them. -/
theorem isItoIntegral_iff_indist (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W H J ↔ I ≡ᵐ[P] J :=
  ⟨isItoIntegral_unique hW hI, hI.congr⟩

/-- For an a.s. continuous filtered pre-Brownian motion `W`, `W` is an Itô integral of `1`. -/
theorem IsFilteredPreBrownianReal.isItoIntegral_one
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) : IsItoIntegral ℱ P W 1 W :=
  IsItoIntegral.one hcont hW.toIsPreBrownianReal.eval_zero_ae_eq_zero

end TauCeti.Probability
