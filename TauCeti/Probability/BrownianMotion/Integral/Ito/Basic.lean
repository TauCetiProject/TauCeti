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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Predictable.Basic

/-!
# Itô integrals against Brownian motion: specification, algebra, and uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings, with heights known at the left endpoints of
their intervals, approximate `H` on `(0,t]` in square energy in probability, while their
elementary integrals at `t` converge in probability to `I t`. Square energy is a lower Lebesgue
integral, so an infinite energy is never read as the default value zero of a divergent Bochner
integral. The heights need not be bounded; bounded approximants are a special case.

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

The elementary integral of a simple holding on a nondecreasing grid with left-measurable heights
is its Itô integral against every process with almost surely continuous paths
(`TauCeti.Probability.isItoIntegral_simpleGains`). This file also establishes linearity,
bounded initial and post-`u` multipliers, `(dt × P)`-a.e. integrand congruence for an `SFinite`
measure `P` (`TauCeti.Probability.IsItoIntegral.congr_integrand`), and gains convergence in measure
for arbitrary approximating sequences against a filtered pre-Brownian motion. Existence of the
integral is proved in `TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, `L2`, and `Local`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W B H K I J : ℝ≥0 → Ω → ℝ}

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
  exists_approx : ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
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
  choose φ hφ using fun j : ℕ ↦ ((henergy 1 zero_lt_one).eventually (gt_mem_nhds
    (ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top : (0 : ℝ≥0∞) < 2⁻¹) j))).exists
  have hsum : (∑' j : ℕ, P {ω | 1 ≤ E (φ j) ω}) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [ENNReal.tsum_geometric_two]; exact ENNReal.ofNat_ne_top)
      (tsum_le_tsum fun j ↦ (hφ j).le)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨j, hj⟩ := hω.exists
  rw [← NNReal.coe_natCast N, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
  have hpred := Finance.isStronglyPredictable_simpleHolding (ha (φ j))
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω) 2
      (timeMeasure N) :=
    MemLp.of_bound ((hpred.mono ℱ.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
      (∑ i ∈ range (n (φ j)), ‖a (φ j) i ω‖) (.of_forall fun s ↦ by
        rw [Finance.simpleHolding_def]
        exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_indicator_le_norm_self _ _))
  have hdiff : MemLp (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω - H s ω) 2
      (timeMeasure N) :=
    (((hpred.sub hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable
      |>.memLp_two_iff_lintegral_enorm_sq_lt_top).mpr (lt_trans (not_le.mp hj) ENNReal.one_lt_top)
  exact (hL.sub hdiff).ae_eq (.of_forall fun _ ↦ sub_sub_cancel _ _)

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
      simpa only [smul_eq_mul] using
        (Finance.simpleGains_mul_left (τ k) (n k) ξ (a k) W t ω).symm) .rfl⟩
  rw [Finance.simpleHolding_mul_left, ← mul_sub, eNorm_mul]

/-- Scaling an integrand by a constant scales its Itô integral. -/
theorem smul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (c • H) (c • I) :=
  hI.bdd_mul stronglyMeasurable_const ⟨‖c‖, fun _ ↦ le_rfl⟩

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (-H) (-I) := by
  simpa [neg_one_smul] using hI.smul (-1 : ℝ)

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
      (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub
        hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
          (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
      he₁ he₂ hε

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-! ### Gains convergence, uniqueness, and post-`u` multipliers -/

/-- If left-measurable simple strategies approximate `H` in pathwise square energy in probability
on `(0, t]`, their elementary gains against a filtered pre-Brownian motion `W` converge in
probability to `I t`, without height bounds or path continuity of `W`. -/
theorem tendstoInMeasure_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t) := by
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, he₁, hg₁⟩ := hI.exists_approx t
  choose m σ b _ hσ hbm hhold hgains_sub using fun k ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ k) (hτ₁ k) (ha k) (ha₁ k)
  have he_sub : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0) := fun ε hε ↦ by
    simpa only [sub_add_sub_cancel, ← hhold] using
      MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
        (f := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
        (g := fun k s ω ↦ H s ω - Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω)
        (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
            (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
        henergy (by simpa only [eNorm_sub_rev] using he₁) hε
  have hdiff := (hW.tendstoInMeasure_simpleGains_of_energy
    (fun k ↦ (hσ k).monotoneOn) hbm t he_sub).congr_left fun k ↦ .of_forall (hgains_sub k W t)
  exact (hdiff.add hg₁).congr (fun _ ↦ .of_forall fun _ ↦ sub_add_cancel _ _)
    (.of_forall fun _ ↦ zero_add _)

/-- Two Itô integrals of the same integrand against a filtered pre-Brownian motion agree a.s. at
each horizon, without assuming path continuity of `W`. -/
theorem ae_eq_eval (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) (t : ℝ≥0) :
    I t =ᵐ[P] J t := by
  obtain ⟨n, τ, a, hτ, ha, he, hg⟩ := hJ.exists_approx t
  exact hI.ae_eq_of_tendstoInMeasure hW hτ ha he hg

end IsItoIntegral

/-- Against a pre-Brownian motion relative to the filtration, the Itô integrals of an integrand
are exactly the processes indistinguishable from one of them. -/
theorem isItoIntegral_iff_indist (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W H J ↔ I ≡ᵐ[P] J :=
  ⟨isItoIntegral_unique hW hI, hI.congr⟩

namespace IsItoIntegral

/-- Any Itô integral of `0` against a filtered pre-Brownian motion vanishes a.s. at each horizon. -/
theorem ae_eq_zero_of_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) (t : ℝ≥0) : I t =ᵐ[P] 0 :=
  hI.ae_eq_eval hW zero t

/-- Any Itô integral of `0` against a filtered pre-Brownian motion is indistinguishable from `0`. -/
theorem indist_zero_of_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) : I ≡ᵐ[P] 0 :=
  isItoIntegral_unique hW hI zero

/-- **Integrand congruence**: predictable integrands agreeing `(dt × P)`-a.e. on every finite
horizon have `P`-indistinguishable continuous Itô integrals against `W`. -/
theorem indist_of_ae_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure t).prod P]
      Function.uncurry K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact isItoIntegral_unique hW (hI.congr_integrand hJ.isStronglyPredictable hHK) hJ

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
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (henergy ε hε)
      (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ by
        simp only [Set.mem_ofPred_eq] at hω ⊢
        refine hω.trans ?_
        rw [← timeMeasure_restrict t u]
        exact lintegral_mono' Measure.restrict_le_self le_rfl
  refine ⟨n, fun k i ↦ max (τ k i) u, fun k i ω ↦ ξ ω * a k i ω,
    fun k _ hi _ hj hij ↦ max_le_max_right u (hτ k hi hj hij),
    fun k i hi ↦ (hξ.mono (ℱ.mono (le_max_right _ _))).mul
      ((ha k i hi).mono (ℱ.mono (le_max_left _ _))),
    fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_bdd_mul
      (μ := timeMeasure t) (ν := P) hCξ henergy (fun k s ω ↦ by
        rw [Finance.simpleHolding_max_eq u ξ s ω]
        by_cases hs : u < s
        · simp [Set.mem_Ioi.mpr hs, ← mul_sub, eNorm_mul]
        · simp [Set.mem_Ioi, hs]) hε,
    ((hgains.sub hgains_min).bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ by
      simpa only [smul_eq_mul] using (Finance.simpleGains_max_eq u ξ W t ω).symm) .rfl⟩

/-- Restricting an integrand to `(u, ∞)` yields the post-`u` Itô integral
`t ↦ I t - I (min u t)`, without assuming path continuity of `W`. -/
theorem indicator_Ioi (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (u : ℝ≥0) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (H · ω) t)
      (fun t ω ↦ I t ω - I (min u t) ω) := by
  simpa only [one_mul] using hI.indicator_Ioi_bdd_mul hW (u := u) (ξ := fun _ ↦ 1)
    stronglyMeasurable_const ⟨1, fun _ ↦ by norm_num⟩

end IsItoIntegral

end TauCeti.Probability
