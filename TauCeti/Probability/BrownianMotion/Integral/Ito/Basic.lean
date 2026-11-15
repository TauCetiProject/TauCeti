/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.TimeMeasure
public import Mathlib.Probability.Process.Indistinguishable
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# The Itô integral predicate and uniqueness

`TauCeti.IsItoIntegral ℱ P W H I` characterizes a process `I` as an Itô stochastic integral of a
predictable integrand `H` against an integrator `W`: almost every path of `I` is continuous, and
at each deterministic horizon `t` some sequence of left-measurable finite-grid holdings
approximates `H` in pathwise square energy in probability while its elementary gains converge in
probability to `I t`. Pathwise square errors are measured by lower Lebesgue integrals on `(0, t]`,
so divergent pathwise energies take the value `∞` rather than a Bochner fallback zero. Neither
uniform height bounds on the elementary approximants nor adaptation of `I` are built into the
predicate, allowing explicit pathwise formulas to be verified directly (such as
`IsItoIntegral.const` and `IsItoIntegral.one`) and then compared with canonical progressive
versions.

Any integrand admitting an Itô integral automatically belongs to `LocallyBrownianIntegrable`
(`IsItoIntegral.locallyBrownianIntegrable`), and the predicate is closed under filtration
enlargement (`IsItoIntegral.mono_filtration`), product-a.e. integrand replacement
(`IsItoIntegral.congr_ae_prod`), sequential limits in pathwise square energy and fixed-time
probability (`IsItoIntegral.of_seq`), and against a filtered pre-Brownian motion `W` multiplication
on `(s, ∞)` by any `ℱ s`-measurable random variable (`IsItoIntegral.ite_lt_mul`). Against a
filtered pre-Brownian motion `W`, every family of elementary holdings converging in pathwise square
energy on `(0, T]` along a filter has gains converging in probability at every horizon `v ≤ T` to
`I v` (`IsItoIntegral.tendstoInMeasure_simpleGains`,
`IsItoIntegral.tendstoInMeasure_simpleGains_of_le`), without requiring path continuity of `W`.
Consequently, Itô integrals are unique up to indistinguishability (`IsItoIntegral.indist`,
`IsItoIntegral.indist_of_le`) and depend on the integrand only up to `(timeMeasure T).prod P`-almost
everywhere equality on finite horizons (`IsItoIntegral.indist_of_ae_eq_prod`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W B H K I J : ℝ≥0 → Ω → ℝ}

/-- `I` is an Itô stochastic integral of `H` against `W` on `(Ω, ℱ, P)` if `H` is predictable,
`I` has almost surely continuous paths, and at each horizon `t` there exist elementary
predictable holdings whose pathwise square-energy errors on `(0, t]` tend to zero in probability
and whose elementary gains at `t` tend to `I t` in probability. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is literally predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every sample path of the integral process is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At each horizon, elementary predictable holdings approximate the integrand in pathwise
  square energy in probability while their elementary integrals converge in probability to `I t`. -/
  exists_seq_approx : ∀ t : ℝ≥0,
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
      (∀ m, MonotoneOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
      TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ m) (n m) (a m) W t) atTop (I t)

namespace IsItoIntegral

/-- Any integrand admitting an Itô integral has locally finite pathwise square energy. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun k ↦ ?_⟩
  rw [← NNReal.coe_natCast k, NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
  obtain ⟨n, τ, a, -, -, hE, -⟩ := hI.exists_seq_approx k
  let E (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
      ∂Probability.timeMeasure k
  have hnull : P (⋂ m, {ω | (1 : ℝ≥0∞) ≤ E m ω}) = 0 :=
    le_antisymm (ge_of_tendsto' (hE 1 one_pos) fun m ↦ measure_mono (iInter_subset _ m))
      zero_le
  have hex : ∀ᵐ ω ∂P, ∃ m, E m ω < 1 := by
    rw [ae_iff]
    convert hnull using 2
    ext ω
    simp
  have hmH : StronglyMeasurable (Function.uncurry H) :=
    hI.isStronglyPredictable.mono ℱ.predictable_le_prod
  filter_upwards [hex] with ω ⟨m, hm⟩
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω) 2
      (Probability.timeMeasure k) := by
    simp only [Finance.simpleHolding_def]
    exact memLp_finsetSum _ fun j _ ↦
      (memLp_const (a m j ω)).indicator measurableSet_Ioc.nullMeasurableSet
  have hsub : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω) 2
      (Probability.timeMeasure k) := by
    have hsm : AEStronglyMeasurable
        (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω)
        (Probability.timeMeasure k) :=
      hL.aestronglyMeasurable.sub
        (hmH.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    exact hsm.memLp_two_iff_lintegral_enorm_sq_lt_top.2 (hm.trans_le le_top)
  simpa only [Pi.sub_def, sub_sub_cancel] using hL.sub hsub

/-- Every Itô integral against an integrator with almost-everywhere strongly measurable marginals
is almost-everywhere strongly measurable at each horizon, without assuming adaptation of `I`. -/
theorem aestronglyMeasurable (hW : ∀ s, AEStronglyMeasurable (W s) P)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    AEStronglyMeasurable (I t) P := by
  obtain ⟨n, g, a, _, ha, _, hG⟩ := hI.exists_seq_approx t
  refine hG.aestronglyMeasurable fun m ↦ ?_
  have hdef : Finance.simpleGains (g m) (n m) (a m) W t =
      fun ω ↦ ∑ j ∈ range (n m),
        a m j ω * (W (min (g m (j + 1)) t) ω - W (min (g m j) t) ω) :=
    funext (Finance.simpleGains_def _ _ _ W t)
  rw [hdef]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j hj ↦
    ((ha m j (mem_range.1 hj)).mono (ℱ.le _)).aestronglyMeasurable.mul ((hW _).sub (hW _))

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp]
theorem zero : IsItoIntegral ℱ P W 0 0 := by
  refine ⟨stronglyMeasurable_zero, .of_forall fun _ ↦ continuous_const, fun t ↦ ?_⟩
  refine ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, fun _ ↦ monotoneOn_const,
    fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · simp [Finance.simpleHolding_def, hε.ne']
  · simp [Finance.simpleGains_def, hε.ne']

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem mono_filtration {𝒢 : Filtration ℝ≥0 mΩ} (hℱ𝒢 : ℱ ≤ 𝒢)
    (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral 𝒢 P W H I where
  isStronglyPredictable := hI.isStronglyPredictable.mono (Filtration.predictable_mono hℱ𝒢)
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, fun m j hj ↦ (ha m j hj).mono (hℱ𝒢 (τ m j)), hE, hG⟩

/-- Indistinguishable replacements preserve `IsItoIntegral`. -/
theorem of_indist (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hc hω
    exact hc.congr hω
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, ha, hE, hG.congr_right (hIJ.ae_eq_eval t)⟩

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ t, W t =ᵐ[P] B t) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, hE, hG.congr_left fun m ↦ ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ j ∈ range (n m + 1), W (min (τ m j) t) ω = B (min (τ m j) t) ω :=
      (ae_ball_iff (Finset.countable_toSet _)).2 fun j _ ↦ hWB _
    filter_upwards [hall] with ω hω
    exact Finance.simpleGains_congr_price ω fun j hj ↦ hω j (mem_range.2 (Nat.lt_succ_of_le hj))

/-- Replacing the integrand by a predictable representative that agrees almost everywhere in time
on almost every path preserves `IsItoIntegral`. -/
theorem congr_ae (hI : IsItoIntegral ℱ P W H I) (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ K s ω)) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hE ε hε).congr' ?_, hG⟩
    refine .of_forall fun m ↦ measure_congr ?_
    filter_upwards [hHK t] with ω hω
    have heq : (∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - K s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      refine lintegral_congr_ae ?_
      filter_upwards [hω] with s hs
      rw [hs]
    simp [heq]

/-- Under an `SFinite` sample measure, replacing the integrand by a predictable representative that
agrees `(timeMeasure T).prod P`-almost everywhere on every finite horizon preserves
`IsItoIntegral`. -/
theorem congr_ae_prod [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry K) :
    IsItoIntegral ℱ P W K I := by
  refine hI.congr_ae hK fun T ↦ ?_
  exact Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := P) (ν := Probability.timeMeasure T))
      |>.quasiMeasurePreserving.ae_eq_comp (hHK T))

/-- The elementary gains of a left-measurable simple holding form an Itô integral of that holding
whenever the integrator has almost surely continuous paths. -/
theorem simpleGains {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := hW.mono fun _ hω ↦ hω.simpleGains
  exists_seq_approx t := by
    refine ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha,
      fun ε hε ↦ by simp [hε.ne'], fun ε hε ↦ by simp [hε.ne']⟩

/-- For any initial-measurable random variable `ξ` and integrator with almost surely continuous
paths, `fun t ω ↦ ξ ω * (W t ω - W 0 ω)` is an Itô integral of the time-constant integrand
`fun _ ω ↦ ξ ω`. -/
theorem const (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * (W t ω - W 0 ω)) where
  isStronglyPredictable := StronglyAdapted.isStronglyPredictable_of_continuous
    (fun _ ↦ hξ.mono (ℱ.mono bot_le)) fun _ ↦ continuous_const
  ae_continuous := hW.mono fun _ hω ↦ continuous_const.mul (hω.sub continuous_const)
  exists_seq_approx t := by
    let τ (k : ℕ) : ℝ≥0 := if k = 0 then 0 else t
    have hτ : MonotoneOn τ (Iic 1) := fun i _ j _ hij ↦ by
      by_cases hi : i = 0
      · simp [τ, hi]
      · have hj : j ≠ 0 := by omega
        simp [τ, hi, hj]
    have ha : ∀ j < 1, StronglyMeasurable[ℱ (τ j)] ξ := fun j hj ↦ by
      obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
      simpa [τ] using hξ
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ _ ↦ ξ, fun _ ↦ hτ, fun _ ↦ ha,
      fun ε hε ↦ tendsto_const_nhds.congr fun _ ↦ ?_,
      fun ε hε ↦ tendsto_const_nhds.congr fun _ ↦ ?_⟩
    · have hzero (ω : Ω) : (∫⁻ s, ‖Finance.simpleHolding τ 1 (fun _ ↦ ξ) s ω - ξ ω‖ₑ ^ 2
          ∂Probability.timeMeasure t) = 0 := by
        refine (lintegral_congr_ae ?_).trans lintegral_zero
        filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
        simp [Finance.simpleHolding_def, τ, indicator_of_mem hs]
      simp [hzero, hε.ne']
    · simp [Finance.simpleGains_def, τ, hε.ne']

/-- For an integrator with almost surely continuous paths vanishing almost surely at time zero,
`W` is an Itô integral of the unit integrand `1`. -/
theorem one (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hW₀ : W 0 =ᵐ[P] 0) :
    IsItoIntegral ℱ P W 1 W := by
  refine (const hW (ξ := fun _ ↦ 1) stronglyMeasurable_const).of_indist ?_
  filter_upwards [hW₀] with ω hω₀ t
  simp [hω₀]

/-- Scaling an integrand scales its Itô integral. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) := by
  refine ⟨hI.isStronglyPredictable.const_mul c,
    hI.ae_continuous.mono fun ω hω ↦ continuous_const.mul hω, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
  refine ⟨n, τ, fun m ↦ c • a m, hτ, fun m j hj ↦ (ha m j hj).const_smul c, fun ε hε ↦ ?_, ?_⟩
  · have hctop : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
    refine (tendsto_measure_ge_zero_const_mul hctop hE hε).congr' (.of_forall fun m ↦ ?_)
    congr 1
    ext ω
    simp only [mem_ofPred_eq, Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ hctop]
  · exact (hG.const_smul c).congr_left fun m ↦ .of_forall fun ω ↦
      (Finance.simpleGains_smul (τ m) (n m) c (a m) W t ω).symm

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W (-H) (-I) := by
  simpa only [neg_one_mul, Pi.neg_def] using hI.const_mul (-1)

/-- Negating both the integrand and the integral process preserves `IsItoIntegral`. -/
@[simp]
theorem neg_iff : IsItoIntegral ℱ P W (-H) (-I) ↔ IsItoIntegral ℱ P W H I :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

/-- The sum of two Itô integrals is an Itô integral of the sum of their integrands. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H + K) (I + J) := by
  refine ⟨hI.isStronglyPredictable.add hJ.isStronglyPredictable, ?_, fun t ↦ ?_⟩
  · filter_upwards [hI.ae_continuous, hJ.ae_continuous] with ω hIω hJω
    exact hIω.add hJω
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hG₁⟩ := hI.exists_seq_approx t
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hJ.exists_seq_approx t
  have href (m : ℕ) := Finance.exists_simpleHolding_simpleGains_sub ℱ t (a₂ := -(a₂ m)) (hτ₁ m)
    (ha₁ m) (hτ₂ m) (fun j hj ↦ (ha₂ m j hj).neg)
  choose N grid height _ hgrid hgrid_le hheight _ hhold hgains using href
  refine ⟨N, grid, height, hgrid, hheight, fun ε hε ↦ ?_, ?_⟩
  · have hle (m : ℕ) (ω : Ω) :
        ∫⁻ s, ‖Finance.simpleHolding (grid m) (N m) (height m) s ω - (H + K) s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t ≤
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t +
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      have hm₁ : Measurable (fun s ↦
          ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2) :=
        (((Finance.isStronglyPredictable_simpleHolding (ha₁ m)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
          |>.comp measurable_prodMk_right
      have heq : (∫⁻ s, ‖Finance.simpleHolding (grid m) (N m) (height m) s ω - (H + K) s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t) =
          ∫⁻ s, ‖(Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω) -
            (K s ω - Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
        refine lintegral_congr_ae ?_
        filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
        rw [hhold m s hs.2 ω, Finance.simpleHolding_neg]
        simp only [Pi.add_apply]
        ring_nf
      rw [heq]
      have hbound := lintegral_enorm_sq_sub_le_two_mul (μ := Probability.timeMeasure t)
        (fun s ↦ Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω)
        (fun s ↦ K s ω - Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)
        (fun _ ↦ 0) (by simpa only [sub_zero] using hm₁.aemeasurable)
      simpa only [sub_zero, eNorm_sub_rev (K _ ω)] using hbound
    exact tendsto_measure_ge_zero_of_ae_le
      (fun _ hδ ↦ tendsto_measure_ge_zero_const_mul (by norm_num) hE₁ hδ)
      (fun _ hδ ↦ tendsto_measure_ge_zero_const_mul (by norm_num) hE₂ hδ)
      (.of_forall fun m ↦ .of_forall (hle m)) hε
  · refine (hG₁.add hG₂).congr_left fun m ↦ .of_forall fun ω ↦ ?_
    have hsum := Finance.simpleGains_apply_eq_sum (a := height m) (hgrid m) le_rfl W ω
    have hge := Finance.simpleGains_of_ge (a := height m) (hgrid m) (hgrid_le m (N m) le_rfl) W ω
    rw [hge, hsum, hgains m W ω, Finance.simpleGains_neg, sub_neg_eq_add]

/-- The difference of two Itô integrals is an Itô integral of the difference of their
integrands. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-- **Sequential closure of the Itô integral.** If a sequence of Itô integrals `(H_seq k, U_seq k)`
approximates a predictable integrand `H` in pathwise square energy in probability on every finite
horizon and `U_seq k t` converges in probability to `I t` at each horizon for an almost surely
continuous process `I`, then `I` is an Itô integral of `H`. -/
theorem of_seq {H_seq : ℕ → ℝ≥0 → Ω → ℝ} {U_seq : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    (hI : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hU : ∀ k, IsItoIntegral ℱ P W (H_seq k) (U_seq k))
    (hE : ∀ t : ℝ≥0, ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖H_seq k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hG : ∀ t : ℝ≥0, TendstoInMeasure P (fun k ↦ U_seq k t) atTop (I t)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hI, fun t ↦ ?_⟩
  let δ (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ k
  have hδ_pos (k : ℕ) : 0 < δ k := ENNReal.pow_pos (by simp) k
  have hδ_lim : Tendsto δ atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hstep (k : ℕ) : ∃ (N : ℕ) (grid : ℕ → ℝ≥0) (height : ℕ → Ω → ℝ),
      MonotoneOn grid (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (grid j)] (height j)) ∧
      P {ω | δ k ≤ ∫⁻ s, ‖Finance.simpleHolding grid N height s ω - H_seq k s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t} ≤ δ k ∧
      P {ω | (2⁻¹ ^ k : ℝ) ≤ ‖Finance.simpleGains grid N height W t ω - U_seq k t ω‖} ≤ δ k := by
    obtain ⟨n, τ, a, hτ, ha, hEk, hGk⟩ := (hU k).exists_seq_approx t
    have hev₁ := (hEk (δ k) (hδ_pos k)).eventually (eventually_lt_nhds (hδ_pos k))
    have hev₂ := ((tendstoInMeasure_iff_norm.1 hGk) (2⁻¹ ^ k) (by positivity)).eventually
      (eventually_lt_nhds (hδ_pos k))
    obtain ⟨m, hm₁, hm₂⟩ := (hev₁.and hev₂).exists
    exact ⟨n m, τ m, a m, hτ m, ha m, hm₁.le, hm₂.le⟩
  choose N grid height hgrid hheight hE_diag hG_diag using hstep
  have hE₁ (ε : ℝ≥0∞) (hε : 0 < ε) : Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (grid k) (N k) (height k) s ω - H_seq k s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ_lim
      (.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hδ_lim.eventually (eventually_lt_nhds hε)] with k hk
    exact (measure_mono fun ω hω ↦ hk.le.trans hω).trans (hE_diag k)
  refine ⟨N, grid, height, hgrid, hheight, fun ε hε ↦ ?_, ?_⟩
  · refine tendsto_measure_ge_zero_of_ae_le
      (fun _ hδ ↦ tendsto_measure_ge_zero_const_mul (c := 2) ENNReal.ofNat_ne_top hE₁ hδ)
      (fun _ hδ ↦ tendsto_measure_ge_zero_const_mul (c := 2) ENNReal.ofNat_ne_top (hE t) hδ)
      (.of_forall fun k ↦ .of_forall fun ω ↦ ?_) hε
    have hbound := lintegral_enorm_sq_sub_le_two_mul (μ := Probability.timeMeasure t)
      (fun s ↦ Finance.simpleHolding (grid k) (N k) (height k) s ω)
      (fun s ↦ H s ω) (fun s ↦ H_seq k s ω)
      ((((Finance.isStronglyPredictable_simpleHolding (hheight k)).sub
        (hU k).isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
        |>.comp measurable_prodMk_right).aemeasurable
    simpa only [eNorm_sub_rev (H _ ω)] using hbound
  · have hG₁ : TendstoInMeasure P
        (fun k ω ↦ Finance.simpleGains (grid k) (N k) (height k) W t ω - U_seq k t ω)
        atTop (fun _ ↦ 0) := by
      refine tendstoInMeasure_of_tendsto_measure_rate_lt_dist
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num) :
          Tendsto (fun k : ℕ ↦ (2⁻¹ ^ k : ℝ)) atTop (𝓝 0)) ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ_lim
        (fun _ ↦ zero_le) fun k ↦ ?_
      exact (measure_mono fun ω hω ↦ by
        rw [mem_ofPred_eq, dist_zero_right] at hω
        exact hω.le).trans (hG_diag k)
    simpa only [sub_add_cancel, zero_add] using hG₁.add (hG t)

private theorem elementaryEnergy_sub_le
    {n₁ n₂ N : ℕ} {τ₁ τ₂ grid : ℕ → ℝ≥0} {a₁ a₂ height : ℕ → Ω → ℝ} {t : ℝ≥0}
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (hH : IsStronglyPredictable ℱ H)
    (hgrid : MonotoneOn grid (Iic N)) (hgrid_le : ∀ j ≤ N, grid j ≤ t)
    (hhold : ∀ s ≤ t, ∀ ω, Finance.simpleHolding grid N height s ω =
      Finance.simpleHolding τ₁ n₁ a₁ s ω - Finance.simpleHolding τ₂ n₂ a₂ s ω)
    (ω : Ω) :
    ENNReal.ofReal (Probability.elementaryEnergy grid height N ω) ≤
      2 * ∫⁻ s, ‖Finance.simpleHolding τ₁ n₁ a₁ s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t +
      2 * ∫⁻ s, ‖Finance.simpleHolding τ₂ n₂ a₂ s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
  rw [← Probability.lintegral_enorm_sq_simpleHolding_eq_ofReal_elementaryEnergy hgrid
    (hgrid_le N le_rfl) ω]
  have heq : (∫⁻ s, ‖Finance.simpleHolding grid N height s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) =
      ∫⁻ s, ‖Finance.simpleHolding τ₁ n₁ a₁ s ω - Finance.simpleHolding τ₂ n₂ a₂ s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t := by
    refine lintegral_congr_ae ?_
    filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
    rw [hhold s hs.2 ω]
  rw [heq]
  exact lintegral_enorm_sq_sub_le_two_mul (μ := Probability.timeMeasure t)
    (fun s ↦ Finance.simpleHolding τ₁ n₁ a₁ s ω)
    (fun s ↦ Finance.simpleHolding τ₂ n₂ a₂ s ω)
    (fun s ↦ H s ω)
    ((((Finance.isStronglyPredictable_simpleHolding ha₁).sub hH).mono
      ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
      |>.comp measurable_prodMk_right).aemeasurable

/-- Against a filtered pre-Brownian motion, **every** family of left-measurable simple holdings
whose pathwise square-energy error on `(0, t]` tends to zero in probability along a filter `l` has
elementary gains at `t` converging in probability along `l` to `I t`. Path continuity of `W` is not
needed. -/
theorem tendstoInMeasure_simpleGains (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {ι : Type*} {l : Filter ι} {t : ℝ≥0}
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ↦ Finance.simpleGains (τ i) (n i) (a i) W t) l (I t) := by
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hI.exists_seq_approx t
  have href (p : ι × ℕ) := Finance.exists_simpleHolding_simpleGains_sub ℱ t
    (hτ p.1) (ha p.1) (hτ₂ p.2) (ha₂ p.2)
  choose N grid height _ hgrid hgrid_le hheight _ hhold hgains using href
  let lp : Filter (ι × ℕ) := l ×ˢ (atTop : Filter ℕ)
  have henergy : TendstoInMeasure P
      (fun p : ι × ℕ ↦ Probability.elementaryEnergy (grid p) (height p) (N p)) lp
      (fun _ ↦ 0) := by
    refine tendstoInMeasure_iff_norm.2 fun δ hδ ↦ ?_
    have htail := tendsto_measure_ge_zero_of_ae_le
      (fun ε hε ↦ (tendsto_measure_ge_zero_const_mul (by norm_num) hE hε).comp tendsto_fst)
      (fun ε hε ↦ (tendsto_measure_ge_zero_const_mul (by norm_num) hE₂ hε).comp tendsto_snd)
      (.of_forall fun p ↦ .of_forall <| elementaryEnergy_sub_le
        (ha p.1) hI.isStronglyPredictable (hgrid p) (hgrid_le p) (hhold p))
      (ENNReal.ofReal_pos.2 hδ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ ↦ zero_le) fun p ↦ measure_mono fun ω hω ↦ ?_
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (Probability.elementaryEnergy_nonneg (hgrid p) ω)] at hω ⊢
    exact ENNReal.ofReal_le_ofReal hω
  have hdiff := (hW.tendstoInMeasure_sum_mul_sub_of_energy hgrid hheight henergy).congr_left
    fun p ↦ .of_forall (hgains p W)
  have hG₂' : TendstoInMeasure P
      (fun p : ι × ℕ ↦ Finance.simpleGains (τ₂ p.2) (n₂ p.2) (a₂ p.2) W t) lp (I t) :=
    fun ε hε ↦ (hG₂ ε hε).comp tendsto_snd
  have hprod : TendstoInMeasure P
      (fun p : ι × ℕ ↦ Finance.simpleGains (τ p.1) (n p.1) (a p.1) W t) lp (I t) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hG₂'
  intro ε hε
  rw [← Filter.map_fst_prod l (atTop : Filter ℕ), tendsto_map'_iff]
  exact hprod ε hε

/-- Against a filtered pre-Brownian motion, elementary holdings whose pathwise square-energy error
on `(0, T]` tends to zero in probability along `l` have elementary gains converging in probability
at **every** earlier horizon `v ≤ T` to `I v`. -/
theorem tendstoInMeasure_simpleGains_of_le (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {ι : Type*} {l : Filter ι} {v T : ℝ≥0} (hv : v ≤ T)
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure T}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ↦ Finance.simpleGains (τ i) (n i) (a i) W v) l (I v) := by
  have hmeas : Probability.timeMeasure v ≤ Probability.timeMeasure T := by
    rw [← min_eq_left hv, ← Probability.timeMeasure_restrict]
    exact Measure.restrict_le_self
  refine hI.tendstoInMeasure_simpleGains hW hτ ha fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE ε hε)
      (fun _ ↦ zero_le) fun i ↦ measure_mono fun ω hω ↦ hω.trans (lintegral_mono' hmeas le_rfl)

/-- **Predictable `ℱ s`-multiplier rule on `(s, ∞)`.** Against a filtered pre-Brownian motion,
multiplying an integrand `H` on `(s, ∞)` by an `ℱ s`-measurable random variable `ξ` yields the Itô
integral `t ↦ ξ * (I t - I (min s t))`. Neither path continuity of `W` nor any moment or
boundedness hypothesis on `ξ` is required. -/
theorem ite_lt_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if s < t then ξ ω * H t ω else 0)
      (fun t ω ↦ ξ ω * (I t ω - I (min s t) ω)) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hξ_pred : IsStronglyPredictable ℱ (fun t ω ↦ if s < t then ξ ω else 0) := by
    refine Measurable.stronglyMeasurable fun B hB ↦ ?_
    by_cases h0 : (0 : ℝ) ∈ B
    · have hpre : Function.uncurry (fun t ω ↦ if s < t then ξ ω else 0) ⁻¹' B =
          (Ioi s ×ˢ univ)ᶜ ∪ (Ioi s ×ˢ (ξ ⁻¹' B)) := by
        ext ⟨u, ω⟩
        by_cases hu : s < u <;> simp [hu, h0]
      rw [hpre]
      exact (measurableSet_predictable_Ioi_prod MeasurableSet.univ).compl.union
        (measurableSet_predictable_Ioi_prod (hξ.measurable hB))
    · have hpre : Function.uncurry (fun t ω ↦ if s < t then ξ ω else 0) ⁻¹' B =
          Ioi s ×ˢ (ξ ⁻¹' B) := by
        ext ⟨u, ω⟩
        by_cases hu : s < u <;> simp [hu, h0]
      rw [hpre]
      exact measurableSet_predictable_Ioi_prod (hξ.measurable hB)
  have hH_pred : IsStronglyPredictable ℱ (fun t ω ↦ if s < t then ξ ω * H t ω else 0) := by
    convert hξ_pred.mul hI.isStronglyPredictable using 2 with t ω
    split_ifs <;> simp
  refine ⟨hH_pred,
    hI.ae_continuous.mono fun ω hc ↦
      continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id))),
    fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
  let τ' (m j : ℕ) : ℝ≥0 := max s (τ m j)
  let a' (m j : ℕ) (ω : Ω) : ℝ := ξ ω * a m j ω
  have hτ' (m : ℕ) : MonotoneOn (τ' m) (Iic (n m)) :=
    fun i hi j hj hij ↦ max_le_max_left s (hτ m hi hj hij)
  have ha' (m j : ℕ) (hj : j < n m) : StronglyMeasurable[ℱ (τ' m j)] (a' m j) :=
    (hξ.mono (ℱ.mono (le_max_left s (τ m j)))).mul
      ((ha m j hj).mono (ℱ.mono (le_max_right s (τ m j))))
  have hhold (m : ℕ) (u : ℝ≥0) (ω : Ω) :
      Finance.simpleHolding (τ' m) (n m) (a' m) u ω =
        if s < u then ξ ω * Finance.simpleHolding (τ m) (n m) (a m) u ω else 0 := by
    rw [Finance.simpleHolding_def, Finance.simpleHolding_def]
    by_cases hu : s < u
    · simp only [hu, ↓reduceIte, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      have hmem : u ∈ Set.Ioc (τ' m j) (τ' m (j + 1)) ↔ u ∈ Set.Ioc (τ m j) (τ m (j + 1)) := by
        simp only [τ', Set.mem_Ioc, max_lt_iff, le_max_iff, hu, true_and, hu.not_ge, false_or]
      by_cases hj : u ∈ Set.Ioc (τ m j) (τ m (j + 1)) <;> simp [hmem, hj, a']
    · simp only [hu, ↓reduceIte]
      exact sum_eq_zero fun j _ ↦ indicator_of_notMem
        (fun (h : u ∈ Set.Ioc _ _) ↦ hu ((le_max_left s (τ m j)).trans_lt h.1)) _
  refine ⟨n, τ', a', hτ', ha', fun ε hε ↦ ?_, ?_⟩
  · have hξ_meas : AEMeasurable (fun ω ↦ ‖ξ ω‖ₑ ^ 2) P :=
      (hξ.mono (ℱ.le s)).aemeasurable.eNorm.pow_const 2
    have hmul := tendsto_measure_ge_zero_mul_of_ae_lt_top hξ_meas
      (.of_forall fun _ ↦ ENNReal.pow_lt_top eNorm_lt_top) hE hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
      (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω (hω : ε ≤ _) ↦ show ε ≤ _ from hω.trans ?_
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)]
    refine lintegral_mono fun u ↦ ?_
    rw [hhold m u ω]
    by_cases hu : s < u
    · simp only [hu, ↓reduceIte, ← mul_sub, eNorm_mul, mul_pow]
      exact le_rfl
    · simp [hu]
  · have hGs := hI.tendstoInMeasure_simpleGains_of_le hW (min_le_right s t) hτ ha hE
    have hsmul : TendstoInMeasure P
        (fun m ω ↦ ξ ω * (Finance.simpleGains (τ m) (n m) (a m) W t ω -
          Finance.simpleGains (τ m) (n m) (a m) W (min s t) ω))
        atTop (fun ω ↦ ξ ω * (I t ω - I (min s t) ω)) :=
      (hξ.mono (ℱ.le s)).aestronglyMeasurable.tendstoInMeasure_smul (hG.sub hGs)
    refine hsmul.congr_left fun m ↦ .of_forall fun ω ↦ ?_
    rw [Finance.simpleGains_def, Finance.simpleGains_def, Finance.simpleGains_def,
      ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    have hle : τ m j ≤ τ m (j + 1) :=
      hτ m (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j)
    have hinc : W (min (τ' m (j + 1)) t) ω - W (min (τ' m j) t) ω =
        (W (min (τ m (j + 1)) t) ω - W (min (τ m j) t) ω) -
          (W (min (τ m (j + 1)) (min s t)) ω - W (min (τ m j) (min s t)) ω) := by
      dsimp only [τ']
      rcases le_total t s with hts | hst
      · rw [min_eq_right hts, min_eq_right (hts.trans (le_max_left _ _)),
          min_eq_right (hts.trans (le_max_left _ _)), sub_self, sub_self]
      · rw [min_eq_left hst]
        rcases le_total (τ m (j + 1)) s with hys | hsy
        · have hxs : τ m j ≤ s := hle.trans hys
          rw [max_eq_left hys, max_eq_left hxs, min_eq_left hst, sub_self,
            min_eq_left (hys.trans hst), min_eq_left (hxs.trans hst),
            min_eq_left hys, min_eq_left hxs, sub_self]
        · rcases le_total (τ m j) s with hxs | hsx
          · rw [max_eq_right hsy, max_eq_left hxs, min_eq_left hst,
              min_eq_left (hxs.trans hst), min_eq_right hsy, min_eq_left hxs]
            ring
          · rw [max_eq_right hsy, max_eq_right hsx, min_eq_right hsy, min_eq_right hsx,
              sub_self, sub_zero]
    rw [hinc]
    dsimp only [a']
    ring

/-- Every Itô integral against a filtered pre-Brownian motion vanishes almost surely at time
zero. -/
theorem eval_zero_ae_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  have h0 : TendstoInMeasure P
      (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ _ ↦ 0) W 0) atTop (I 0) := by
    refine hI.tendstoInMeasure_simpleGains hW (fun _ ↦ monotoneOn_const)
      (fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim) fun ε hε ↦ ?_
    simp [Probability.timeMeasure_zero, hε.ne']
  have hconst : TendstoInMeasure P
      (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ _ ↦ 0) W 0) atTop (0 : Ω → ℝ) :=
    fun ε hε ↦ by simp [Finance.simpleGains_def, hε.ne']
  exact tendstoInMeasure_ae_unique h0 hconst

/-- **Uniqueness of the Itô integral.** Against a filtered pre-Brownian motion, any two Itô
integrals of the same integrand are indistinguishable. -/
theorem indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J := by
  have hmod (t : ℝ≥0) : I t =ᵐ[P] J t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hJ.exists_seq_approx t
    exact tendstoInMeasure_ae_unique (hI.tendstoInMeasure_simpleGains hW hτ ha hE) hG
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ℝ≥0
  filter_upwards [hI.ae_continuous, hJ.ae_continuous, (ae_ball_iff hDc).2 fun q _ ↦ hmod q]
    with ω hIω hJω hDω t
  exact EqOn.closure hDω hIω hJω (hDd t)

/-- **Filtration invariance of the Itô integral.** If `ℱ ≤ 𝒢` and `W` remains a filtered
pre-Brownian motion on `𝒢` (for instance when `𝒢` is the augmented filtration), any Itô integral of
`H` on `ℱ` is indistinguishable from any Itô integral of `H` on `𝒢`. -/
theorem indist_of_le {𝒢 : Filtration ℝ≥0 mΩ}
    (hW : Probability.IsFilteredPreBrownianReal 𝒢 W P) (hℱ𝒢 : ℱ ≤ 𝒢)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral 𝒢 P W H J) :
    I ≡ᵐ[P] J :=
  (hI.mono_filtration hℱ𝒢).indist hW hJ

/-- Against a filtered pre-Brownian motion, two Itô integrals whose integrands agree almost
everywhere in time on almost every path are indistinguishable. -/
theorem indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ K s ω)) :
    I ≡ᵐ[P] J :=
  (hI.congr_ae hJ.isStronglyPredictable hHK).indist hW hJ

/-- **Product-almost-everywhere congruence of Itô integrals.** Against a filtered pre-Brownian
motion, Itô integrals of integrands agreeing `(timeMeasure T).prod P`-almost everywhere on every
finite horizon are indistinguishable. -/
theorem indist_of_ae_eq_prod (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry K) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (hI.congr_ae_prod hJ.isStronglyPredictable hHK).indist hW hJ

end IsItoIntegral

/-- Against a filtered pre-Brownian motion with almost surely continuous paths, `W` itself is an
Itô integral of the unit integrand `1`. -/
theorem Probability.IsFilteredPreBrownianReal.isItoIntegral_one
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) :
    IsItoIntegral ℱ P W 1 W :=
  IsItoIntegral.one hcont hW.toIsPreBrownianReal.eval_zero_ae_eq_zero

end TauCeti
