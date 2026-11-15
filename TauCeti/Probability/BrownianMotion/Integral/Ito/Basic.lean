/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE

/-!
# The continuous time-indexed Brownian Itô integral: specification, algebra, and uniqueness

`TauCeti.IsItoIntegral ℱ P W H I` specifies when a real-valued process `I` is a continuous
time-indexed Itô stochastic integral of a predictable integrand `H` against `W` under `P`:
`H` is predictable for `ℱ`, `I` has `P`-almost-surely continuous sample paths, and at every
horizon `t` there exist bounded, left-measurable simple strategies whose holdings converge to `H`
in pathwise square energy on `(0, t]` in probability while their elementary gains against `W` at
`t` converge to `I t` in probability.

This relational specification uses `TauCeti.Finance.simpleHolding` and
`TauCeti.Finance.simpleGains` directly on a raw filtration without completeness, right continuity,
or moment assumptions on `H`. Pathwise square energy is measured by the `ℝ≥0∞`-valued lower
Lebesgue integral against `TauCeti.Probability.timeMeasure t`, so infinite-energy paths are never
conflated with zero energy.

## Main definitions and results

* `TauCeti.IsItoIntegral`: relational specification of a continuous Brownian Itô integral process.
* `TauCeti.IsItoIntegral.simpleHolding`, `indicator_Ioc`, `const_sub_initial`, `const`: elementary
  holdings, predictable interval indicators, and constant integrands have explicit continuous Itô
  integrals when `W` has almost-surely continuous paths.
* `TauCeti.IsItoIntegral.add`, `sub`, `neg`, `const_mul`, `smul`: linearity of `IsItoIntegral`.
* `TauCeti.IsItoIntegral.indist`: uniqueness up to `P`-indistinguishability for any filtered
  pre-Brownian integrator, requiring no path-continuity assumption on `W`.
* `TauCeti.IsItoIntegral.congr_integrand`, `indist_of_ae_eq`: invariance and indistinguishability
  under `(dt × P)`-almost-everywhere integrand equality on each finite horizon.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W B H K I J : ℝ≥0 → Ω → ℝ}

/-- `IsItoIntegral ℱ P W H I` means that `I` is a continuous time-indexed Brownian Itô integral
of the predictable integrand `H` against `W` under `P`: `H` is literally predictable for `ℱ`,
`I` has `P`-almost-surely continuous paths, and at each horizon `t` there exist bounded,
left-measurable simple strategies whose holdings converge to `H` in pathwise square energy on
`(0, t]` in probability while their elementary gains against `W` at `t` converge to `I t` in
probability. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- The integral process has `P`-almost-surely continuous sample paths. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At every horizon `t`, bounded left-measurable simple strategies approximate `H` in pathwise
  square energy in probability on `(0, t]` while their elementary gains approximate `I t` in
  probability. -/
  exists_seq_approx : ∀ t : ℝ≥0,
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i)) ∧
      (∀ k i, i < n k → ∃ C : ℝ, ∀ ω, ‖a k i ω‖ ≤ C) ∧
      (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
      TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-- Unfolding characterization of `IsItoIntegral`. -/
theorem isItoIntegral_iff :
    IsItoIntegral ℱ P W H I ↔
      IsStronglyPredictable ℱ H ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
        (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
        (∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i)) ∧
        (∀ k i, i < n k → ∃ C : ℝ, ∀ ω, ‖a k i ω‖ ≤ C) ∧
        (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
          ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
        TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

namespace IsItoIntegral

/-! ### Congruence and initial value -/

/-- Replacing an Itô integral by an indistinguishable process preserves `IsItoIntegral`. -/
theorem of_indist (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hω heq
    exact hω.congr fun t ↦ heq t
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, ha, hb, henergy, hgains.congr_right (hIJ.ae_eq_eval t)⟩

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ s, W s =ᵐ[P] B s) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, hb, henergy, hgains.congr_left fun k ↦ ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ j ≤ n k, W (min (τ k j) t) ω = B (min (τ k j) t) ω :=
      (ae_ball_iff (finite_Iic (n k)).countable).2 fun j _ ↦ hWB (min (τ k j) t)
    filter_upwards [hall] with ω hω
    exact Finance.simpleGains_congr_price ω hω

/-- Replacing the integrand by a predictable process agreeing `(dt × P)`-almost everywhere on
every finite horizon preserves `IsItoIntegral`. -/
theorem congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P]
      Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    have hswap : (fun p : Ω × ℝ≥0 ↦ H p.2 p.1) =ᵐ[P.prod (Probability.timeMeasure t)]
        fun p : Ω × ℝ≥0 ↦ K p.2 p.1 :=
      (Measure.measurePreserving_swap (μ := P)
        (ν := Probability.timeMeasure t)).quasiMeasurePreserving.ae_eq_comp (hHK t)
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] fun s ↦ K s ω :=
      Measure.ae_ae_of_ae_prod hswap
    refine ⟨n, τ, a, hτ, ha, hb, fun ε hε ↦ (henergy ε hε).congr fun k ↦ ?_, hgains⟩
    refine measure_congr ?_
    filter_upwards [hsec] with ω hω
    have hlin : (∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      refine lintegral_congr_ae ?_
      filter_upwards [hω] with s hs
      rw [hs]
    simp only [hlin]

/-- Every Itô integral vanishes almost surely at time `0`. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, hτ, -, -, -, hgains⟩ := hI.exists_seq_approx 0
  have hzero (k : ℕ) : Finance.simpleGains (τ k) (n k) (a k) W 0 = 0 := by
    ext ω
    exact Finance.simpleGains_of_le (hτ k) bot_le W ω
  simp_rw [hzero] at hgains
  exact tendstoInMeasure_ae_unique hgains tendstoInMeasure_const

/-! ### Elementary and constant integrands -/

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp]
theorem zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall fun _ ↦ continuous_const
  exists_seq_approx t := by
    refine ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ _ _ _ ↦ le_rfl,
      fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim, fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim,
      fun ε hε ↦ ?_, ?_⟩
    · simp [Finance.simpleHolding_def, hε.not_ge]
    · have hg : (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ ↦ 0) W t) =
          fun _ : ℕ ↦ (0 : Ω → ℝ) := by
        ext
        simp [Finance.simpleGains_def]
      rw [hg]
      exact tendstoInMeasure_const

/-- A bounded left-measurable simple holding has its elementary gains as an Itô integral whenever
`W` has almost-surely continuous paths. -/
theorem simpleHolding {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, ∃ C : ℝ, ∀ ω, ‖a i ω‖ ≤ C) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := by
    filter_upwards [hcont] with ω hω
    simp only [Finance.simpleGains_def]
    fun_prop
  exists_seq_approx t := by
    refine ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha, fun _ ↦ hb,
      fun ε hε ↦ ?_, tendstoInMeasure_const⟩
    simp [sub_self, hε.not_ge]

/-- A bounded `ℱ u`-measurable random variable held on `(u, v]` (with `u ≤ v`) has clipped
increment gains `ξ * (W (v ⊓ t) - W (u ⊓ t))` as its continuous Itô integral. -/
theorem indicator_Ioc {u v : ℝ≥0} {ξ : Ω → ℝ} (huv : u ≤ v)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hξ : StronglyMeasurable[ℱ u] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ ξ ω) t)
      (fun t ω ↦ ξ ω * (W (min v t) ω - W (min u t) ω)) := by
  let τ : ℕ → ℝ≥0 := fun i ↦ if i = 0 then u else v
  have hτ : MonotoneOn τ (Iic 1) := by
    intro i _ j _ hij
    dsimp [τ]
    split_ifs with hi0 hj0 hj0'
    · exact le_rfl
    · exact huv
    · omega
    · exact le_rfl
  have h := simpleHolding (ℱ := ℱ) (P := P) (n := 1) (τ := τ) (a := fun _ ↦ ξ) hcont hτ
    (fun i hi ↦ by obtain rfl : i = 0 := (by omega); exact hξ)
    (fun _ _ ↦ hb)
  have h1 : Finance.simpleHolding τ 1 (fun _ ↦ ξ) =
      fun t ω ↦ (Ioc u v).indicator (fun _ ↦ ξ ω) t := by
    ext t ω
    simp [Finance.simpleHolding_def, τ]
  have h2 : Finance.simpleGains τ 1 (fun _ ↦ ξ) W =
      fun t ω ↦ ξ ω * (W (min v t) ω - W (min u t) ω) := by
    ext t ω
    simp [Finance.simpleGains_def, τ]
  rwa [h1, h2] at h

/-- A constant integrand `c` has `t ↦ c * (W t - W 0)` as a continuous Itô integral whenever `W`
has almost-surely continuous paths, without assuming `W 0 = 0`. -/
theorem const_sub_initial (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (c : ℝ) :
    IsItoIntegral ℱ P W (fun _ _ ↦ c) (fun t ω ↦ c * (W t ω - W 0 ω)) where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := by
    filter_upwards [hcont] with ω hω
    fun_prop
  exists_seq_approx t := by
    let τ : ℕ → ℝ≥0 := fun i ↦ if i = 0 then 0 else t
    have hτ : MonotoneOn τ (Iic 1) := by
      intro i _ j _ hij
      dsimp [τ]
      split_ifs with hi0 hj0
      · exact le_rfl
      · exact bot_le
      · omega
      · exact le_rfl
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ _ _ ↦ c, fun _ ↦ hτ,
      fun _ _ _ ↦ stronglyMeasurable_const,
      fun _ _ _ ↦ ⟨‖c‖, fun _ ↦ le_rfl⟩, fun ε hε ↦ ?_, ?_⟩
    · have hlin (ω : Ω) : (∫⁻ s, ‖Finance.simpleHolding τ 1 (fun _ _ ↦ c) s ω - c‖ₑ ^ 2
          ∂Probability.timeMeasure t) = 0 := by
        rw [Probability.timeMeasure_def]
        refine (lintegral_eq_zero_iff' ?_).2 ?_
        · exact ((Finance.isStronglyPredictable_simpleHolding (ℱ := ℱ)
            (τ := τ) (n := 1) (a := fun _ _ ↦ c) fun _ _ ↦ stronglyMeasurable_const).mono
              ℱ.predictable_le_prod |>.measurable.comp
                (measurable_id.prodMk measurable_const) |>.sub measurable_const).eNorm.pow_const 2
                  |>.aemeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          simp [Finance.simpleHolding_def, τ, hs.1, hs.2]
      simp [hlin, hε.not_ge]
    · have hg : (fun _ : ℕ ↦ Finance.simpleGains τ 1 (fun _ _ ↦ c) W t) =
          fun _ : ℕ ↦ fun ω ↦ c * (W t ω - W 0 ω) := by
        ext _ ω
        simp [Finance.simpleGains_def, τ]
      rw [hg]
      exact tendstoInMeasure_const

/-- When `W` has almost-surely continuous paths and `W 0 = 0` almost surely, a constant integrand
`c` has `t ↦ c * W t` as a continuous Itô integral. -/
theorem const (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hW₀ : W 0 =ᵐ[P] 0) (c : ℝ) :
    IsItoIntegral ℱ P W (fun _ _ ↦ c) (fun t ω ↦ c * W t ω) := by
  refine (const_sub_initial hcont c).of_indist ?_
  filter_upwards [hW₀] with ω hω t
  simp [hω]

/-! ### Linearity -/

private theorem sq_add_le_four_mul (u v : ℝ≥0∞) : (u + v) ^ 2 ≤ 4 * u ^ 2 + 4 * v ^ 2 := by
  rcases le_total u v with huv | hvu
  · calc
      (u + v) ^ 2 ≤ (v + v) ^ 2 := by gcongr
      _ = 4 * v ^ 2 := by ring
      _ ≤ 4 * u ^ 2 + 4 * v ^ 2 := le_add_self
  · calc
      (u + v) ^ 2 ≤ (u + u) ^ 2 := by gcongr
      _ = 4 * u ^ 2 := by ring
      _ ≤ 4 * u ^ 2 + 4 * v ^ 2 := le_self_add

private theorem tendsto_measure_lintegral_ge_of_ne_top {E : ℕ → Ω → ℝ≥0∞}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ → Tendsto (fun k ↦ P {ω | ε ≤ E k ω}) atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤ E k ω}) atTop (𝓝 0) := by
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | htop
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h 1 zero_lt_one ENNReal.one_ne_top) (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ ?_
    exact (le_top : (1 : ℝ≥0∞) ≤ ∞).trans hω
  · exact h ε hε htop

private theorem tendsto_measure_lintegral_add_sub_sq {t : ℝ≥0}
    {L₁ L₂ : ℕ → ℝ≥0 → Ω → ℝ}
    (hL₁ : ∀ k, IsStronglyPredictable ℱ (L₁ k))
    (hH : IsStronglyPredictable ℱ H)
    (he₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L₁ k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (he₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L₂ k s ω - K s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖(L₁ k s ω + L₂ k s ω) - (H s ω + K s ω)‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  refine tendsto_measure_lintegral_ge_of_ne_top fun ε hε htop ↦ ?_
  let δ : ℝ≥0∞ := ↑(ε.toNNReal / 8)
  have hε_coe : (ε.toNNReal : ℝ≥0∞) = ε := ENNReal.coe_toNNReal htop
  have hδ : 0 < δ := by
    dsimp [δ]
    exact ENNReal.coe_pos.mpr (div_pos (ENNReal.toNNReal_pos hε.ne' htop) (by norm_num))
  have h4δ : 4 * δ = ε / 2 := by
    have hnn : (4 : ℝ≥0) * (ε.toNNReal / 8) = ε.toNNReal / 2 := by ring
    calc
      4 * δ = ↑((4 : ℝ≥0) * (ε.toNNReal / 8)) := by simp [δ]
      _ = ↑(ε.toNNReal / 2) := by rw [hnn]
      _ = ε / 2 := by rw [ENNReal.coe_div two_ne_zero, hε_coe, ENNReal.coe_ofNat]
  have hsum : Tendsto (fun k ↦
      P {ω | δ ≤ ∫⁻ s, ‖L₁ k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t} +
      P {ω | δ ≤ ∫⁻ s, ‖L₂ k s ω - K s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    simpa using (he₁ δ hδ).add (he₂ δ hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun k ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  have hm₁ : Measurable (fun s ↦ 4 * ‖L₁ k s ω - H s ω‖ₑ ^ 2) :=
    (((hL₁ k).sub hH).mono ℱ.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2 |>.const_mul 4
  have hbound : (∫⁻ s, ‖(L₁ k s ω + L₂ k s ω) - (H s ω + K s ω)‖ₑ ^ 2
      ∂Probability.timeMeasure t) ≤
      4 * (∫⁻ s, ‖L₁ k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) +
      4 * (∫⁻ s, ‖L₂ k s ω - K s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) := by
    calc
      _ ≤ ∫⁻ s, 4 * ‖L₁ k s ω - H s ω‖ₑ ^ 2 + 4 * ‖L₂ k s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
        refine lintegral_mono fun s ↦ ?_
        have htri : ‖(L₁ k s ω + L₂ k s ω) - (H s ω + K s ω)‖ₑ ≤
            ‖L₁ k s ω - H s ω‖ₑ + ‖L₂ k s ω - K s ω‖ₑ := by
          rw [add_sub_add_comm]
          exact eNorm_add_le _ _
        exact (pow_le_pow_left' htri 2).trans (sq_add_le_four_mul _ _)
      _ = _ := by
        rw [lintegral_add_left hm₁, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
  have hle := hω.trans hbound
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
  have hlt1 : 4 * (∫⁻ s, ‖L₁ k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) < ε / 2 := by
    rw [mul_comm 4, ← h4δ, mul_comm 4]
    exact ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) hnot.1
  have hlt2 : 4 * (∫⁻ s, ‖L₂ k s ω - K s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) < ε / 2 := by
    rw [mul_comm 4, ← h4δ, mul_comm 4]
    exact ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) hnot.2
  exact hle.not_gt ((ENNReal.add_lt_add hlt1 hlt2).trans_eq (ENNReal.add_halves ε))

/-- Scaling an integrand by a constant scales its Itô integral. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul]
    exact zero
  refine ⟨hI.isStronglyPredictable.const_mul c, ?_, fun t ↦ ?_⟩
  · filter_upwards [hI.ae_continuous] with ω hω
    exact continuous_const.mul hω
  · obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, fun k ↦ c • a k, hτ,
      fun k i hi ↦ (ha k i hi).const_smul c,
      fun k i hi ↦ ?_, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hb k i hi
      exact ⟨‖c‖ * C, fun ω ↦ by
        simpa [Pi.smul_apply, norm_mul] using mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg c)⟩
    · refine tendsto_measure_lintegral_ge_of_ne_top fun ε hε _ ↦ ?_
      have hc0 : ‖c‖ₑ ≠ 0 := (eNorm_pos.2 hc).ne'
      have hc2_pos : (0 : ℝ≥0∞) < ‖c‖ₑ ^ 2 := by
        rw [sq]
        exact ENNReal.mul_pos hc0 hc0
      have hc2_top : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
      have hdiv : 0 < ε / ‖c‖ₑ ^ 2 := ENNReal.div_pos hε.ne' hc2_top
      refine (henergy (ε / ‖c‖ₑ ^ 2) hdiv).congr fun k ↦ ?_
      congr 1
      ext ω
      have hscale : (∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (c • a k) s ω - c * H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t) =
          ‖c‖ₑ ^ 2 * ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t := by
        have hpoint (s : ℝ≥0) :
            ‖Finance.simpleHolding (τ k) (n k) (c • a k) s ω - c * H s ω‖ₑ ^ 2 =
              ‖c‖ₑ ^ 2 * ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 := by
          rw [Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
        simp_rw [hpoint]
        exact lintegral_const_mul' _ _ hc2_top
      simp only [Set.mem_ofPred_eq, hscale, ENNReal.div_le_iff_le_mul (Or.inl hc2_pos.ne')
        (Or.inl hc2_top), mul_comm (‖c‖ₑ ^ 2)]
    · refine (hgains.const_smul c).congr (fun k ↦ .of_forall fun ω ↦ ?_) .rfl
      exact (Finance.simpleGains_smul _ _ _ _ _ _ _).symm

/-- Scalar-multiplication form of `IsItoIntegral.const_mul`. -/
theorem smul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (c • H) (c • I) :=
  hI.const_mul c

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (-H) (-I) := by
  simpa [neg_one_smul] using hI.smul (-1 : ℝ)

/-- Adding two integrands adds their Itô integrals. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H + K) (I + J) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hJ.ae_continuous] with ω hIω hJω
    exact hIω.add hJω
  exists_seq_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hb₁, he₁, hg₁⟩ := hI.exists_seq_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hb₂, he₂, hg₂⟩ := hJ.exists_seq_approx t
    choose n τ b _ hτ hbm hbb hhold hgains using fun k ↦
      Finance.exists_simpleHolding_simpleGains_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    refine ⟨n, τ, b, fun k ↦ (hτ k).monotoneOn, hbm, fun k j hj ↦ ?_, ?_, ?_⟩
    · choose C₁ hC₁ using fun (i : Fin (n₁ k)) ↦ hb₁ k i.1 i.2
      choose C₂ hC₂ using fun (i : Fin (n₂ k)) ↦ hb₂ k i.1 i.2
      refine ⟨(∑ i : Fin (n₁ k), C₁ i) + ∑ i : Fin (n₂ k), C₂ i, fun ω ↦
        (hbb k j hj ω).trans (add_le_add ?_ ?_)⟩
      · rw [← Fin.sum_univ_eq_sum_range]
        exact sum_le_sum fun i _ ↦ hC₁ i ω
      · rw [← Fin.sum_univ_eq_sum_range]
        exact sum_le_sum fun i _ ↦ hC₂ i ω
    · simp_rw [hhold, Pi.add_apply]
      exact tendsto_measure_lintegral_add_sub_sq
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha₁ k))
        hI.isStronglyPredictable he₁ he₂
    · exact (hg₁.add hg₂).congr (fun k ↦ .of_forall fun ω ↦ (hgains k W t ω).symm) .rfl

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-! ### Uniqueness and local integrand congruence -/

private theorem ofReal_elementaryEnergy_clip_eq {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n)) (t : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (Probability.elementaryEnergy (fun i ↦ min (τ i) t)
      (fun i ↦ if τ i ≤ t then a i else 0) n ω) =
      ∫⁻ s, ‖Finance.simpleHolding τ n a s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
  rw [Probability.elementaryEnergy_def, Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hτ,
    ENNReal.ofReal_sum_of_nonneg]
  · refine sum_congr rfl fun i _ ↦ ?_
    by_cases hle : τ i ≤ t
    · simp only [hle, ↓reduceIte, min_eq_left hle,
        ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_sq_eq_ofReal_sq]
    · have hgt : (min (τ (i + 1)) t : ℝ) - τ i ≤ 0 :=
        sub_nonpos.mpr (NNReal.coe_le_coe.mpr ((min_le_right _ _).trans (le_of_not_ge hle)))
      simp [hle, ENNReal.ofReal_eq_zero.mpr hgt]
  · intro i hi
    have hi' := mem_range.mp hi
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_min_right t (hτ hi'.le hi' (Nat.le_succ i)))))

private theorem tendstoInMeasure_simpleGains_zero_of_lintegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop 0 := by
  let τ' (k i : ℕ) : ℝ≥0 := min (τ k i) t
  let a' (k i : ℕ) : Ω → ℝ := if τ k i ≤ t then a k i else 0
  have hτ' (k : ℕ) : MonotoneOn (τ' k) (Iic (n k)) :=
    fun _ hi _ hj hij ↦ min_le_min_right t (hτ k hi hj hij)
  have ha' (k i : ℕ) (hi : i < n k) : StronglyMeasurable[ℱ (τ' k i)] (a' k i) := by
    by_cases hle : τ k i ≤ t
    · rw [show τ' k i = τ k i from min_eq_left hle]
      simpa only [a', hle, ↓reduceIte] using ha k i hi
    · rw [show a' k i = fun _ ↦ (0 : ℝ) by ext; simp [a', hle]]
      exact stronglyMeasurable_const
  have he : TendstoInMeasure P (fun k ↦ Probability.elementaryEnergy (τ' k) (a' k) (n k))
      atTop 0 := by
    refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
    refine (henergy (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)).congr fun k ↦ ?_
    congr 1
    ext ω
    have hnn := Probability.elementaryEnergy_nonneg (a := a' k) (hτ' k) ω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [← ofReal_elementaryEnergy_clip_eq (hτ k) t ω]
    exact ENNReal.ofReal_le_ofReal_iff hnn
  have hsum_eq (k : ℕ) (ω : Ω) :
      (∑ i ∈ range (n k), a' k i ω * (W (τ' k (i + 1)) ω - W (τ' k i) ω)) =
        Finance.simpleGains (τ k) (n k) (a k) W t ω := by
    rw [Finance.simpleGains_def]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    by_cases hle : τ k i ≤ t
    · simp [τ', a', hle]
    · have hgt : t ≤ τ k i := le_of_not_ge hle
      simp [τ', a', hle, min_eq_right hgt,
        min_eq_right (hgt.trans (hτ k hi'.le hi' (Nat.le_succ i)))]
  exact (hW.tendstoInMeasure_sum_mul_sub_of_energy hτ' ha' he).congr_left
    fun k ↦ .of_forall (hsum_eq k)

/-- Any Itô integral of the zero integrand against a filtered pre-Brownian motion vanishes almost
surely at each horizon, without assuming path continuity of `W`. -/
theorem ae_eq_zero_of_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) (t : ℝ≥0) : I t =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, hτ, ha, -, henergy, hgains⟩ := hI.exists_seq_approx t
  simp only [Pi.zero_apply, sub_zero] at henergy
  exact tendstoInMeasure_ae_unique hgains
    (tendstoInMeasure_simpleGains_zero_of_lintegral hW hτ ha henergy)

/-- Any Itô integral of the zero integrand against a filtered pre-Brownian motion is
indistinguishable from `0`. -/
theorem indist_zero_of_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) : I ≡ᵐ[P] 0 :=
  ProbabilityTheory.indist_of_ae_continuous hI.ae_continuous
    (Eventually.of_forall fun _ ↦ continuous_const) (hI.ae_eq_zero_of_zero hW)

/-- At any fixed horizon `t`, if a sequence of left-measurable simple strategies approximates `H`
in pathwise square energy in probability on `(0, t]` and its elementary gains converge in
probability to `Y`, then `I t =ᵐ[P] Y`. Neither boundedness of the approximating heights nor a
full continuous process extending `Y` is required. -/
theorem ae_eq_of_approx (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {Y : Ω → ℝ}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hgains : TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop Y) :
    I t =ᵐ[P] Y := by
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, -, he₁, hg₁⟩ := hI.exists_seq_approx t
  choose m σ b _ hσ hbm _ hhold hgains_sub using fun k ↦
    Finance.exists_simpleHolding_simpleGains_sub ℱ (hτ₁ k) (hτ k) (ha₁ k) (ha k)
  have he_neg : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖(-Finance.simpleHolding (τ k) (n k) (a k) s ω) - (-H s ω)‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    simpa only [neg_sub_neg, eNorm_sub_rev] using henergy
  have he_sub : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    have h := tendsto_measure_lintegral_add_sub_sq
      (L₁ := fun k ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k))
      (L₂ := fun k ↦ -Finance.simpleHolding (τ k) (n k) (a k)) (H := H) (K := -H)
      (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha₁ k))
      hI.isStronglyPredictable he₁ he_neg
    simpa only [Pi.neg_apply, add_neg_cancel, sub_zero, ← sub_eq_add_neg, ← hhold] using h
  have hzero := (tendstoInMeasure_simpleGains_zero_of_lintegral hW
    (fun k ↦ (hσ k).monotoneOn) hbm he_sub).congr_left fun k ↦ .of_forall (hgains_sub k W t)
  filter_upwards [tendstoInMeasure_ae_unique (hg₁.sub hgains) hzero] with ω hω
  exact sub_eq_zero.mp hω

/-- Two Itô integrals of the same integrand against a filtered pre-Brownian motion agree almost
surely at each horizon, without assuming path continuity of `W`. -/
theorem ae_eq_eval (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) (t : ℝ≥0) :
    I t =ᵐ[P] J t := by
  obtain ⟨n, τ, a, hτ, ha, -, he, hg⟩ := hJ.exists_seq_approx t
  exact hI.ae_eq_of_approx hW hτ ha he hg

/-- **Uniqueness of the continuous Brownian Itô integral**: any two continuous Itô integrals of the
same predictable integrand against a filtered pre-Brownian motion are `P`-indistinguishable. No
moment bound on `H` and no path-continuity hypothesis on `W` are required. -/
theorem indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J :=
  ProbabilityTheory.indist_of_ae_continuous hI.ae_continuous hJ.ae_continuous (hI.ae_eq_eval hW hJ)

/-- **Integrand congruence for continuous Brownian Itô integrals**: if two predictable integrands
agree `(dt × P)`-almost everywhere on every finite horizon, then any continuous Itô integrals of
them against a filtered pre-Brownian motion are `P`-indistinguishable. -/
theorem indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P]
      Function.uncurry K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (hI.congr_integrand hJ.isStronglyPredictable hHK).indist hW hJ

end IsItoIntegral

end TauCeti

