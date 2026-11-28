/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Associativity
import TauCeti.Probability.Process.Predictable.Basic

/-!
# Simple integrands against Itô integrals

Let `I` be an Itô integral of `H` against a pre-Brownian motion `W` relative to the filtration.
For a simple holding `K` whose heights are known at the left endpoints of their intervals, the
elementary integral of `K` against `I` is an Itô integral of `K H` against `W`:

`∫ K d(∫ H dW) = ∫ K H dW`  (`TauCeti.Probability.IsItoIntegral.simpleGains`).

The heights of `K` need not be bounded or integrable, and `H` need only have an Itô integral;
no moment condition is imposed. The case of a single interval is the **multiplier rule**
(`TauCeti.Probability.IsItoIntegral.mul_sub_min`): for `s ≤ u` and `ξ` measurable at time `s`,
the process `ξ (I_{u ∧ t} - I_{s ∧ t})` is an Itô integral of `1_{(s,u]} ξ H`, which extends to
the post-`s` multiplier rule `TauCeti.Probability.IsItoIntegral.indicator_Ioi_mul` (with
`TauCeti.Probability.IsItoIntegral.indicator_Ioi` as the unit-multiplier special case).

The proof multiplies the simple approximants of `H` by `K` on common grids
(`TauCeti.Finance.exists_simpleHolding_simpleGains_eq_mul`). Their square errors are multiplied
by at most the square of the sum of the absolute heights of `K`, a finite random factor, so they
still vanish in probability (`MeasureTheory.tendsto_measure_le_enorm_mul`). The elementary
integrals of the products are the elementary integrals of `K` against those of the approximants
of `H`, which converge in probability to `I` at every time up to the horizon
(`TauCeti.Probability.IsItoIntegral.tendstoInMeasure_simpleGains_of_le`).

Applied to the martingale part `∫ θ dW` of a price process, these identities express the gains of
a simple trading strategy through the Brownian Itô integral of its position times `θ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition, Springer,
  1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- Multiplying two processes by a simple holding multiplies the square energy of their
difference by at most the square of the sum of the absolute heights. -/
private theorem lintegral_enorm_simpleHolding_mul_sub_le (hτ : MonotoneOn τ (Iic n))
    (f g : ℝ≥0 → Ω → ℝ) (μ : Measure ℝ≥0) (ω : Ω) :
    ∫⁻ s, ‖Finance.simpleHolding τ n a s ω * f s ω -
        Finance.simpleHolding τ n a s ω * g s ω‖ₑ ^ 2 ∂μ ≤
      ‖(∑ j ∈ Finset.range n, ‖a j ω‖) ^ 2‖ₑ * ∫⁻ s, ‖f s ω - g s ω‖ₑ ^ 2 ∂μ := by
  rw [← lintegral_const_mul' _ _ eNorm_ne_top]
  refine lintegral_mono fun s ↦ ?_
  rw [← mul_sub, eNorm_mul, mul_pow, eNorm_pow]
  gcongr
  -- The holding is bounded by the sum of the absolute heights.
  have hsum : 0 ≤ ∑ j ∈ Finset.range n, ‖a j ω‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine eNorm_le_iff_norm_le.mpr ((Finance.norm_simpleHolding_le hτ s ω fun j hj ↦
    Finset.single_le_sum (fun i _ ↦ norm_nonneg (a i ω)) (Finset.mem_range.mpr hj)).trans ?_)
  rw [max_eq_left hsum]
  exact Real.le_norm_self _

/-- **Substitution for simple integrands.** Against a pre-Brownian motion relative to the
filtration, if `I` is an Itô integral of `H`, then the elementary integral of a simple holding
`K` with heights known at the left endpoints of their intervals against `I` is an Itô integral
of `K H`: `∫ K d(∫ H dW) = ∫ K H dW`. The heights need not be bounded or integrable. -/
theorem IsItoIntegral.simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) :
    IsItoIntegral ℱ P W (fun t ω ↦ Finance.simpleHolding τ n a t ω * H t ω)
      (Finance.simpleGains τ n a I) where
  isStronglyPredictable :=
    (Finance.isStronglyPredictable_simpleHolding ha).mul hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous] with ω hω
    exact Finance.continuous_simpleGains hω
  exists_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    obtain ⟨m, σ, b, hσ, hb, hbH, -⟩ := hI.exists_approx t
    -- Multiply each approximant of `H` by `K` on a common grid.
    choose N ρ c _ hρ hc hhold hgain using fun k ↦
      Finance.exists_simpleHolding_simpleGains_eq_mul ℱ (hσ k) hτ (hb k) ha
    refine ⟨N, ρ, c, fun k ↦ (hρ k).monotoneOn, hc, fun ε hε ↦ ?_, ?_⟩
    · -- The square errors are multiplied by a finite random factor.
      have hA : AEStronglyMeasurable (fun ω ↦ (∑ j ∈ Finset.range n, ‖a j ω‖) ^ 2) P :=
        ((Finset.stronglyMeasurable_fun_sum _ fun j hj ↦
          ((ha j (Finset.mem_range.mp hj)).mono (ℱ.le _)).norm).pow 2).aestronglyMeasurable
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_measure_le_enorm_mul hA hbH hε) (fun _ ↦ zero_le)
        fun k ↦ measure_mono fun ω hω ↦ ?_
      simp only [mem_ofPred_eq, hhold] at hω ⊢
      exact hω.trans (lintegral_enorm_simpleHolding_mul_sub_le hτ _ _ _ ω)
    · -- The elementary integrals of `K` against the approximating integrals converge.
      have hconv := TendstoInMeasure.finset_sum (Finset.range n) fun j hj ↦
        (tendstoInMeasure_const (a j)).mul
          ((ha j (Finset.mem_range.mp hj)).mono (ℱ.le _)).aestronglyMeasurable
          ((hI.aestronglyMeasurable hW.adapted _).sub (hI.aestronglyMeasurable hW.adapted _))
          ((hI.tendstoInMeasure_simpleGains_of_le hW (min_le_right (τ (j + 1)) t) hσ hb
            hbH).sub (hI.tendstoInMeasure_simpleGains_of_le hW (min_le_right (τ j) t) hσ hb hbH))
      rw [show Finance.simpleGains τ n a I t = _ from funext (Finance.simpleGains_def τ n a I t)]
      refine hconv.congr_left fun k ↦ ae_of_all _ fun ω ↦ ?_
      rw [hgain, Finance.simpleGains_def]

/-- **Multiplier rule.** Against a pre-Brownian motion relative to the filtration, if `I` is an
Itô integral of `H`, `s ≤ u` and `ξ` is measurable at time `s`, then the process
`ξ (I_{u ∧ t} - I_{s ∧ t})` is an Itô integral of `1_{(s,u]} ξ H`. The variable `ξ` need not
be bounded or integrable. -/
theorem IsItoIntegral.mul_sub_min (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s u : ℝ≥0} (hsu : s ≤ u) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t * H t ω)
      (fun t ω ↦ ξ ω * (I (min u t) ω - I (min s t) ω)) := by
  -- The one-interval grid `s ≤ u` with height `ξ`.
  have hτ : MonotoneOn (fun j : ℕ ↦ if j = 0 then s else u) (Iic 1) := fun i _ j _ hij ↦ by
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj] <;> omega
  have h := hI.simpleGains hW hτ (a := fun _ ↦ ξ) fun j hj ↦ by
    obtain rfl := Nat.lt_one_iff.mp hj
    simpa using hξ
  have hgain : Finance.simpleGains (fun j : ℕ ↦ if j = 0 then s else u) 1 (fun _ ↦ ξ) I =
      fun t ω ↦ ξ ω * (I (min u t) ω - I (min s t) ω) := by
    ext t ω
    simp [Finance.simpleGains_def]
  simpa [Finance.simpleHolding_def, hgain] using h

/-- **Unbounded post-`s` multiplier rule.** Multiplying an integrand after a deterministic time
`s` by an arbitrary `ℱ s`-measurable random variable `ξ` yields `t ↦ ξ * (I t - I (min s t))`.
Neither boundedness nor moment conditions on `ξ`, nor path continuity of `W`, are needed. -/
theorem IsItoIntegral.indicator_Ioi_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (s : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi s).indicator (fun _ ↦ ξ ω) t * H t ω)
      (fun t ω ↦ ξ ω * (I t ω - I (min s t) ω)) := by
  have hpred : IsStronglyPredictable ℱ (fun t ω ↦ (Ioi s).indicator (fun _ ↦ ξ ω) t * H t ω) := by
    convert hI.isStronglyPredictable.indicator_Ioi_mul hξ using 2 with r ω
    by_cases hr : s < r <;> simp [hr]
  refine ⟨hpred, hI.ae_continuous.mono fun _ hω ↦ by fun_prop, fun t ↦ ?_⟩
  obtain ⟨n, τ, b, hτ, hb, he, hg⟩ := (hI.mul_sub_min hW (le_max_left s t) hξ).exists_approx t
  refine ⟨n, τ, b, hτ, hb, fun ε hε ↦ (he ε hε).congr fun k ↦ congrArg (P ·) (Set.ext fun ω ↦ by
    simp only [Set.mem_ofPred_eq]
    have h_ae : (Ioi s).indicator (fun _ ↦ ξ ω) =ᵐ[timeMeasure t]
        (Ioc s (max s t)).indicator (fun _ ↦ ξ ω) :=
      ae_mono (timeMeasure_mono (le_max_right s t))
        (indicator_Ioi_ae_eq_indicator_Ioc_timeMeasure _ s (max s t))
    have h_eq : (∫⁻ r, ‖Finance.simpleHolding (τ k) (n k) (b k) r ω -
        (Ioc s (max s t)).indicator (fun _ ↦ ξ ω) r * H r ω‖ₑ ^ 2 ∂timeMeasure t) =
        ∫⁻ r, ‖Finance.simpleHolding (τ k) (n k) (b k) r ω -
          (Ioi s).indicator (fun _ ↦ ξ ω) r * H r ω‖ₑ ^ 2 ∂timeMeasure t :=
      lintegral_congr_ae (h_ae.mono fun r hr ↦ by dsimp only; rw [← hr])
    rw [h_eq]),
    by simpa only [min_eq_right (le_max_right s t)] using hg⟩

/-- Restricting an integrand to `(u, ∞)` yields the post-`u` Itô integral
`t ↦ I t - I (min u t)`, without assuming path continuity of `W`. -/
theorem IsItoIntegral.indicator_Ioi (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (u : ℝ≥0) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (H · ω) t)
      (fun t ω ↦ I t ω - I (min u t) ω) := by
  convert hI.indicator_Ioi_mul hW u (ξ := fun _ ↦ 1) stronglyMeasurable_const using 1 <;>
    ext t ω
  · by_cases ht : u < t <;> simp [ht]
  · simp

end TauCeti.Probability
