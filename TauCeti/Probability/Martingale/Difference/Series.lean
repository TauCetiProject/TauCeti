/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Martingale.Convergence
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Series of square-integrable martingale differences

A sequence `Y s` of functions with values in a real Banach space is a sequence of martingale
differences for a filtration `ℱ` if each `Y s` is `ℱ (s + 1)`-measurable with
`μ[Y s | ℱ s] = 0`; its partial sums `∑_{s < t} Y s` form a martingale. When the `Y s` are
real-valued and square-integrable they are orthogonal in `L²`, so the second moment of a partial
sum is the sum of the second moments of its terms. If these second moments are summable, the
martingale is bounded in `L²`, hence in `L¹`, and the almost everywhere martingale convergence
theorem shows that the series `∑ Y s` converges almost everywhere.

## Main results

* `TauCeti.MeasureTheory.martingale_sum_range`: the partial sums of martingale differences form
  a martingale.
* `TauCeti.MeasureTheory.integral_sq_sum_range_of_condExp_eq_zero`: the second moment of a
  partial sum of square-integrable martingale differences is the sum of their second moments.
* `TauCeti.MeasureTheory.exists_ae_tendsto_sum_range_of_summable_integral_sq`: if the second
  moments are summable, the series converges almost everywhere.
-/

public section

open MeasureTheory Filter Finset Topology
open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m₀}

/-- A partial sum of a sequence whose `s`-th term is `ℱ (s + 1)`-measurable is measurable at the
time of its last term. -/
theorem stronglyMeasurable_sum_range_of_succ {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] {Y : ℕ → Ω → M} (hY : ∀ s, StronglyMeasurable[ℱ (s + 1)] (Y s)) (t : ℕ) :
    StronglyMeasurable[ℱ t] fun ω ↦ ∑ s ∈ range t, Y s ω :=
  Finset.stronglyMeasurable_fun_sum _ fun s hs ↦
    (hY s).mono (ℱ.mono (Nat.succ_le_of_lt (mem_range.1 hs)))

/-- The partial sums of integrable martingale differences form a martingale. -/
theorem martingale_sum_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] {Y : ℕ → Ω → E}
    (hY : ∀ s, StronglyMeasurable[ℱ (s + 1)] (Y s)) (hint : ∀ s, Integrable (Y s) μ)
    (hc : ∀ s, μ[Y s | ℱ s] =ᵐ[μ] 0) :
    Martingale (fun t ω ↦ ∑ s ∈ range t, Y s ω) ℱ μ :=
  martingale_of_condExp_sub_eq_zero_nat (stronglyMeasurable_sum_range_of_succ hY)
    (fun t ↦ integrable_finsetSum _ fun s _ ↦ hint s) fun t ↦ by
      have h : ((fun ω ↦ ∑ s ∈ range (t + 1), Y s ω) - fun ω ↦ ∑ s ∈ range t, Y s ω) = Y t := by
        ext ω
        simp [sum_range_succ]
      rw [h]
      exact hc t

variable {Y : ℕ → Ω → ℝ}

/-- **Orthogonality of martingale differences.** The second moment of a partial sum of
square-integrable martingale differences is the sum of their second moments. -/
theorem integral_sq_sum_range_of_condExp_eq_zero [IsFiniteMeasure μ]
    (hY : ∀ s, StronglyMeasurable[ℱ (s + 1)] (Y s)) (hL2 : ∀ s, MemLp (Y s) 2 μ)
    (hc : ∀ s, μ[Y s | ℱ s] =ᵐ[μ] 0) (t : ℕ) :
    ∫ ω, (∑ s ∈ range t, Y s ω) ^ 2 ∂μ = ∑ s ∈ range t, ∫ ω, Y s ω ^ 2 ∂μ := by
  -- The cross terms vanish: pull the `ℱ j`-measurable earlier term out of `μ[Y j | ℱ j]`
  -- (for real functions `f • g` is `f * g` by `smul_eq_mul`).
  have horth {i j : ℕ} (hij : i < j) : ∫ ω, Y i ω * Y j ω ∂μ = 0 := by
    rw [← integral_condExp (ℱ.le j)]
    exact integral_eq_zero_of_ae (TauCeti.MeasureTheory.condExp_smul_eq_zero_of_condExp_eq_zero
      ((hY i).mono (ℱ.mono (Nat.succ_le_of_lt hij))).aestronglyMeasurable
      ((hL2 i).integrable_mul (hL2 j)) ((hL2 j).integrable one_le_two) (hc j))
  refine TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero (fun s _ ↦ hL2 s)
    fun i _ j _ hij ↦ ?_
  rcases hij.lt_or_gt with h | h
  · exact horth h
  · simpa only [mul_comm] using horth h

/-- **Convergence of square-summable martingale difference series.** If square-integrable
martingale differences have summable second moments, their series converges almost
everywhere. -/
theorem exists_ae_tendsto_sum_range_of_summable_integral_sq [IsFiniteMeasure μ]
    (hY : ∀ s, StronglyMeasurable[ℱ (s + 1)] (Y s)) (hL2 : ∀ s, MemLp (Y s) 2 μ)
    (hc : ∀ s, μ[Y s | ℱ s] =ᵐ[μ] 0) (hsum : Summable fun s ↦ ∫ ω, Y s ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun t ↦ ∑ s ∈ range t, Y s ω) atTop (𝓝 c) := by
  refine (martingale_sum_range hY (fun s ↦ (hL2 s).integrable one_le_two) hc).submartingale
    |>.exists_ae_tendsto_of_bdd (lt_of_le_of_lt (iSup_le fun t ↦ ?_)
      (ENNReal.ofReal_lt_top (r := μ.real Set.univ + ∑' s, ∫ ω, Y s ω ^ 2 ∂μ)))
  -- The `L¹` norm is controlled by the second moment through `|x| ≤ 1 + x ^ 2`.
  have hS : MemLp (fun ω ↦ ∑ s ∈ range t, Y s ω) 2 μ := memLp_finsetSum _ fun s _ ↦ hL2 s
  rw [eLpNorm_one_eq_lintegral_eNorm hS.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_eNorm (hS.integrable one_le_two)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ ω, ‖∑ s ∈ range t, Y s ω‖ ∂μ
      ≤ ∫ ω, (1 + (∑ s ∈ range t, Y s ω) ^ 2) ∂μ :=
        integral_mono (hS.integrable one_le_two).norm
          ((integrable_const 1).add hS.integrable_sq) fun ω ↦ by
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (∑ s ∈ range t, Y s ω), sq_abs (∑ s ∈ range t, Y s ω)]
    _ = μ.real Set.univ + ∑ s ∈ range t, ∫ ω, Y s ω ^ 2 ∂μ := by
        rw [integral_add (integrable_const 1) hS.integrable_sq, integral_const, smul_eq_mul,
          mul_one, integral_sq_sum_range_of_condExp_eq_zero hY hL2 hc t]
    _ ≤ μ.real Set.univ + ∑' s, ∫ ω, Y s ω ^ 2 ∂μ := by
        gcongr
        exact hsum.sum_le_tsum _ fun s _ ↦ integral_nonneg fun ω ↦ sq_nonneg _

end MeasureTheory

end TauCeti
