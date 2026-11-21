/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Martingale.Convergence

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

* `MeasureTheory.condExp_smul_eq_zero_of_condExp_eq_zero`: a measurable factor times a
  martingale difference is again a martingale difference.
* `MeasureTheory.martingale_sum_range`: the partial sums of martingale differences form a
  martingale.
* `MeasureTheory.integral_sq_sum_range`: the second moment of a partial sum of square-integrable
  martingale differences is the sum of their second moments.
* `MeasureTheory.exists_ae_tendsto_sum_range_of_summable_integral_sq`: if the second moments are
  summable, the series converges almost everywhere.
-/

public section

open Filter Finset Topology
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m₀}

/-- If `μ[g | m] = 0` and `f` is `m`-measurable, then `μ[f • g | m] = 0`: a measurable factor
times a martingale difference is again a martingale difference. -/
theorem condExp_smul_eq_zero_of_condExp_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {m : MeasurableSpace Ω} {f : Ω → ℝ} {g : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (hg : Integrable g μ)
    (hcg : μ[g | m] =ᵐ[μ] 0) : μ[f • g | m] =ᵐ[μ] 0 := by
  filter_upwards [condExp_smul_of_aestronglyMeasurable_left hf hfg hg, hcg] with ω h₁ h₂
  simp [h₁, h₂]

/-- A partial sum of a sequence whose `s`-th term is `ℱ (s + 1)`-measurable is measurable at the
time of its last term. -/
theorem stronglyMeasurable_sum_range {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
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
  martingale_of_condExp_sub_eq_zero_nat (stronglyMeasurable_sum_range hY)
    (fun t ↦ integrable_finsetSum _ fun s _ ↦ hint s) fun t ↦ by
      have h : ((fun ω ↦ ∑ s ∈ range (t + 1), Y s ω) - fun ω ↦ ∑ s ∈ range t, Y s ω) = Y t := by
        ext ω
        simp [sum_range_succ]
      rw [h]
      exact hc t

variable {Y : ℕ → Ω → ℝ}

/-- **Orthogonality of martingale differences.** The second moment of a partial sum of
square-integrable martingale differences is the sum of their second moments. -/
theorem integral_sq_sum_range [IsFiniteMeasure μ]
    (hY : ∀ s, StronglyMeasurable[ℱ (s + 1)] (Y s)) (hL2 : ∀ s, MemLp (Y s) 2 μ)
    (hc : ∀ s, μ[Y s | ℱ s] =ᵐ[μ] 0) (t : ℕ) :
    ∫ ω, (∑ s ∈ range t, Y s ω) ^ 2 ∂μ = ∑ s ∈ range t, ∫ ω, Y s ω ^ 2 ∂μ := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hS : MemLp (fun ω ↦ ∑ s ∈ range t, Y s ω) 2 μ := memLp_finsetSum _ fun s _ ↦ hL2 s
    have hSY : Integrable (fun ω ↦ (∑ s ∈ range t, Y s ω) * Y t ω) μ :=
      hS.integrable_mul (hL2 t)
    -- The cross term vanishes: pull the `ℱ t`-measurable partial sum out of `μ[Y t | ℱ t]`
    -- (for real functions `f • g` is `f * g` by `smul_eq_mul`).
    have hcross : ∫ ω, (∑ s ∈ range t, Y s ω) * Y t ω ∂μ = 0 := by
      rw [← integral_condExp (ℱ.le t)]
      exact integral_eq_zero_of_ae (condExp_smul_eq_zero_of_condExp_eq_zero
        (stronglyMeasurable_sum_range hY t).aestronglyMeasurable hSY
        ((hL2 t).integrable one_le_two) (hc t))
    calc ∫ ω, (∑ s ∈ range (t + 1), Y s ω) ^ 2 ∂μ
        = ∫ ω, ((∑ s ∈ range t, Y s ω) ^ 2 + 2 * ((∑ s ∈ range t, Y s ω) * Y t ω) +
            Y t ω ^ 2) ∂μ := by
          congr 1
          ext ω
          rw [sum_range_succ]
          ring
      _ = ∑ s ∈ range (t + 1), ∫ ω, Y s ω ^ 2 ∂μ := by
          rw [integral_add, integral_add, integral_const_mul, hcross, ih, sum_range_succ]
          · ring
          · exact hS.integrable_sq
          · exact hSY.const_mul 2
          · exact hS.integrable_sq.add (hSY.const_mul 2)
          · exact (hL2 t).integrable_sq

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
          mul_one, integral_sq_sum_range hY hL2 hc t]
    _ ≤ μ.real Set.univ + ∑' s, ∫ ω, Y s ω ^ 2 ∂μ := by
        gcongr
        exact hsum.sum_le_tsum _ fun s _ ↦ integral_nonneg fun ω ↦ sq_nonneg _

end MeasureTheory
