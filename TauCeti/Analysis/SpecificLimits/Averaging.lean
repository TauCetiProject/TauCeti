/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Averaging iterations with step sizes of divergent sum

Let `α t ∈ [0, 1]` be step sizes with `∑ α t = ∞`. The averaging iteration

`z (t + 1) = (1 - α t) • z t + α t • r t`

moves `z` by the fraction `α t` of the way towards the input `r t`. If the inputs tend to `0`,
then so does `z`, whatever its initial value: the products `∏_{s < t} (1 - α s)` tend to `0`,
so the initial value is forgotten, and the inputs of small norm can only keep `z` small. Only the
eventual behaviour of the steps matters, so the convergence statements assume `0 ≤ α t ≤ 1` only
from some time on.

Summation by parts turns this into a statement about noise. If `W` follows the iteration
`W (t + 1) = (1 - α t) • W t + α t • w t` and the series `∑ α t • w t` converges, then
`W t → 0`, although the terms `w t` themselves need not tend to `0`. For `α t = 1 / (t + 1)`,
`W t` is the running average of `w 0, …, w (t - 1)` and this is Kronecker's lemma. In stochastic
approximation the series is a martingale transform whose convergence comes from the martingale
convergence theorem.

## Main results

* `TauCeti.tendsto_prod_range_one_sub_of_not_summable`: `∏_{s < t} (1 - α s) → 0`.
* `TauCeti.tendsto_zero_of_succ_eq_one_sub_smul_add_smul`: the averaging iteration with inputs
  tending to `0` tends to `0`.
* `TauCeti.tendsto_zero_of_tendsto_sum_range_smul`: the averaging iteration of a sequence `w` for
  which `∑ α t • w t` converges tends to `0`.

## References

* J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Mach. Learn. **16**
  (1994), 185–202, proof of Lemma 1.
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- If eventually `0 ≤ α t ≤ 1`, and `∑ α t = ∞`, the products `∏_{s < t} (1 - α s)` tend
to `0`. -/
theorem tendsto_prod_range_one_sub_of_not_summable {α : ℕ → ℝ} (h0 : ∀ᶠ t in atTop, 0 ≤ α t)
    (h1 : ∀ᶠ t in atTop, α t ≤ 1) (hα : ¬Summable α) :
    Tendsto (fun t ↦ ∏ s ∈ range t, (1 - α s)) atTop (𝓝 0) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h0.and h1)
  -- From time `T` on, `0 ≤ 1 - α s ≤ exp (-α s)`, and the exponents sum to `-∞`.
  have htail : Tendsto (fun t ↦ ∏ s ∈ range t, (1 - α (T + s))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun t ↦ ∑ s ∈ range t, α (T + s)) atTop atTop :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg fun s ↦ (hT _ (Nat.le_add_right T s)).1).1
        (by simpa only [add_comm _ T] using (summable_nat_add_iff T).not.2 hα)
    refine squeeze_zero
      (fun t ↦ prod_nonneg fun s _ ↦ sub_nonneg.2 (hT _ (Nat.le_add_right T s)).2) (fun t ↦ ?_)
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsum)
    calc ∏ s ∈ range t, (1 - α (T + s)) ≤ ∏ s ∈ range t, Real.exp (-α (T + s)) :=
          prod_le_prod₀ (fun s _ ↦ sub_nonneg.2 (hT _ (Nat.le_add_right T s)).2) fun s _ ↦
            Real.one_sub_le_exp_neg _
      _ = Real.exp (-∑ s ∈ range t, α (T + s)) := by rw [← Real.exp_sum, sum_neg_distrib]
  have h := htail.const_mul (∏ s ∈ range T, (1 - α s))
  rw [mul_zero] at h
  refine (tendsto_add_atTop_iff_nat T).1 (h.congr fun t ↦ ?_)
  rw [add_comm t T, prod_range_add]

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Averaging with vanishing inputs.** If eventually `0 ≤ α t ≤ 1`, `∑ α t = ∞` and the inputs
`r t` tend to `0`, then the iteration `z (t + 1) = (1 - α t) • z t + α t • r t` tends to `0`, from
any initial value. -/
theorem tendsto_zero_of_succ_eq_one_sub_smul_add_smul {α : ℕ → ℝ} {z r : ℕ → E}
    (h0 : ∀ᶠ t in atTop, 0 ≤ α t) (h1 : ∀ᶠ t in atTop, α t ≤ 1) (hα : ¬Summable α)
    (hr : Tendsto r atTop (𝓝 0)) (hz : ∀ t, z (t + 1) = (1 - α t) • z t + α t • r t) :
    Tendsto z atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hr (ε / 2) (half_pos hε)).and
    (h0.and h1))
  have hT0 : ∀ s, 0 ≤ α (s + T) := fun s ↦ (hT (s + T) (Nat.le_add_left T s)).2.1
  have hT1 : ∀ s, α (s + T) ≤ 1 := fun s ↦ (hT (s + T) (Nat.le_add_left T s)).2.2
  -- From time `T` on, the excess of `‖z‖` over `ε / 2` decays at least like the products.
  have key : ∀ n, ‖z (n + T)‖ - ε / 2 ≤
      (∏ s ∈ range n, (1 - α (s + T))) * max (‖z T‖ - ε / 2) 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hrn : ‖r (n + T)‖ ≤ ε / 2 := by
        simpa using (hT (n + T) (Nat.le_add_left T n)).1.le
      have hstep : ‖z (n + 1 + T)‖ ≤ (1 - α (n + T)) * ‖z (n + T)‖ + α (n + T) * ‖r (n + T)‖ := by
        rw [Nat.add_right_comm, hz]
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 (hT1 n)),
          Real.norm_of_nonneg (hT0 n)]
      have hih := mul_le_mul_of_nonneg_left ih (sub_nonneg.2 (hT1 n))
      have hr' := mul_le_mul_of_nonneg_left hrn (hT0 n)
      rw [prod_range_succ]
      linarith
  have hprod := (tendsto_prod_range_one_sub_of_not_summable (.of_forall hT0) (.of_forall hT1)
    (by rwa [summable_nat_add_iff T])).mul_const (max (‖z T‖ - ε / 2) 0)
  rw [zero_mul] at hprod
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hprod (ε / 2) (half_pos hε)
  refine ⟨N + T, fun m hm ↦ ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + T := ⟨m - T, by omega⟩
  have hn := hN n (by omega)
  rw [Real.dist_eq, sub_zero] at hn
  rw [dist_zero_right]
  linarith [key n, le_abs_self ((∏ s ∈ range n, (1 - α (s + T))) * max (‖z T‖ - ε / 2) 0)]

/-- **Averaging of a summable noise.** If eventually `0 ≤ α t ≤ 1`, `∑ α t = ∞` and the series
`∑ α t • w t` converges, then the iteration `W (t + 1) = (1 - α t) • W t + α t • w t` tends to
`0`, from any initial value. -/
theorem tendsto_zero_of_tendsto_sum_range_smul {α : ℕ → ℝ} {w W : ℕ → E} {L : E}
    (h0 : ∀ᶠ t in atTop, 0 ≤ α t) (h1 : ∀ᶠ t in atTop, α t ≤ 1) (hα : ¬Summable α)
    (hsum : Tendsto (fun t ↦ ∑ s ∈ range t, α s • w s) atTop (𝓝 L))
    (hW : ∀ t, W (t + 1) = (1 - α t) • W t + α t • w t) :
    Tendsto W atTop (𝓝 0) := by
  -- With the tails `R t = L - ∑_{s < t} α s • w s`, the sum `W + R` follows the averaging
  -- iteration with inputs `R`.
  set R : ℕ → E := fun t ↦ L - ∑ s ∈ range t, α s • w s with hR_def
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa [hR_def] using (tendsto_const_nhds (x := L)).sub hsum
  have hZ := tendsto_zero_of_succ_eq_one_sub_smul_add_smul (z := fun t ↦ W t + R t) h0 h1 hα hR
    fun t ↦ by simp only [hR_def, sum_range_succ, hW]; module
  simpa using hZ.sub hR

end TauCeti
