/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint

/-!
# Ordered convergence is not unconditional convergence

The alternating coefficients, zero at `0` and `(-1) ^ (n - 1)` at positive `n`, satisfy the
bounded Dirichlet endpoint theorem with an entire continuation. Their ordered harmonic sums
converge to `-HurwitzZeta.expZeta (1 / 2) 1`, but their boundary Dirichlet series is not
unconditionally summable. In particular no `LSeriesHasSum` at `1` can replace the ordered limit.

In contrast, the constant coefficients `1` admit no holomorphic continuation on an open
neighbourhood of the closed half-plane `1 ≤ re s`. Otherwise the endpoint theorem would
force the divergent harmonic partial sums to converge.

The continuation for alternating coefficients uses Mathlib's exponential zeta function,
whose defining coefficients at parameter `1 / 2` are `exp (π i n) = (-1) ^ n`.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti.LSeries

/-- The alternating coefficients `1, -1, 1, -1, …` at positive indices, with value `0` at `0`.
Their Dirichlet series is the Dirichlet eta series. -/
def alternatingCoeff (n : ℕ) : ℂ :=
  if n = 0 then 0 else (-1) ^ (n - 1)

@[simp] theorem alternatingCoeff_zero : alternatingCoeff 0 = 0 := by
  simp [alternatingCoeff]

/-- At positive indices the alternating coefficients are `(-1) ^ (n - 1)`. -/
@[simp] theorem alternatingCoeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    alternatingCoeff n = (-1 : ℂ) ^ (n - 1) := by
  simp [alternatingCoeff, hn]

/-- The alternating coefficients have unit norm at every positive index. -/
theorem norm_alternatingCoeff {n : ℕ} (hn : n ≠ 0) : ‖alternatingCoeff n‖ = 1 := by
  simp [alternatingCoeff_of_ne_zero hn, norm_pow]

private theorem alternatingCoeff_eq_neg_exp {n : ℕ} (hn : n ≠ 0) :
    alternatingCoeff n = -Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ) * n) := by
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ) * n) = (-1 : ℂ) ^ n := by
    have harg : 2 * Real.pi * Complex.I * (1 / 2 : ℂ) * n =
        n * ((Real.pi : ℂ) * Complex.I) := by ring
    rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [hexp]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [alternatingCoeff, pow_succ]

/-- The native exponential zeta function at parameter `1 / 2`, with its sign reversed,
continues the alternating Dirichlet series from the half-plane of absolute convergence. -/
theorem LSeriesHasSum_alternatingCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum alternatingCoeff s (-HurwitzZeta.expZeta (1 / 2 : ℝ) s) := by
  refine (LSeriesHasSum_congr (g := fun n ↦
    -Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ) * n)) s _
    fun hn ↦ alternatingCoeff_eq_neg_exp hn).mpr ?_
  simpa [Pi.neg_def] using (HurwitzZeta.LSeriesHasSum_exp (1 / 2) hs).neg

/-- Ordered harmonic sums of the alternating coefficients converge, using an entire
continuation rather than a merely continuous boundary value. -/
theorem tendsto_sum_Icc_alternatingCoeff_div :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, alternatingCoeff n / (n : ℂ)) atTop
      (𝓝 (-HurwitzZeta.expZeta (1 / 2 : ℝ) 1)) := by
  have hhalf : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
    intro h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp h
    norm_num at this
  exact boundedDirichlet_tendsto_ordered_at_one (M := 1)
    (fun n hn ↦ (norm_alternatingCoeff (Nat.ne_zero_of_lt hn)).le)
    isOpen_univ (subset_univ _)
    (HurwitzZeta.differentiable_expZeta_of_ne_zero hhalf).neg.differentiableOn
    (fun _ hs ↦ LSeriesHasSum_alternatingCoeff hs)

/-- The alternating boundary terms have exactly the norms of the harmonic series,
including the totalized term at index `0`. -/
theorem norm_alternatingCoeff_div (n : ℕ) :
    ‖alternatingCoeff n / (n : ℂ)‖ = 1 / (n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [norm_alternatingCoeff hn]

/-- Although its ordered harmonic sums converge, the alternating Dirichlet series is not
absolutely (equivalently, unconditionally over `ℂ`) summable at `s = 1`. -/
theorem not_LSeriesSummable_alternatingCoeff_one :
    ¬ LSeriesSummable alternatingCoeff 1 := by
  intro h
  apply Real.not_summable_one_div_natCast
  refine h.norm.congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_one, norm_alternatingCoeff_div]

/-- No unconditional sum at the boundary exists for the alternating coefficients, regardless
of the proposed value. This does not contradict their ordered boundary limit. -/
theorem not_LSeriesHasSum_alternatingCoeff_one (L : ℂ) :
    ¬ LSeriesHasSum alternatingCoeff 1 L :=
  fun h ↦ not_LSeriesSummable_alternatingCoeff_one h.LSeriesSummable

/-- Constant coefficients cannot have the analytic continuation required by the bounded
Dirichlet endpoint theorem: that would make the harmonic partial sums converge. -/
theorem not_differentiableOn_of_LSeriesHasSum_one {Ω : Set ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω)
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun _ ↦ 1) s (F s)) :
    ¬ DifferentiableOn ℂ F Ω := by
  intro hF
  have hlim := (Complex.continuous_re.tendsto (F 1)).comp
    (boundedDirichlet_tendsto_ordered_at_one (M := 1) (by simp) hΩ hcover hF hseries)
  have hreal : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1))
      atTop (𝓝 (F 1).re) := by
    refine hlim.congr fun N ↦ ?_
    have hre (n : ℕ) : (1 / (n : ℂ)).re = 1 / (n : ℝ) := by
      rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.one_re]
    simp only [Function.comp_apply, Complex.re_sum, hre]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop _ hreal

end TauCeti.LSeries
