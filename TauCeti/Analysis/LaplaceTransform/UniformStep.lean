/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Truncated
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.SpecialFunctions.Exp.Decay

/-!
# Laplace transforms of uniform step functions

For a uniform step function `t ↦ c ⌊t / h⌋₊` of step length `h > 0`:

* the truncated Laplace transform over `[0, N * h]` (`intervalIntegral_floor_div_mul_cexp_neg_mul`)
  and, for bounded `c` and `0 < re z`, the full Laplace transform on `[0, ∞)`
  (`integral_floor_div_mul_cexp_neg_mul`) factor as the entire single-step integral
  `∫ u in 0..h, exp (-z * u)` times the power series of `c` evaluated at `exp (-h * z)`;
* when the power series of `c` has a sum `P` continuous on `closedBall 0 1` agreeing with
  `∑' n, c n * w ^ n` on `ball 0 1`, `exists_continuousOn_integral_floor_div_mul_cexp_neg_mul`
  transfers `P` to a continuous extension on `0 ≤ re z` that is holomorphic on `0 < re z` and
  agrees there with the Laplace transform of `t ↦ c ⌊t / h⌋₊`.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Complex Interval

namespace TauCeti

private theorem norm_cexp_neg_mul_lt_one {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    ‖cexp (-(h : ℂ) * z)‖ < 1 := by
  rw [neg_mul, mul_comm (h : ℂ) z, Complex.norm_exp_neg_mul_ofReal]
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

/-- **Truncated Laplace transform of a uniform step function.** For `h > 0`, `c : ℕ → ℂ`,
`N : ℕ`, and `z : ℂ`, the Laplace integral of `t ↦ c ⌊t / h⌋₊` over `[0, N * h]` factors as the
single-step integral `∫ u in 0..h, exp (-z * u)` times the `N`-th partial sum of the power series
`∑ c n * exp (-h * z) ^ n`. -/
theorem intervalIntegral_floor_div_mul_cexp_neg_mul (c : ℕ → ℂ) {h : ℝ} (hh : 0 < h)
    (N : ℕ) (z : ℂ) :
    ∫ t in (0 : ℝ)..((N : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t) =
      (∫ u in (0 : ℝ)..h, cexp (-z * u)) * ∑ n ∈ Finset.range N, c n * cexp (-(h : ℂ) * z) ^ n := by
  have hfloor {n : ℕ} {t : ℝ} (ht : t ∈ Ioo ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h)) :
      ⌊t / h⌋₊ = n := by
    have h1 : (n : ℝ) < t / h := (lt_div_iff₀ hh).mpr ht.1
    have h2 : t / h < (n : ℝ) + 1 :=
      (div_lt_iff₀ hh).mpr (by simpa only [Nat.cast_add, Nat.cast_one] using ht.2)
    exact (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans h1.le)).mpr ⟨h1.le, h2⟩
  have hle (n : ℕ) : (n : ℝ) * h ≤ ((n + 1 : ℕ) : ℝ) * h := by
    gcongr
    exact_mod_cast Nat.le_succ n
  have hint (n : ℕ) : IntervalIntegrable (fun t : ℝ ↦ c ⌊t / h⌋₊ * cexp (-z * t)) volume
      ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h) := by
    refine ((by fun_prop : Continuous fun t : ℝ ↦ c n * cexp (-z * t)).intervalIntegrable
      _ _).congr_uIoo fun t ht ↦ ?_
    rw [uIoo_of_le (hle n)] at ht
    simp only [hfloor ht]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ ↦ c ⌊t / h⌋₊ * cexp (-z * t)) (μ := volume)
    (a := fun k : ℕ ↦ (k : ℝ) * h) (n := N) fun k _ ↦ hint k
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hcongr : ∫ t in ((n : ℝ) * h)..(((n + 1 : ℕ) : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t) =
      ∫ t in ((n : ℝ) * h)..(((n + 1 : ℕ) : ℝ) * h), c n * cexp (-z * t) :=
    intervalIntegral.integral_congr_Ioo_of_le (hle n) fun t ht ↦ by rw [hfloor ht]
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hshift := intervalIntegral.integral_comp_add_left (f := fun t : ℝ ↦ cexp (-z * t))
    ((n : ℝ) * h) (a := (0 : ℝ)) (b := h)
  have hhi : (n : ℝ) * h + h = ((n + 1 : ℕ) : ℝ) * h := by push_cast; ring
  rw [add_zero, hhi] at hshift
  rw [← hshift]
  have hexp (u : ℝ) : cexp (-z * ((n : ℝ) * h + u : ℝ)) =
      cexp (-(h : ℂ) * z) ^ n * cexp (-z * u) := by
    rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp, intervalIntegral.integral_const_mul]
  ring

/-- **Laplace transform of a bounded uniform step function.** For `h > 0`, a bounded sequence
`c : ℕ → ℂ`, and `0 < re z`, the Laplace transform of `t ↦ c ⌊t / h⌋₊` on `[0, ∞)` factors as
`(∫ u in 0..h, exp (-z * u)) * ∑' n, c n * exp (-h * z) ^ n`. -/
theorem integral_floor_div_mul_cexp_neg_mul {c : ℕ → ℂ} {M : ℝ} (hbound : ∀ n, ‖c n‖ ≤ M)
    {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t) =
      (∫ u in (0 : ℝ)..h, cexp (-z * u)) * ∑' n, c n * cexp (-(h : ℂ) * z) ^ n := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ c ⌊t / h⌋₊) (volume.restrict (Ici 0)) :=
    (measurable_from_nat.comp (measurable_id.div_const h).nat_floor).aestronglyMeasurable
  have hint := integrableOn_mul_cexp_neg_mul hmeas (fun t _ ↦ hbound _) hz
  have hnorm_lt : ‖cexp (-(h : ℂ) * z)‖ < 1 := norm_cexp_neg_mul_lt_one hh hz
  have hsumm : Summable fun n : ℕ ↦ c n * cexp (-(h : ℂ) * z) ^ n := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg _) hnorm_lt).mul_left M) fun n ↦ ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)
  have hlim1 : Tendsto (fun N : ℕ ↦ ∫ t in (0 : ℝ)..((N : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t))
      atTop (𝓝 (∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t))) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact intervalIntegral_tendsto_integral_Ioi 0 ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
  have hlim2 : Tendsto (fun N : ℕ ↦ ∫ t in (0 : ℝ)..((N : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t))
      atTop (𝓝 ((∫ u in (0 : ℝ)..h, cexp (-z * u)) * ∑' n, c n * cexp (-(h : ℂ) * z) ^ n)) := by
    simp_rw [intervalIntegral_floor_div_mul_cexp_neg_mul c hh]
    exact hsumm.hasSum.tendsto_sum_nat.const_mul _
  exact tendsto_nhds_unique hlim1 hlim2

/-- **Half-plane transfer of a disc-algebra power series via a uniform step function.** For
`h > 0`, a bounded sequence `c : ℕ → ℂ`, and a function `P : ℂ → ℂ` continuous on `closedBall 0 1`
with power series `∑' n, c n * w ^ n = P w` on `ball 0 1`, the Laplace transform
`z ↦ ∫ t in Ici 0, c ⌊t / h⌋₊ * exp (-z * t)` extends continuously to `0 ≤ re z` and
holomorphically to `0 < re z`. -/
theorem exists_continuousOn_integral_floor_div_mul_cexp_neg_mul
    {c : ℕ → ℂ} {M : ℝ} (hbound : ∀ n, ‖c n‖ ≤ M) {h : ℝ} (hh : 0 < h) {P : ℂ → ℂ}
    (hP_cont : ContinuousOn P (closedBall 0 1))
    (hP_sum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n ↦ c n * w ^ n) (P w)) :
    ∃ G : ℂ → ℂ,
      ContinuousOn G {z : ℂ | 0 ≤ z.re} ∧
      DifferentiableOn ℂ G {z : ℂ | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t)) := by
  set K : ℂ → ℂ := fun z ↦ ∫ u in (0 : ℝ)..h, cexp (-z * u)
  set G : ℂ → ℂ := fun z ↦ K z * P (cexp (-(h : ℂ) * z))
  have hK_diff : Differentiable ℂ K := by
    simpa [K] using
      differentiable_intervalIntegral_mul_cexp_neg_mul (f := fun _ : ℝ ↦ (1 : ℂ)) (a := 0) (b := h)
  have hG_eq : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t) := by
    intro z hz
    rw [integral_floor_div_mul_cexp_neg_mul hbound hh hz,
      (hP_sum _ (norm_cexp_neg_mul_lt_one hh hz)).tsum_eq]
  have hlap_diff : DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t)) {z : ℂ | 0 < z.re} :=
    differentiableOn_integral_mul_cexp_neg_mul (f := fun t : ℝ ↦ c ⌊t / h⌋₊) (fun t _ ↦ hbound _)
  refine ⟨G, ?_, hlap_diff.congr fun z hz ↦ hG_eq z hz, hG_eq⟩
  refine hK_diff.continuous.continuousOn.mul
    (hP_cont.comp (by fun_prop : Continuous fun z : ℂ ↦ cexp (-(h : ℂ) * z)).continuousOn
      fun z (hz : 0 ≤ z.re) ↦ ?_)
  rw [mem_closedBall_zero_iff, neg_mul, mul_comm (h : ℂ) z, Complex.norm_exp_neg_mul_ofReal]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

end TauCeti
