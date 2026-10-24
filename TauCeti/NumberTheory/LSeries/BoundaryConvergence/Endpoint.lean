/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection
public import TauCeti.NumberTheory.LSeries.Newman.Tauberian

/-!
# Ordered boundary convergence of bounded Dirichlet series at `s = 1`

Let `a : ℕ → ℂ` be bounded by `M` from `n = 1` on, and let `F` be holomorphic on an open set
containing the closed half-plane `1 ≤ re s`, with `LSeriesHasSum a s (F s)` for `1 < re s`.
Then the ordered partial sums `∑ n ∈ Finset.Icc 1 N, a n / n` converge to `F 1`
(`boundedDirichlet_tendsto_ordered_at_one`).

The conclusion is a limit of *ordered* finite cutoffs: the Dirichlet series need not converge
absolutely at `s = 1` (for example for `a n = (-1) ^ (n - 1)`), so it is neither an unconditional
`HasSum` nor a statement about the value of `LSeries a 1`.

The proof applies Newman's Tauberian theorem `newmanLaplace_tendsto_integral` to the step
function `t ↦ a ⌊exp t⌋₊`, which is bounded by `M` on `[0, ∞)`:

* on each step `[log n, log (n + 1)]`, the substitution `x = exp t` turns its Laplace integral
  into `a n ∫ x in n..n+1, x ^ (-z - 1)` (`intervalIntegral_floor_exp_mul_cexp_neg_mul`);
* summing the steps, its truncated Laplace transform at `log (N + 1)` is the partial sum of the
  Dirichlet series of `a` at `z + 1` plus the partial sum of the step correction
  (`intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ`);
* letting `N → ∞`, its Laplace transform on `0 < re z` is `LSeries a (z + 1) + stepCorrection a z`
  (`integral_floor_exp_mul_cexp_neg_mul`), which `F (z + 1) + stepCorrection a z` continues to a
  neighbourhood of `0 ≤ re z`, since the step correction is holomorphic on `-1 < re z`.

At `z = 0` the truncated transform at `log (N + 1)` is
`∑ n ≤ N, (a n / n + stepCorrectionTerm a n 0)`; subtracting the absolutely convergent step
correction gives the theorem.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set
open scoped Topology Complex Interval

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {M : ℝ} {z : ℂ}

/-- **The Laplace integral over one step.** For `n ≠ 0`, the step function `t ↦ a ⌊exp t⌋₊`
equals `a n` on `(log n, log (n + 1))`, so its Laplace integral over `[log n, log (n + 1)]` is
`a n ∫ x in n..n+1, x ^ (-z - 1)`. -/
theorem intervalIntegral_floor_exp_mul_cexp_neg_mul (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    ∫ t in Real.log n..Real.log (n + 1), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      a n * ∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [intervalIntegral_ofReal_cpow_neg_sub_one hn' (by positivity),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_Ioo_of_le
    (Real.log_le_log hn' (by linarith)) fun t ht ↦ ?_
  have hlo : (n : ℝ) < Real.exp t := by simpa [Real.exp_log hn'] using Real.exp_lt_exp.mpr ht.1
  have hhi : Real.exp t < n + 1 := by
    simpa [Real.exp_log (by positivity : (0 : ℝ) < n + 1)] using Real.exp_lt_exp.mpr ht.2
  rw [(Nat.floor_eq_iff (Real.exp_pos t).le).mpr ⟨hlo.le, hhi⟩]

/-- The step function `t ↦ a ⌊exp t⌋₊` times `exp (-z t)` is interval integrable on each step
`[log n, log (n + 1)]`, `n ≠ 0`, where it agrees with `a n exp (-z t)` away from the
endpoints. -/
theorem intervalIntegrable_floor_exp_mul_cexp_neg_mul (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    (z : ℂ) : IntervalIntegrable (fun t : ℝ ↦ a ⌊Real.exp t⌋₊ * cexp (-z * t)) volume
      (Real.log n) (Real.log (n + 1)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  refine ((by fun_prop : Continuous fun t : ℝ ↦ a n * cexp (-z * t)).intervalIntegrable
    _ _).congr_uIoo fun t ht ↦ ?_
  rw [uIoo_of_le (Real.log_le_log hn' (by linarith))] at ht
  have hlo : (n : ℝ) < Real.exp t := by simpa [Real.exp_log hn'] using Real.exp_lt_exp.mpr ht.1
  have hhi : Real.exp t < n + 1 := by
    simpa [Real.exp_log (by positivity : (0 : ℝ) < n + 1)] using Real.exp_lt_exp.mpr ht.2
  simp only [(Nat.floor_eq_iff (Real.exp_pos t).le).mpr ⟨hlo.le, hhi⟩]

/-- **The truncated Laplace transform of the step function.** For every `N`, the Laplace integral
of `t ↦ a ⌊exp t⌋₊` over `[0, log (N + 1)]` is the partial sum up to `N` of the Dirichlet series
of `a` at `z + 1` plus that of the step correction. -/
theorem intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    ∫ t in (0 : ℝ)..Real.log (N + 1), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      ∑ n ∈ Finset.range (N + 1), (LSeries.term a (z + 1) n + stepCorrectionTerm a n z) := by
  -- the steps `[log (k + 1), log (k + 2)]`, `k < N`, partition `[0, log (N + 1)]`
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ ↦ a ⌊Real.exp t⌋₊ * cexp (-z * t)) (μ := volume)
    (a := fun k : ℕ ↦ Real.log (k + 1)) (n := N) fun k _ ↦ by
      simpa using intervalIntegrable_floor_exp_mul_cexp_neg_mul a k.succ_ne_zero z
  simp only [Nat.cast_zero, zero_add, Real.log_one] at h
  rw [← h, Finset.sum_range_succ', LSeries.term_zero, stepCorrectionTerm_zero, Pi.zero_apply,
    add_zero, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.succ_ne_zero
  have h₁ := intervalIntegral_floor_exp_mul_cexp_neg_mul a k.succ_ne_zero z
  push_cast at h₁ ⊢
  rw [h₁, LSeries.term_of_ne_zero k.succ_ne_zero, stepCorrectionTerm_of_ne_zero a k.succ_ne_zero,
    div_eq_mul_inv, ← Complex.cpow_neg, neg_add', ← mul_add]
  push_cast
  ring

/-- For `0 ≤ t`, the step function `t ↦ a ⌊exp t⌋₊` only takes values `a n` with `1 ≤ n`, so it
is bounded by `M` when the coefficients are bounded by `M` from `n = 1` on. -/
private theorem norm_floor_exp_le (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) {t : ℝ} (ht : t ∈ Ici 0) :
    ‖a ⌊Real.exp t⌋₊‖ ≤ M :=
  hbound _ (Nat.le_floor (by simpa using Real.one_le_exp (mem_Ici.mp ht)))

/-- The cutoffs `log (N + 1)` tend to infinity. -/
private theorem tendsto_log_natCast_add_one :
    Tendsto (fun N : ℕ ↦ Real.log (N + 1)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- **The Laplace transform of the step function.** For coefficients bounded from `n = 1` on and
`0 < re z`, the Laplace transform of `t ↦ a ⌊exp t⌋₊` is `LSeries a (z + 1) + stepCorrection a z`.
-/
theorem integral_floor_exp_mul_cexp_neg_mul (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      LSeries a (z + 1) + stepCorrection a z := by
  have hint := integrableOn_mul_cexp_neg_mul
    (measurable_from_nat.comp Real.measurable_exp.nat_floor).aestronglyMeasurable
    (fun t ht ↦ norm_floor_exp_le hbound ht) hz
  have hL : LSeriesSummable a (z + 1) :=
    LSeriesSummable_of_le_const_mul_rpow (x := 1) (by simpa using hz)
      ⟨M, fun n hn ↦ by simpa using hbound n (Nat.one_le_iff_ne_zero.mpr hn)⟩
  have hsum := (hL.LSeriesHasSum.add (hasSum_stepCorrection hbound (by linarith))).tendsto_sum_nat
  rw [integral_Ici_eq_integral_Ioi]
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0
    ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint) tendsto_log_natCast_add_one) ?_
  simp_rw [intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ]
  exact hsum.comp (tendsto_add_atTop_nat 1)

/-- **Bounded Dirichlet series converge in order at `s = 1`.** Let `a : ℕ → ℂ` be bounded from
`n = 1` on, and let `F` be holomorphic on an open set `Ω` containing the closed half-plane
`1 ≤ re s`, with `LSeriesHasSum a s (F s)` for `1 < re s`. Then the ordered partial sums
`∑ n ∈ Finset.Icc 1 N, a n / n` converge to `F 1`.

This is a limit of ordered cutoffs, not an unconditional sum: the Dirichlet series of `a` need not
converge absolutely at `s = 1`. -/
theorem boundedDirichlet_tendsto_ordered_at_one (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum a s (F s)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ)) atTop (𝓝 (F 1)) := by
  -- Newman's theorem for the step function, with `F (z + 1) + stepCorrection a z` continuing its
  -- Laplace transform to `{z | z + 1 ∈ Ω, -1 < re z}`.
  have hshift : Continuous fun z : ℂ ↦ z + 1 := by fun_prop
  have hnewman := newmanLaplace_tendsto_integral
    (f := fun t ↦ a ⌊Real.exp t⌋₊) (G := fun z ↦ F (z + 1) + stepCorrection a z)
    (Ω := (fun z : ℂ ↦ z + 1) ⁻¹' Ω ∩ {z | -1 < z.re})
    (measurable_from_nat.comp Real.measurable_exp.nat_floor).aestronglyMeasurable
    (fun t ht ↦ norm_floor_exp_le hbound ht)
    ((hΩ.preimage hshift).inter (isOpen_lt continuous_const Complex.continuous_re))
    (fun z (hz : 0 ≤ z.re) ↦ ⟨hcover (by simpa using hz), (by linarith : -1 < z.re)⟩)
    ((hF.comp (differentiable_id.add_const 1).differentiableOn
      fun _ ↦ And.left).add
      ((differentiableOn_stepCorrection hbound).mono inter_subset_right))
    fun z hz ↦ by
      rw [integral_floor_exp_mul_cexp_neg_mul hbound hz,
        (hseries (z + 1) (by simpa using hz)).LSeries_eq]
  -- at `z = 0`, the truncated transform at `log (N + 1)` is the partial sum of `a n / n` plus the
  -- partial sum of the step correction
  have hcorr := ((hasSum_stepCorrection (z := 0) hbound (by simp)).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have h := (hnewman.comp tendsto_log_natCast_add_one).sub hcorr
  simp only [zero_add, add_sub_cancel_right] at h
  refine h.congr fun N ↦ ?_
  have hN := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ a N 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at hN
  simp only [Function.comp_apply, hN, Finset.sum_add_distrib, add_sub_cancel_right]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot N.succ_pos, LSeries.term_zero, zero_add,
    zero_add, Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [LSeries.term_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1),
    Complex.cpow_one]

end TauCeti.LSeries
