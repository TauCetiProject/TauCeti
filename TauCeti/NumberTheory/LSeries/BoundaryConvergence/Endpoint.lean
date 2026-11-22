/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.Newman.Tauberian
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.Deriv
import TauCeti.Analysis.Complex.ClosedHalfPlane
import TauCeti.Analysis.LaplaceTransform.ExponentialStep
import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.LaplaceBridge
import TauCeti.NumberTheory.LSeries.Term

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
function `t ↦ a ⌊exp t⌋₊`, using the bridge identities from
`TauCeti.NumberTheory.LSeries.BoundaryConvergence.LaplaceBridge`:

* its truncated Laplace transform at `log (N + 1)` is the partial sum of the Dirichlet series of
  `a` at `z + 1` plus the partial sum of the step correction
  (`intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ`);
* on `0 < re z`, its Laplace transform is `LSeries a (z + 1) + stepCorrection a z`
  (`integral_floor_exp_mul_cexp_neg_mul`), which `F (z + 1) + stepCorrection a z` continues to a
  neighbourhood of `0 ≤ re z`, since the step correction is holomorphic on `-1 < re z`.

At `z = 0` the truncated transform at `log (N + 1)` is
`∑ n ≤ N, (a n / n + stepCorrectionTerm a n 0)`; subtracting the absolutely convergent step
correction gives the theorem.

Where the Dirichlet series converges absolutely it is holomorphic, so the continuation hypothesis
only concerns the boundary line: `boundedDirichlet_tendsto_ordered_at_one_of_analyticAt` asks
instead that `F` be analytic at each point of `re s = 1`.

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
  have h := (hnewman.comp (Real.tendsto_log_natCast_add_atTop 1)).sub hcorr
  simp only [zero_add, add_sub_cancel_right] at h
  refine h.congr fun N ↦ ?_
  have hN := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ a N 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at hN
  simp only [Function.comp_apply, hN, Finset.sum_add_distrib, add_sub_cancel_right]
  exact sum_range_add_one_LSeries_term_one a N

/-- **Bounded Dirichlet series converge in order at `s = 1`, with a pointwise continuation
hypothesis.** Let `a : ℕ → ℂ` be bounded from `n = 1` on, and let `F` satisfy
`LSeriesHasSum a s (F s)` for `1 < re s` and be analytic at every point of the line `re s = 1`.
Then the ordered partial sums `∑ n ∈ Finset.Icc 1 N, a n / n` converge to `F 1`.

Since `F` is holomorphic on `1 < re s`, where it is the sum of the Dirichlet series, this hypothesis
on `F` is equivalent to holomorphy on an open set containing the closed half-plane `1 ≤ re s`, as
in `boundedDirichlet_tendsto_ordered_at_one`. -/
theorem boundedDirichlet_tendsto_ordered_at_one_of_analyticAt (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M)
    {F : ℂ → ℂ} (hF : ∀ s : ℂ, s.re = 1 → AnalyticAt ℂ F s)
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum a s (F s)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ)) atTop (𝓝 (F 1)) := by
  -- `F` is holomorphic on `1 < re s`, where it agrees with `LSeries a`.
  have habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      (hseries y (by simpa using hy)).LSeriesSummable
  have hF' : DifferentiableOn ℂ F {s | (1 : ℝ) < s.re} :=
    ((LSeries_differentiableOn a).mono (s := {s | (1 : ℝ) < s.re}) fun _ hs ↦
      habs.trans_lt (EReal.coe_lt_coe_iff.mpr hs)).congr fun s hs ↦ (hseries s hs).LSeries_eq.symm
  obtain ⟨Ω, hΩ, hcover, hFΩ⟩ :=
    (TauCeti.exists_isOpen_differentiableOn_iff_analyticAt hF').mpr hF
  exact boundedDirichlet_tendsto_ordered_at_one hbound hΩ hcover hFΩ hseries

end TauCeti.LSeries
