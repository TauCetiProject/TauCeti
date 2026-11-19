/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.HalfPlaneIdentity
import TauCeti.Analysis.SpecialFunctions.Pow.AtTop
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Sharpness of whole-line hypotheses in Laplace and Dirichlet boundary convergence

Tauberian boundary theorems at `z = 0` or `s = 1` — Newman's bounded Laplace theorem
(`TauCeti.LSeries.newmanLaplace_tendsto_integral`), the ordered Dirichlet endpoint theorem
(`TauCeti.LSeries.boundedDirichlet_tendsto_ordered_at_one`), and the continuation of the logarithm
of an Euler product across `re s = 1`
(`DirichletCharacter.exists_differentiableOn_exp_eq_LFunction`) — ask for analytic continuation or
nonvanishing across the *entire* vertical boundary line, even though their conclusions evaluate
only at the real boundary point (`z = 0` or `s = 1`).

Twisting by a nonzero imaginary frequency `u : ℝ` (`u ≠ 0`) moves the singularity at the real
boundary point to `u * I` or `1 + u * I` while leaving the real boundary point itself regular and
nonzero. This file uses those vertical shifts to show that none of the three whole-line hypotheses
can be weakened to data at the real boundary point or to radial Abel limits:

* **Bounded Laplace transforms (`t ↦ exp (u * I * t)`).** For `u ≠ 0`, the unimodular function
  `t ↦ exp (u * I * t)` has Laplace transform `(z - u * I)⁻¹` on `0 < re z`, which extends
  analytically across every point of `re z = 0` *except* `u * I`, takes the nonzero value `I / u`
  at `z = 0`, and has radial limit `I / u` as `σ → 0⁺`. Yet its truncated integrals
  `∫ t in 0..T, exp (u * I * t)` oscillate on a circle and fail to converge as `T → ∞`.
* **Bounded Dirichlet series (`n ↦ n ^ (u * I)`).** First, identifying `stepCorrection 1 z` with
  `-riemannZeta₀ (z + 1)` on `-1 < re z` yields the critical-strip partial-sum asymptotic
  `(∑ n ∈ Icc 1 N, n ^ (-s)) - N ^ (1 - s) / (1 - s) → ζ(s)` for `0 < re s`, `s ≠ 1`. Specializing
  to `s = 1 - u * I` (`u ≠ 0`) shows that the unimodular coefficients `n ^ (u * I)` have `L`-series
  `ζ(s - u * I)`, analytic across every boundary point of `re s = 1` except `1 + u * I`, nonzero at
  `s = 1`, with radial Abel limit `ζ(1 - u * I)` as `σ → 1⁺`; yet the ordered partial sums
  `∑ n ∈ Icc 1 N, n ^ (u * I) / n` differ from `ζ(1 - u * I)` by `N ^ (u * I) / (u * I) + o(1)` and
  diverge. In particular, the Abelian theorem `tendsto_LSeries_nhdsGT_one` has no
  bounded-coefficient Tauberian converse from radial limits or local analyticity at `s = 1` alone.
* **Euler logarithms (`recipZetaEulerLogCoeff u`).** The regularized reciprocal
  `s ↦ (s - 1 - u * I) * (riemannZeta₁ (s - u * I))⁻¹` of `ζ(s - u * I)` is holomorphic on an open
  neighbourhood of the *entire* closed half-plane `1 ≤ re s` and, for `u ≠ 0`, is nonzero at every
  point of `re s = 1` except `1 + u * I` (in particular `(ζ(1 - u * I))⁻¹ ≠ 0` at `s = 1`).
  Consequently the `L`-series of `-(Λ n / log n) * n ^ (u * I)` extends analytically across every
  boundary point of `re s = 1` other than `1 + u * I` and has a finite radial Abel limit as
  `σ → 1⁺`. Nevertheless, its single zero on `re s = 1` at `s = 1 + u * I` prevents any continuous
  (let alone holomorphic) extension of that logarithm to `1 ≤ re s`.

## Main declarations

* `TauCeti.LSeries.stepCorrection_one_eq_neg_riemannZeta₀`,
  `TauCeti.LSeries.stepCorrection_one_zero`, and
  `TauCeti.LSeries.tendsto_sum_Icc_cpow_neg_sub_riemannZeta`: the step correction of constant `1`
  and the partial-sum asymptotic of `riemannZeta` on `0 < re s`, `s ≠ 1`.
* `TauCeti.LSeries.integral_Ici_cexp_mul_I_mul_cexp_neg_mul`,
  `TauCeti.LSeries.tendsto_integral_Ici_cexp_mul_I_nhdsGT_zero`,
  `TauCeti.LSeries.not_tendsto_intervalIntegral_cexp_mul_I`, and
  `TauCeti.LSeries.not_continuousOn_of_eq_integral_Ici_cexp_mul_I`: bounded Laplace sharpness.
* `TauCeti.LSeries.LSeriesHasSum_natCast_cpow_mul_I`,
  `TauCeti.LSeries.analyticAt_riemannZeta_sub_mul_I`,
  `TauCeti.LSeries.tendsto_LSeries_natCast_cpow_mul_I_nhdsGT_one`,
  `TauCeti.LSeries.tendsto_sum_Icc_natCast_cpow_mul_I_div_sub`,
  `TauCeti.LSeries.not_tendsto_sum_Icc_natCast_cpow_mul_I_div`, and
  `TauCeti.LSeries.not_continuousOn_of_LSeriesHasSum_natCast_cpow_mul_I`: bounded Dirichlet and
  radial-Abel-converse sharpness.
* `TauCeti.LSeries.recipZetaEulerLogCoeff`, `TauCeti.LSeries.riemannZeta₁_ne_zero_of_one_le_re`,
  `TauCeti.LSeries.exists_analyticAt_LSeries_recipZetaEulerLogCoeff`,
  `TauCeti.LSeries.exists_analyticAt_one_LSeries_recipZetaEulerLogCoeff`,
  `TauCeti.LSeries.exists_tendsto_LSeries_recipZetaEulerLogCoeff_nhdsGT_one`,
  `TauCeti.LSeries.not_continuousOn_of_LSeriesHasSum_recipZetaEulerLogCoeff`, and
  `TauCeti.LSeries.not_differentiableOn_of_LSeriesHasSum_recipZetaEulerLogCoeff`: Euler-logarithm
  whole-line nonvanishing sharpness.

## References

* G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*, Cambridge University Press,
  1915.
* A. E. Ingham, *The Distribution of Prime Numbers*, Cambridge University Press, 1932, Chapter II.
* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87 (1980),
  693–696.
-/

public section

open ArithmeticFunction Complex Filter Finset MeasureTheory Set
open scoped Topology Interval

namespace TauCeti.LSeries

/-! ### Step correction of `1` and partial-sum asymptotics of `riemannZeta` -/

/-- On `0 < re z`, the Laplace transform of the constant function `1` on `[0, ∞)` is `z⁻¹`. -/
private theorem integral_Ici_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), cexp (-z * t) = z⁻¹ := by
  have hre : (-z).re < 0 := by simpa using hz
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi hre 0]
  simp [div_eq_mul_inv, inv_neg]

/-- **The step correction of constant coefficients `1`.** On `-1 < re z`,
`stepCorrection 1 z = -riemannZeta₀ (z + 1)`, where `riemannZeta₀` is the entire completion of
`ζ(s) - (s - 1)⁻¹`. -/
theorem stepCorrection_one_eq_neg_riemannZeta₀ {z : ℂ} (hz : -1 < z.re) :
    stepCorrection 1 z = -riemannZeta₀ (z + 1) := by
  have hbound : ∀ n : ℕ, 1 ≤ n → ‖(1 : ℕ → ℂ) n‖ ≤ 1 := fun _ _ ↦ by simp
  have hdiff₁ : DifferentiableOn ℂ (stepCorrection 1) {w : ℂ | -1 < w.re} :=
    differentiableOn_stepCorrection hbound
  have hdiff₂ : DifferentiableOn ℂ (fun w : ℂ ↦ -riemannZeta₀ (w + 1)) {w : ℂ | -1 < w.re} :=
    (differentiable_riemannZeta₀.comp (differentiable_id.add_const 1)).neg.differentiableOn
  refine hdiff₁.eqOn_of_eqOn_re_gt hdiff₂ (b := 0) (fun w (hw : 0 < w.re) ↦ ?_) hz
  have hlap := integral_floor_exp_mul_cexp_neg_mul hbound (z := w) hw
  simp only [Pi.one_apply, one_mul] at hlap
  have hw1 : w + 1 ≠ 1 := fun h ↦ by
    have hw0 : w = 0 := by simpa using h
    simp [hw0] at hw
  rw [integral_Ici_cexp_neg_mul hw, LSeries_one_eq_riemannZeta (by simpa using hw),
    riemannZeta_eq_inv_sub_add hw1, add_sub_cancel_right] at hlap
  linear_combination -hlap

/-- At `z = 0`, the step correction `∑' n, (log (1 + 1 / n) - 1 / n)` equals `-γ`. -/
theorem stepCorrection_one_zero :
    stepCorrection 1 0 = -(Real.eulerMascheroniConstant : ℂ) := by
  rw [stepCorrection_one_eq_neg_riemannZeta₀ (by norm_num), zero_add, riemannZeta₀_one]

/-- On `-1 < re z` away from `z = 0`, `riemannZeta (z + 1)` equals `z⁻¹ - stepCorrection 1 z`. -/
theorem riemannZeta_eq_inv_sub_stepCorrection_one {z : ℂ} (hz : -1 < z.re) (hz₀ : z ≠ 0) :
    riemannZeta (z + 1) = z⁻¹ - stepCorrection 1 z := by
  have hz1 : z + 1 ≠ 1 := fun h ↦ hz₀ (by simpa using h)
  rw [riemannZeta_eq_inv_sub_add hz1, stepCorrection_one_eq_neg_riemannZeta₀ hz,
    add_sub_cancel_right, sub_neg_eq_add]

/-- Finite Euler–Maclaurin identity at cutoff `N + 1`: for `z ≠ 0`, the partial sum of
`n ^ (-(z + 1))` over `1 ≤ n ≤ N` minus `(N + 1) ^ (-z) / (-z)` equals `z⁻¹` minus the partial sum
of `stepCorrectionTerm 1 · z`. -/
private theorem sum_Icc_cpow_neg_add_one_sub {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(z + 1))) - (N + 1 : ℂ) ^ (-z) / (-z) =
      z⁻¹ - ∑ n ∈ Finset.range (N + 1), stepCorrectionTerm 1 n z := by
  have hstep := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ 1 N z
  simp only [Pi.one_apply, one_mul, Finset.sum_add_distrib] at hstep
  have hint : ∫ t in (0 : ℝ)..Real.log (N + 1), cexp (-z * t) =
      ((N + 1 : ℂ) ^ (-z) - 1) / (-z) := by
    rw [integral_exp_mul_complex (neg_ne_zero.mpr hz)]
    have hpos : (0 : ℝ) < N + 1 := by positivity
    have hpow : cexp (-z * (Real.log (N + 1) : ℂ)) = (N + 1 : ℂ) ^ (-z) := by
      rw [cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), mul_comm (-z),
        ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_log hpos.le]
    rw [hpow]
    simp
  have hsum : ∑ n ∈ Finset.range (N + 1), LSeries.term 1 (z + 1) n =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(z + 1)) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot N.succ_pos, LSeries.term_zero,
      zero_add, Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0, Pi.one_apply, one_div, cpow_neg]
  rw [hint, hsum] at hstep
  have hdiv : ((N + 1 : ℂ) ^ (-z) - 1) / (-z) = (N + 1 : ℂ) ^ (-z) / (-z) + z⁻¹ := by
    rw [sub_div, one_div, inv_neg, sub_neg_eq_add]
  rw [hdiv] at hstep
  linear_combination -hstep

/-- **Partial-sum asymptotic of `riemannZeta` on `0 < re s`, `s ≠ 1` (shifted cutoff `N + 1`).** -/
theorem tendsto_sum_Icc_cpow_neg_sub_succ_riemannZeta {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) -
      (N + 1 : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 (riemannZeta s)) := by
  have hz : -1 < (s - 1).re := by simp; linarith
  have hz₀ : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  have hbound : ∀ n : ℕ, 1 ≤ n → ‖(1 : ℕ → ℂ) n‖ ≤ 1 := fun _ _ ↦ by simp
  have hcorr := ((hasSum_stepCorrection (z := s - 1) hbound hz).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have hlim := tendsto_const_nhds (x := (s - 1)⁻¹).sub hcorr
  have hζ : (s - 1)⁻¹ - stepCorrection 1 (s - 1) = riemannZeta s := by
    have h := riemannZeta_eq_inv_sub_stepCorrection_one hz hz₀
    rw [sub_add_cancel] at h
    exact h.symm
  rw [hζ] at hlim
  refine hlim.congr fun N ↦ ?_
  have hN := sum_Icc_cpow_neg_add_one_sub hz₀ N
  have hexp₁ : -(s - 1 + 1) = -s := by ring
  have hexp₂ : -(s - 1) = 1 - s := by ring
  simp only [Function.comp_apply]
  rw [hexp₁, hexp₂] at hN
  exact hN.symm

/-- For `0 < re s` and `s ≠ 1`, the endpoint shift `((N + 1) ^ (1 - s) - N ^ (1 - s)) / (1 - s)`
tends to `0` as `N → ∞`. -/
private theorem tendsto_succ_cpow_sub_div_atTop {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    Tendsto (fun N : ℕ ↦ ((N + 1 : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s))
      atTop (𝓝 0) := by
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  refine squeeze_zero_norm' (a := fun N : ℕ ↦ (N : ℝ) ^ (-s.re)) ?_
    ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- Express `((N + 1) ^ (1 - s) - N ^ (1 - s)) / (1 - s)` as `∫ x in N..N+1, x ^ (-s)`.
  have hint_eq : ((N + 1 : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) =
      ∫ x in (N : ℝ)..N + 1, (x : ℂ) ^ (-s) := by
    have hsub := TauCeti.intervalIntegral_ofReal_cpow_neg_sub_one hN_pos (v := N + 1)
      (by positivity) (s - 1)
    have hexp : -(s - 1) - 1 = -s := by ring
    have hexp' : -(s - 1) = 1 - s := by ring
    rw [hexp, hexp'] at hsub
    rw [hsub, integral_exp_mul_complex h1s]
    have hpow₁ : cexp ((1 - s) * (Real.log (N + 1) : ℂ)) = (N + 1 : ℂ) ^ (1 - s) := by
      have hp : (0 : ℝ) < N + 1 := by positivity
      rw [cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), mul_comm (1 - s),
        ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_log hp.le]
    have hpow₂ : cexp ((1 - s) * (Real.log N : ℂ)) = (N : ℂ) ^ (1 - s) := by
      rw [cpow_def_of_ne_zero (by exact_mod_cast hN_pos.ne'), mul_comm (1 - s),
        ← ofReal_natCast, ← ofReal_log hN_pos.le]
    rw [hpow₁, hpow₂]
  rw [hint_eq]
  have hbound : ∀ x ∈ Ι (N : ℝ) (N + 1), ‖(x : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ (-s.re) := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hx_pos : 0 < x := hN_pos.trans hx.1
    rw [norm_cpow_eq_rpow_re_of_pos hx_pos, neg_re]
    exact Real.rpow_le_rpow_of_nonpos hN_pos hx.1.le (neg_nonpos.mpr hs.le)
  calc ‖∫ x in (N : ℝ)..N + 1, (x : ℂ) ^ (-s)‖
      ≤ (N : ℝ) ^ (-s.re) * |(N + 1 : ℝ) - N| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = (N : ℝ) ^ (-s.re) := by simp

/-- **Partial-sum asymptotic of `riemannZeta` on `0 < re s`, `s ≠ 1`.** For every `s` in the right
half-plane `0 < re s` other than the pole `s = 1`,
`(∑ n ∈ Icc 1 N, n ^ (-s)) - N ^ (1 - s) / (1 - s)` converges to `riemannZeta s` as `N → ∞`. -/
theorem tendsto_sum_Icc_cpow_neg_sub_riemannZeta {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) -
      (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 (riemannZeta s)) := by
  have h := (tendsto_sum_Icc_cpow_neg_sub_succ_riemannZeta hs hs₁).add
    (tendsto_succ_cpow_sub_div_atTop hs hs₁)
  rw [add_zero] at h
  refine h.congr fun N ↦ ?_
  ring

/-! ### Bounded Laplace boundary sharpness (`t ↦ exp (u * I * t)`) -/

/-- On `0 < re z`, the Laplace transform of `t ↦ exp (u * I * t)` on `[0, ∞)` is `(z - u * I)⁻¹`. -/
theorem integral_Ici_cexp_mul_I_mul_cexp_neg_mul (u : ℝ) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), cexp ((u : ℂ) * I * t) * cexp (-z * t) = (z - (u : ℂ) * I)⁻¹ := by
  have hcongr : ∀ t : ℝ, cexp ((u : ℂ) * I * t) * cexp (-z * t) =
      cexp (((u : ℂ) * I - z) * t) := fun t ↦ by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hcongr]
  have hre : ((u : ℂ) * I - z).re < 0 := by
    simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      zero_sub, neg_lt_zero]
    exact hz
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi hre 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div, ← inv_neg, neg_sub]

/-- For `u ≠ 0`, the Laplace transform of `t ↦ exp (u * I * t)` is analytic at every boundary point
of `re z = 0` other than `u * I` — in particular at `z = 0`, where its continuation `(z - u * I)⁻¹`
takes the nonzero value `I / u` — and has radial Abel limit `I / u` as `σ → 0⁺`. -/
theorem tendsto_integral_Ici_cexp_mul_I_nhdsGT_zero {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun σ : ℝ ↦ ∫ t in Ici (0 : ℝ), cexp ((u : ℂ) * I * t) * cexp (-(σ : ℂ) * t))
      (𝓝[>] 0) (𝓝 (I / u)) := by
  have huI : (0 : ℂ) - (u : ℂ) * I ≠ 0 := by
    simp [hu]
  have hcont : ContinuousAt (fun z : ℂ ↦ (z - (u : ℂ) * I)⁻¹) 0 :=
    (continuousAt_id.sub continuousAt_const).inv₀ huI
  have hval : ((0 : ℂ) - (u : ℂ) * I)⁻¹ = I / u := by
    have hu' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
    rw [zero_sub, inv_neg]
    field_simp [hu']
    simp
  have hlim : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - (u : ℂ) * I)⁻¹) (𝓝[>] 0) (𝓝 (I / u)) := by
    rw [← hval]
    exact (hcont.tendsto.comp continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 0 < σ)
  exact (integral_Ici_cexp_mul_I_mul_cexp_neg_mul u (by simpa using hσ)).symm

/-- **Divergence of the truncated integrals of `t ↦ exp (u * I * t)` (`u ≠ 0`).** Even though
`t ↦ exp (u * I * t)` has norm `1` everywhere and its Laplace transform extends analytically across
every point of `re z = 0` except `u * I` (including `z = 0`, with radial limit `I / u`), the
truncated integrals `∫ t in 0..T, exp (u * I * t)` have no finite limit as `T → ∞`. -/
theorem not_tendsto_intervalIntegral_cexp_mul_I {u : ℝ} (hu : u ≠ 0) {L : ℂ} :
    ¬ Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, cexp ((u : ℂ) * I * t)) atTop (𝓝 L) := by
  intro h
  have hc : (u : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hu) I_ne_zero
  have hre : 0 ≤ ((u : ℂ) * I).re := by simp
  have hexp : Tendsto (fun T : ℝ ↦ cexp (((u : ℂ) * I) * T)) atTop
      (𝓝 (L * ((u : ℂ) * I) + 1)) := by
    have hmul := (h.mul_const ((u : ℂ) * I)).add_const 1
    refine hmul.congr fun T ↦ ?_
    rw [integral_exp_mul_complex hc, ofReal_zero, mul_zero, Complex.exp_zero,
      div_mul_cancel₀ _ hc, sub_add_cancel]
  exact TauCeti.not_tendsto_exp_mul_ofReal_atTop hre hc hexp

/-- No function agreeing with the Laplace transform of `t ↦ exp (u * I * t)` on `0 < re z` can be
continuous on the entire closed right half-plane `0 ≤ re z`: its norm blows up along
`σ + u * I` as `σ → 0⁺`. -/
theorem not_continuousOn_of_eq_integral_Ici_cexp_mul_I (u : ℝ) {G : ℂ → ℂ}
    (hLaplace : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Ici (0 : ℝ), cexp ((u : ℂ) * I * t) * cexp (-z * t)) :
    ¬ ContinuousOn G {z : ℂ | 0 ≤ z.re} := by
  intro hG
  have hmem : (u : ℂ) * I ∈ {z : ℂ | 0 ≤ z.re} := by simp
  have hpath : Tendsto (fun σ : ℝ ↦ (σ : ℂ) + (u : ℂ) * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.re}] ((u : ℂ) * I)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using
        ((continuous_ofReal.tendsto 0).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 0 < σ)
      simpa using hσ.le
  have hlim : Tendsto (fun σ : ℝ ↦ ‖G ((σ : ℂ) + (u : ℂ) * I)‖) (𝓝[>] 0)
      (𝓝 ‖G ((u : ℂ) * I)‖) :=
    ((hG _ hmem).tendsto.comp hpath).norm
  have hblow : Tendsto (fun σ : ℝ ↦ ‖G ((σ : ℂ) + (u : ℂ) * I)‖) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 0 < σ)
    rw [hLaplace _ (by simpa using hσ), integral_Ici_cexp_mul_I_mul_cexp_neg_mul u (by simpa),
      add_sub_cancel_right, norm_inv, norm_real, Real.norm_of_nonneg hσ.le]
  exact not_tendsto_nhds_of_tendsto_atTop hblow _ hlim

/-- No function agreeing with the Laplace transform of `t ↦ exp (u * I * t)` on `0 < re z` is
holomorphic on an open neighbourhood of the closed half-plane `0 ≤ re z`. -/
theorem not_differentiableOn_of_eq_integral_Ici_cexp_mul_I (u : ℝ) {Ω : Set ℂ}
    (hcover : {z : ℂ | 0 ≤ z.re} ⊆ Ω) {G : ℂ → ℂ}
    (hLaplace : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Ici (0 : ℝ), cexp ((u : ℂ) * I * t) * cexp (-z * t)) :
    ¬ DifferentiableOn ℂ G Ω := fun hG ↦
  not_continuousOn_of_eq_integral_Ici_cexp_mul_I u hLaplace (hG.continuousOn.mono hcover)

/-! ### Bounded Dirichlet boundary sharpness (`n ↦ n ^ (u * I)`) -/

/-- For `1 ≤ n`, the coefficient `(n : ℂ) ^ (u * I)` has norm `1`. -/
theorem norm_natCast_cpow_mul_I (u : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ ((u : ℂ) * I)‖ = 1 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hn_pos]
  simp

/-- On `1 < re s`, the Dirichlet series of `n ↦ (n : ℂ) ^ (u * I)` sums to
`riemannZeta (s - u * I)`. -/
theorem LSeriesHasSum_natCast_cpow_mul_I (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) s (riemannZeta (s - (u : ℂ) * I)) := by
  have hs' : 1 < (s - (u : ℂ) * I).re := by simpa using hs
  have h1 : LSeriesHasSum (1 : ℕ → ℂ) (s - (u : ℂ) * I) (riemannZeta (s - (u : ℂ) * I)) := by
    rw [← LSeries_one_eq_riemannZeta hs']
    exact (LSeriesSummable_one_iff.mpr hs').LSeriesHasSum
  simpa using (LSeriesHasSum_mul_natCast_cpow_iff (1 : ℕ → ℂ) ((u : ℂ) * I) s
    (riemannZeta (s - (u : ℂ) * I))).mpr h1

/-- The continuation `w ↦ riemannZeta (w - u * I)` of `LSeries (n ^ (u * I))` is analytic at every
point `s ≠ 1 + u * I` — in particular at every point of `re s = 1` except `1 + u * I`. -/
theorem analyticAt_riemannZeta_sub_mul_I (u : ℝ) {s : ℂ} (hs : s ≠ 1 + (u : ℂ) * I) :
    AnalyticAt ℂ (fun w : ℂ ↦ riemannZeta (w - (u : ℂ) * I)) s := by
  have hne : s - (u : ℂ) * I ∈ ({1} : Set ℂ)ᶜ :=
    mem_compl_singleton_iff.mpr fun h ↦ hs (by linear_combination h)
  exact AnalyticAt.comp (f := fun w : ℂ ↦ w - (u : ℂ) * I)
    (analyticOn_riemannZeta _ hne) (analyticAt_id.sub analyticAt_const)

/-- **Radial Abel limit for `n ↦ n ^ (u * I)` (`u ≠ 0`).** As `σ → 1⁺`, the `L`-series of
`n ↦ (n : ℂ) ^ (u * I)` converges to the nonzero boundary value `riemannZeta (1 - u * I)`. -/
theorem tendsto_LSeries_natCast_cpow_mul_I_nhdsGT_one {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun σ : ℝ ↦ LSeries (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) σ) (𝓝[>] 1)
      (𝓝 (riemannZeta (1 - (u : ℂ) * I))) := by
  have h1 : (1 : ℂ) ≠ 1 + (u : ℂ) * I := by simp [hu]
  have hlim : Tendsto (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) - (u : ℂ) * I)) (𝓝[>] 1)
      (𝓝 (riemannZeta (1 - (u : ℂ) * I))) :=
    (((analyticAt_riemannZeta_sub_mul_I u h1).continuousAt.tendsto.comp
      (continuous_ofReal.tendsto 1)).mono_left nhdsWithin_le_nhds)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  exact (LSeriesHasSum_natCast_cpow_mul_I u (by simpa using hσ)).LSeries_eq.symm

/-- **Boundary asymptotic of the ordered harmonic sums of `n ^ (u * I)` (`u ≠ 0`).** Subtracting
the oscillatory main term `N ^ (u * I) / (u * I)` from `∑ n ∈ Icc 1 N, n ^ (u * I) / n` yields a
convergent sequence with limit `riemannZeta (1 - u * I)`. -/
theorem tendsto_sum_Icc_natCast_cpow_mul_I_div_sub {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ)) -
      (N : ℂ) ^ ((u : ℂ) * I) / ((u : ℂ) * I)) atTop (𝓝 (riemannZeta (1 - (u : ℂ) * I))) := by
  have hs_re : 0 < ((1 : ℂ) - (u : ℂ) * I).re := by simp
  have hs₁ : (1 : ℂ) - (u : ℂ) * I ≠ 1 := by simp [hu]
  have h := tendsto_sum_Icc_cpow_neg_sub_riemannZeta hs_re hs₁
  have hexp : (1 : ℂ) - ((1 : ℂ) - (u : ℂ) * I) = (u : ℂ) * I := by ring
  rw [hexp] at h
  refine h.congr fun N ↦ ?_
  congr 1
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)
  have hneg : -((1 : ℂ) - (u : ℂ) * I) = (u : ℂ) * I - 1 := by ring
  rw [hneg, sub_eq_add_neg, cpow_add _ _ hn0, cpow_neg_one, div_eq_mul_inv]

/-- **Divergence of the ordered partial sums `∑ n ∈ Icc 1 N, n ^ (u * I) / n` (`u ≠ 0`).**
Although the coefficients have norm `1` for `n ≥ 1` and their `L`-series extends analytically
across `s = 1` with finite nonzero radial Abel limit `riemannZeta (1 - u * I)`, the ordered partial
sums at `s = 1` fail to converge. In particular:
1. `boundedDirichlet_tendsto_ordered_at_one_of_analyticAt` fails when analyticity omits the single
   off-real boundary point `1 + u * I`;
2. `tendsto_LSeries_nhdsGT_one` admits no bounded-coefficient Tauberian converse from radial
   convergence at `1⁺` (or even analyticity in a disc around `1`) alone. -/
theorem not_tendsto_sum_Icc_natCast_cpow_mul_I_div {u : ℝ} (hu : u ≠ 0) {L : ℂ} :
    ¬ Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ))
      atTop (𝓝 L) := by
  intro h
  have huI : (u : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hu) I_ne_zero
  have hre : 0 ≤ ((u : ℂ) * I).re := by simp
  have hosc : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ ((u : ℂ) * I)) atTop
      (𝓝 ((L - riemannZeta (1 - (u : ℂ) * I)) * ((u : ℂ) * I))) := by
    have hsub := (h.sub (tendsto_sum_Icc_natCast_cpow_mul_I_div_sub hu)).mul_const ((u : ℂ) * I)
    refine hsub.congr fun N ↦ ?_
    rw [sub_sub_cancel, div_mul_cancel₀ _ huI]
  exact TauCeti.not_tendsto_natCast_cpow_atTop hre huI hosc

/-- No function summing the Dirichlet series of `n ↦ (n : ℂ) ^ (u * I)` on `1 < re s` is continuous
on the entire closed half-plane `1 ≤ re s`: its norm tends to `+∞` along `σ + u * I` as
`σ → 1⁺`. -/
theorem not_continuousOn_of_LSeriesHasSum_natCast_cpow_mul_I (u : ℝ) {F : ℂ → ℂ}
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) s (F s)) :
    ¬ ContinuousOn F {s : ℂ | 1 ≤ s.re} := by
  intro hF
  set s₀ : ℂ := 1 + (u : ℂ) * I
  have hs₀ : s₀ ∈ {s : ℂ | 1 ≤ s.re} := by simp [s₀]
  have hpath : Tendsto (fun σ : ℝ ↦ (σ : ℂ) + (u : ℂ) * I) (𝓝[>] 1)
      (𝓝[{s : ℂ | 1 ≤ s.re}] s₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa [s₀] using
        (((continuous_ofReal.tendsto 1).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      simpa using hσ.le
  -- Along `σ + u * I`, `F (σ + u * I) = ζ(σ) = (σ - 1)⁻¹ + riemannZeta₀ σ`, whose singular part
  -- blows up while `riemannZeta₀ σ → riemannZeta₀ 1`.
  have hsub : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1)⁻¹) (𝓝[>] 1)
      (𝓝 (F s₀ - riemannZeta₀ 1 + 0)) := by
    have hFσ : Tendsto (fun σ : ℝ ↦ F ((σ : ℂ) + (u : ℂ) * I) - riemannZeta₀ σ) (𝓝[>] 1)
        (𝓝 (F s₀ - riemannZeta₀ 1)) :=
      (((hF _ hs₀).tendsto.comp hpath).sub
        ((differentiable_riemannZeta₀.continuous.tendsto 1).comp
          (continuous_ofReal.tendsto 1) |>.mono_left nhdsWithin_le_nhds))
    simpa using hFσ.congr' (by
      filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      have hFs := (hseries ((σ : ℂ) + (u : ℂ) * I) (by simpa using hσ)).unique
        (LSeriesHasSum_natCast_cpow_mul_I u (by simpa using hσ))
      have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
      rw [hFs, add_sub_cancel_right, riemannZeta_eq_inv_sub_add hne, add_sub_cancel_right])
  have hblow : Tendsto (fun σ : ℝ ↦ ‖((σ : ℂ) - 1)⁻¹‖) (𝓝[>] 1) atTop := by
    have hshift : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝[>] 1) (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with σ hσ using sub_pos.mpr hσ)
    refine (tendsto_inv_nhdsGT_zero.comp hshift).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [Function.comp_apply, norm_inv, ← ofReal_one, ← ofReal_sub, norm_real,
      Real.norm_of_nonneg (sub_pos.mpr hσ).le]
  exact not_tendsto_nhds_of_tendsto_atTop hblow _ hsub.norm

/-- No function summing the Dirichlet series of `n ↦ (n : ℂ) ^ (u * I)` on `1 < re s` is
holomorphic on an open neighbourhood of the closed half-plane `1 ≤ re s`. -/
theorem not_differentiableOn_of_LSeriesHasSum_natCast_cpow_mul_I (u : ℝ) {Ω : Set ℂ}
    (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω) {F : ℂ → ℂ}
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) s (F s)) :
    ¬ DifferentiableOn ℂ F Ω := fun hF ↦
  not_continuousOn_of_LSeriesHasSum_natCast_cpow_mul_I u hseries (hF.continuousOn.mono hcover)

/-! ### Imaginary-shifted reciprocal-zeta Euler logarithm: whole-line nonvanishing sharpness -/

/-- The entire regularized factor `riemannZeta₁` of `(s - 1) ζ(s)` has no zeros on the closed
half-plane `1 ≤ re s`: at `s = 1` it equals `1`, and away from `s = 1` it is `(s - 1) ζ(s)`. -/
theorem riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp
  · intro h0
    exact riemannZeta_ne_zero_of_one_le_re hs (by rw [riemannZeta_eq_inv_sub_mul hs₁, h0, mul_zero])

/-- The coefficients `-(Λ n / log n) * n ^ (u * I)` of the logarithm of the shifted reciprocal
Euler product `∏ p, (1 - p ^ (u * I) * p ^ (-s)) = (ζ(s - u * I))⁻¹` on `1 < re s`. -/
noncomputable def recipZetaEulerLogCoeff (u : ℝ) (n : ℕ) : ℂ :=
  -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)

/-- Defining formula for `recipZetaEulerLogCoeff`. -/
theorem recipZetaEulerLogCoeff_apply (u : ℝ) (n : ℕ) :
    recipZetaEulerLogCoeff u n = -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I) := by
  rfl

/-- Express `recipZetaEulerLogCoeff u` as the negative `n ^ (u * I)`-twist of the level-`1`
Euler-logarithm coefficients `(1 : DirichletCharacter ℂ 1).eulerLogCoeff`. -/
private theorem recipZetaEulerLogCoeff_eq_neg_eulerLogCoeff_mul_cpow (u : ℝ) (n : ℕ) :
    recipZetaEulerLogCoeff u n =
      -((1 : DirichletCharacter ℂ 1).eulerLogCoeff n * (n : ℂ) ^ ((u : ℂ) * I)) := by
  simp [recipZetaEulerLogCoeff, DirichletCharacter.eulerLogCoeff_apply,
    MulChar.one_apply (isUnit_of_subsingleton _)]

/-- At `n = 0`, `recipZetaEulerLogCoeff u 0 = 0`. -/
@[simp]
theorem recipZetaEulerLogCoeff_zero (u : ℝ) : recipZetaEulerLogCoeff u 0 = 0 := by
  simp [recipZetaEulerLogCoeff]

/-- At `n = 1`, `recipZetaEulerLogCoeff u 1 = 0`. -/
@[simp]
theorem recipZetaEulerLogCoeff_one (u : ℝ) : recipZetaEulerLogCoeff u 1 = 0 := by
  simp [recipZetaEulerLogCoeff]

/-- `recipZetaEulerLogCoeff u` vanishes off prime powers. -/
theorem recipZetaEulerLogCoeff_eq_zero_of_not_isPrimePow (u : ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    recipZetaEulerLogCoeff u n = 0 := by
  rw [recipZetaEulerLogCoeff_eq_neg_eulerLogCoeff_mul_cpow,
    DirichletCharacter.eulerLogCoeff_eq_zero_of_not_isPrimePow _ hn, zero_mul, neg_zero]

/-- At a prime power `p ^ k`, `recipZetaEulerLogCoeff u (p ^ k) = -((p ^ (u * I)) ^ k / k)`
(for `k = 0` both sides are `0`). -/
theorem recipZetaEulerLogCoeff_prime_pow (u : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    recipZetaEulerLogCoeff u (p ^ k) = -(((p : ℂ) ^ ((u : ℂ) * I)) ^ k / k) := by
  rw [recipZetaEulerLogCoeff_eq_neg_eulerLogCoeff_mul_cpow,
    DirichletCharacter.eulerLogCoeff_prime_pow _ hp,
    MulChar.one_apply (isUnit_of_subsingleton _), one_pow]
  have hpow : ((p ^ k : ℕ) : ℂ) ^ ((u : ℂ) * I) = ((p : ℂ) ^ ((u : ℂ) * I)) ^ k := by
    rw [TauCeti.natCast_cpow_ofReal_mul (pow_ne_zero k hp.ne_zero) u I,
      TauCeti.natCast_cpow_ofReal_mul hp.ne_zero u I, ← Complex.exp_nat_mul]
    congr 1
    simp only [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [hpow]
  ring

/-- At a prime `p`, `recipZetaEulerLogCoeff u p = -p ^ (u * I)`. -/
@[simp]
theorem recipZetaEulerLogCoeff_prime (u : ℝ) {p : ℕ} (hp : p.Prime) :
    recipZetaEulerLogCoeff u p = -(p : ℂ) ^ ((u : ℂ) * I) := by
  simpa using recipZetaEulerLogCoeff_prime_pow u hp 1

/-- Every coefficient `recipZetaEulerLogCoeff u n` has norm at most `1`. -/
theorem norm_recipZetaEulerLogCoeff_le_one (u : ℝ) (n : ℕ) :
    ‖recipZetaEulerLogCoeff u n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [recipZetaEulerLogCoeff_eq_neg_eulerLogCoeff_mul_cpow, norm_neg, norm_mul,
    norm_natCast_cpow_mul_I u (Nat.one_le_iff_ne_zero.mpr hn), mul_one]
  exact DirichletCharacter.norm_eulerLogCoeff_le_one _ n

/-- The `L`-series of `recipZetaEulerLogCoeff u` converges absolutely on `1 < re s`. -/
theorem LSeriesSummable_recipZetaEulerLogCoeff (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (recipZetaEulerLogCoeff u) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ ↦ norm_recipZetaEulerLogCoeff_le_one u n) hs

/-- The `L`-series of `recipZetaEulerLogCoeff u` is holomorphic on `1 < re s`. -/
theorem differentiableOn_LSeries_recipZetaEulerLogCoeff (u : ℝ) :
    DifferentiableOn ℂ (LSeries (recipZetaEulerLogCoeff u)) {s : ℂ | 1 < s.re} :=
  (LSeries_differentiableOn _).mono fun s (hs : 1 < s.re) ↦
    (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ ↦
      norm_recipZetaEulerLogCoeff_le_one u n⟩).trans_lt (mod_cast hs)

/-- On `1 < re s`, `exp (LSeries (recipZetaEulerLogCoeff u) s) = (riemannZeta (s - u * I))⁻¹`. -/
theorem exp_LSeries_recipZetaEulerLogCoeff (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries (recipZetaEulerLogCoeff u) s) = (riemannZeta (s - (u : ℂ) * I))⁻¹ := by
  have hs' : 1 < (s - (u : ℂ) * I).re := by simpa using hs
  have hfn : recipZetaEulerLogCoeff u =
      -(fun n : ℕ ↦ (Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) :=
    funext fun n ↦ by simp [recipZetaEulerLogCoeff]
  rw [hfn, LSeries_neg, LSeries_mul_natCast_cpow, Complex.exp_neg,
    riemannZeta_eq_exp_LSeries hs']

/-- On `1 < re s`, `exp (LSeries (recipZetaEulerLogCoeff u) s)` agrees with the regularized
reciprocal `(s - 1 - u * I) * (riemannZeta₁ (s - u * I))⁻¹`, which is holomorphic on an open
neighbourhood of the entire closed half-plane `1 ≤ re s`. -/
theorem exp_LSeries_recipZetaEulerLogCoeff_eq_sub_mul (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries (recipZetaEulerLogCoeff u) s) =
      (s - 1 - (u : ℂ) * I) * (riemannZeta₁ (s - (u : ℂ) * I))⁻¹ := by
  have hne : s - (u : ℂ) * I ≠ 1 := fun h ↦ by
    have : (s - (u : ℂ) * I).re = 1 := congrArg re h
    simp at this
    linarith
  rw [exp_LSeries_recipZetaEulerLogCoeff u hs, inv_riemannZeta_eq_sub_mul_of_ne_one hne]
  ring

/-- The nonvanishing locus `{s | riemannZeta₁ (s - u * I) ≠ 0}` is open in `ℂ`. -/
private theorem isOpen_riemannZeta₁_sub_ne_zero (u : ℝ) :
    IsOpen {s : ℂ | riemannZeta₁ (s - (u : ℂ) * I) ≠ 0} :=
  isOpen_ne_fun (differentiable_riemannZeta₁.continuous.comp (continuous_id.sub continuous_const))
    continuous_const

/-- The regularized reciprocal `s ↦ (s - 1 - u * I) * (riemannZeta₁ (s - u * I))⁻¹` is holomorphic
on the open set `{s | riemannZeta₁ (s - u * I) ≠ 0}`, which contains the entire closed half-plane
`1 ≤ re s`. -/
theorem differentiableOn_sub_mul_inv_riemannZeta₁ (u : ℝ) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (s - 1 - (u : ℂ) * I) * (riemannZeta₁ (s - (u : ℂ) * I))⁻¹)
      {s : ℂ | riemannZeta₁ (s - (u : ℂ) * I) ≠ 0} := by
  refine ((differentiableOn_id.sub_const 1).sub_const _).mul ?_
  exact ((differentiable_riemannZeta₁.comp (differentiable_id.sub_const _)).differentiableOn).inv
    fun _ hs ↦ hs

/-- At every point `s₀` with `1 ≤ re s₀` and `s₀ ≠ 1 + u * I`, the regularized reciprocal
`s ↦ (s - 1 - u * I) * (riemannZeta₁ (s - u * I))⁻¹` is analytic at `s₀`, equals
`(riemannZeta (s₀ - u * I))⁻¹`, and is nonzero. -/
private theorem analyticAt_and_eq_inv_riemannZeta {u : ℝ} {s₀ : ℂ} (hs₀ : 1 ≤ s₀.re)
    (hne : s₀ ≠ 1 + (u : ℂ) * I) :
    AnalyticAt ℂ (fun s : ℂ ↦ (s - 1 - (u : ℂ) * I) * (riemannZeta₁ (s - (u : ℂ) * I))⁻¹) s₀ ∧
      (s₀ - 1 - (u : ℂ) * I) * (riemannZeta₁ (s₀ - (u : ℂ) * I))⁻¹ =
        (riemannZeta (s₀ - (u : ℂ) * I))⁻¹ ∧
      (riemannZeta (s₀ - (u : ℂ) * I))⁻¹ ≠ 0 := by
  have hre : 1 ≤ (s₀ - (u : ℂ) * I).re := by simpa using hs₀
  have hmem : s₀ ∈ {s : ℂ | riemannZeta₁ (s - (u : ℂ) * I) ≠ 0} :=
    riemannZeta₁_ne_zero_of_one_le_re hre
  have hne' : s₀ - (u : ℂ) * I ≠ 1 := fun h ↦ hne (by linear_combination h)
  have heq : (s₀ - 1 - (u : ℂ) * I) * (riemannZeta₁ (s₀ - (u : ℂ) * I))⁻¹ =
      (riemannZeta (s₀ - (u : ℂ) * I))⁻¹ := by
    rw [inv_riemannZeta_eq_sub_mul_of_ne_one hne']
    ring
  exact ⟨(differentiableOn_sub_mul_inv_riemannZeta₁ u).analyticAt
    ((isOpen_riemannZeta₁_sub_ne_zero u).mem_nhds hmem),
    heq, inv_ne_zero (riemannZeta_ne_zero_of_one_le_re hre)⟩

/-- **Boundary analyticity of the shifted reciprocal-zeta Euler logarithm away from `1 + u * I`.**
At every point `s₀` on `re s₀ = 1` other than `1 + u * I`, `LSeries (recipZetaEulerLogCoeff u)`
agrees near `s₀` in `1 < re s` with a function `L` analytic at `s₀` satisfying
`exp (L s₀) = (riemannZeta (s₀ - u * I))⁻¹`. -/
theorem exists_analyticAt_LSeries_recipZetaEulerLogCoeff {u : ℝ} {s₀ : ℂ} (hs₀ : s₀.re = 1)
    (hne : s₀ ≠ 1 + (u : ℂ) * I) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L s₀ ∧ Complex.exp (L s₀) = (riemannZeta (s₀ - (u : ℂ) * I))⁻¹ ∧
      ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] s₀, L s = LSeries (recipZetaEulerLogCoeff u) s := by
  obtain ⟨hga, hgeq, hgnz⟩ := analyticAt_and_eq_inv_riemannZeta hs₀.ge hne
  obtain ⟨L, hLa, hLexp, hLf⟩ := TauCeti.exists_analyticAt_eq_exp_of_re_eq hs₀ hga
    (hgeq.symm ▸ hgnz) (differentiableOn_LSeries_recipZetaEulerLogCoeff u)
    (fun s hs ↦ exp_LSeries_recipZetaEulerLogCoeff_eq_sub_mul u hs)
  exact ⟨L, hLa, hLexp.self_of_nhds.trans hgeq, hLf⟩

/-- **Local analyticity of the shifted reciprocal-zeta Euler logarithm at `s = 1` (`u ≠ 0`).**
For `u ≠ 0`, `LSeries (recipZetaEulerLogCoeff u)` agrees near `1` in `1 < re s` with a function `L`
analytic at `1` satisfying `exp (L 1) = (riemannZeta (1 - u * I))⁻¹`. -/
theorem exists_analyticAt_one_LSeries_recipZetaEulerLogCoeff {u : ℝ} (hu : u ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 1 ∧ Complex.exp (L 1) = (riemannZeta (1 - (u : ℂ) * I))⁻¹ ∧
      ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] 1, L s = LSeries (recipZetaEulerLogCoeff u) s :=
  exists_analyticAt_LSeries_recipZetaEulerLogCoeff one_re (by simp [hu])

/-- **Finite radial Abel limit of the shifted reciprocal-zeta Euler logarithm at `1⁺` (`u ≠ 0`).**
As `σ → 1⁺`, `LSeries (recipZetaEulerLogCoeff u) σ` converges to a finite limit `w` with
`exp w = (riemannZeta (1 - u * I))⁻¹ ≠ 0`. -/
theorem exists_tendsto_LSeries_recipZetaEulerLogCoeff_nhdsGT_one {u : ℝ} (hu : u ≠ 0) :
    ∃ w : ℂ, Complex.exp w = (riemannZeta (1 - (u : ℂ) * I))⁻¹ ∧
      Tendsto (fun σ : ℝ ↦ LSeries (recipZetaEulerLogCoeff u) σ) (𝓝[>] 1) (𝓝 w) := by
  obtain ⟨hga, hgeq, hgnz⟩ :=
    analyticAt_and_eq_inv_riemannZeta (u := u) (s₀ := (1 : ℂ)) (by simp) (by simp [hu])
  obtain ⟨w, hw, hlim⟩ := TauCeti.exists_tendsto_nhdsWithin_Ioi_of_analyticAt_of_ne_zero (a := 1)
    (by simpa only [ofReal_one] using hga) (by rw [ofReal_one, hgeq]; exact hgnz)
    (differentiableOn_LSeries_recipZetaEulerLogCoeff u)
    (fun s hs ↦ exp_LSeries_recipZetaEulerLogCoeff_eq_sub_mul u hs)
  exact ⟨w, hw.trans (by rw [ofReal_one, hgeq]), hlim⟩

/-- **No continuous closed-half-plane extension of the shifted reciprocal-zeta Euler logarithm.**
For every `u : ℝ` (including `u ≠ 0`, where the exponentiated target is holomorphic on a
neighbourhood of `1 ≤ re s`, nonzero at every boundary point except `1 + u * I`, and the `L`-series
has a finite radial Abel limit at `1⁺`), no function `F` summing `recipZetaEulerLogCoeff u` on
`1 < re s` is continuous on the closed half-plane `1 ≤ re s`: the zero of the regularized
reciprocal at `1 + u * I` obstructs any continuous boundary extension of its logarithm. -/
theorem not_continuousOn_of_LSeriesHasSum_recipZetaEulerLogCoeff (u : ℝ) {F : ℂ → ℂ}
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (recipZetaEulerLogCoeff u) s (F s)) :
    ¬ ContinuousOn F {s : ℂ | 1 ≤ s.re} := by
  intro hF
  set g : ℂ → ℂ := fun s ↦ (s - 1 - (u : ℂ) * I) * (riemannZeta₁ (s - (u : ℂ) * I))⁻¹
  have hcover : {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | riemannZeta₁ (s - (u : ℂ) * I) ≠ 0} := fun s hs ↦
    riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs)
  have hFf : EqOn F (LSeries (recipZetaEulerLogCoeff u)) {s : ℂ | 1 < s.re} := fun s hs ↦
    (hseries s hs).LSeries_eq.symm
  have hnz := (TauCeti.exists_continuousOn_eqOn_le_re_iff (isOpen_riemannZeta₁_sub_ne_zero u) hcover
    (differentiableOn_sub_mul_inv_riemannZeta₁ u)
    (differentiableOn_LSeries_recipZetaEulerLogCoeff u)
    (fun s hs ↦ exp_LSeries_recipZetaEulerLogCoeff_eq_sub_mul u hs)).mp ⟨F, hF, hFf⟩
  have hzero : g (1 + (u : ℂ) * I) = 0 := by simp [g]
  exact hnz (1 + (u : ℂ) * I) (by simp) hzero

/-- **No holomorphic continuation of the shifted reciprocal-zeta Euler logarithm across
`re s = 1`.** Pointwise nonvanishing at `s = 1` and a finite radial Abel limit as `σ → 1⁺` (`u ≠ 0`)
do not suffice to continue the Euler logarithm across `re s = 1` when the target function vanishes
at `1 + u * I`. -/
theorem not_differentiableOn_of_LSeriesHasSum_recipZetaEulerLogCoeff (u : ℝ) {Ω : Set ℂ}
    (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω) {F : ℂ → ℂ}
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (recipZetaEulerLogCoeff u) s (F s)) :
    ¬ DifferentiableOn ℂ F Ω := fun hF ↦
  not_continuousOn_of_LSeriesHasSum_recipZetaEulerLogCoeff u hseries (hF.continuousOn.mono hcover)

end TauCeti.LSeries
