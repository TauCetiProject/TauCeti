/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.LogNorm
import TauCeti.Analysis.InnerProductSpace.Harmonic.Taylor
import TauCeti.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The exterior multipole expansion of the planar Newtonian kernel

In dimension two, the totalized Euclidean kernel `TauCeti.newtonianKernel 2` vanishes identically,
and the fundamental solution for `-Δ` on the plane is the logarithmic kernel
`TauCeti.planarNewtonianKernel`,

`G(z) = -(2 * π)⁻¹ * log ‖z‖`.

For a nonzero pole `x ∈ ℂ` and `‖y‖ < ‖x‖`, factoring `x - y = x * (1 - y / x)` and expanding
`-Complex.log (1 - y / x)` on the unit disk (`TauCeti.hasFPowerSeriesOnBall_neg_clog_one_sub`)
yields the **planar exterior multipole expansion**:

`G(x - y) = G(x) + ∑_{k ≥ 1} (2 * π * k)⁻¹ * Re ((y / x) ^ k)`.

Whereas `TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Multipole` produces an abstract power
series on a ball of radius `c ‖x‖` for an unspecified dimensional constant `0 < c < 1`, the complex
logarithm supplies an explicit multilinear series (`TauCeti.planarMultipoleSeries`), an explicit
holomorphic polynomial (`TauCeti.planarMultipolePolynomial`) whose real part gives the partial sums,
and the **sharp** convergence radius `‖x‖` (`TauCeti.radius_planarMultipoleSeries`,
`TauCeti.hasFPowerSeriesOnBall_planarNewtonianKernel_sub`).

Applying `HasFPowerSeriesOnBall.tendstoUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt` shows
that on every closed disk `closedBall 0 r` with `r < ‖x‖`, the partial sums converge uniformly
together with iterated derivatives of every order to `y ↦ G(x - y)`. Consequently, any continuous
linear functional on functions on `closedBall 0 r` for the `C^k` topology that annihilates global
harmonic polynomials also annihilates `y ↦ G(x - y)` for `‖x‖ > r`, supplying the exterior step in
the duality proof of harmonic Runge approximation in dimension two. Transporting along an
orthonormal identification with `ℂ` gives the corresponding sharp power series and global
harmonic-polynomial `C^k` approximation theorems for `y ↦ log ‖x - y‖` in two-dimensional real
inner product spaces and on `EuclideanSpace ℝ (Fin 2)`, pairing with
`TauCeti.harmonicAt_log_norm_sub_of_finrank_eq_two` and
`exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub`.

## Main declarations

* `TauCeti.planarMultipoleSeries`: the explicit real formal multilinear series of `y ↦ G(x - y)`
  about the origin, with constant term `G(x)` and degree-`(k + 1)` term
  `v ↦ (2 * π * (k + 1))⁻¹ * Re ((∏ i, v i) / x ^ (k + 1))`.
* `TauCeti.planarMultipolePolynomial`: the explicit complex polynomial of degree at most `N - 1`
  whose real part evaluates to `(planarMultipoleSeries x).partialSum N`.
* `TauCeti.hasFPowerSeriesOnBall_planarNewtonianKernel_sub` and
  `TauCeti.hasFPowerSeriesOnBall_planarNewtonianKernel`: power series representations on the sharp
  balls of radius `‖x‖` and `‖a‖`.
* `TauCeti.radius_planarMultipoleSeries`: the convergence radius of `planarMultipoleSeries x` is
  `‖x‖₊` for `x ≠ 0`.
* `TauCeti.tendstoUniformlyOn_iteratedFDeriv_planarMultipoleSeries_partialSum`: uniform convergence
  of all iterated derivatives of the multipole partial sums on every `closedBall 0 r` with
  `r < ‖x‖`.
* `TauCeti.exists_hasFPowerSeriesOnBall_log_norm_sub_of_finrank_eq_two`: sharp exterior multipole
  expansion of `y ↦ log ‖x - y‖` in any two-dimensional real inner product space.
* `TauCeti.exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_log_norm_sub`:
  approximation of `y ↦ log ‖x - y‖` on `EuclideanSpace ℝ (Fin 2)` by harmonic polynomials of
  degree at most `N`, uniformly with all derivatives on every `closedBall 0 r` with `r < ‖x‖`.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapters 5 and 10.
* O. D. Kellogg, *Foundations of Potential Theory*, Chapter V.
* T. Ransford, *Potential Theory in the Complex Plane*, §3.1.
-/

public section

noncomputable section

open Filter InnerProductSpace Metric Set Topology
open scoped NNReal ENNReal

namespace TauCeti

/-! ### The explicit multipole series on `ℂ` -/

/-- **The exterior multipole formal power series of the planar Newtonian kernel.**
For a pole `x : ℂ`, `planarMultipoleSeries x` is the real formal multilinear series at the origin
whose `0`-th term is `planarNewtonianKernel x` and whose `(k + 1)`-st term sends
`v : Fin (k + 1) → ℂ` to `(2 * π * (k + 1))⁻¹ * Re ((∏ i, v i) / x ^ (k + 1))`. At `x = 0` it is
the zero series. -/
def planarMultipoleSeries (x : ℂ) : FormalMultilinearSeries ℝ ℂ ℝ :=
  constFormalMultilinearSeries ℝ ℂ (planarNewtonianKernel x) +
    (((2 * Real.pi)⁻¹ • Complex.reCLM).compFormalMultilinearSeries
      ((FormalMultilinearSeries.ofScalars ℂ fun k : ℕ ↦ (k : ℂ)⁻¹).restrictScalars
        ℝ)).compContinuousLinearMap
      ((x⁻¹ • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)

/-- The defining decomposition of `planarMultipoleSeries`. -/
theorem planarMultipoleSeries_def (x : ℂ) :
    planarMultipoleSeries x =
      constFormalMultilinearSeries ℝ ℂ (planarNewtonianKernel x) +
        (((2 * Real.pi)⁻¹ • Complex.reCLM).compFormalMultilinearSeries
          ((FormalMultilinearSeries.ofScalars ℂ fun k : ℕ ↦ (k : ℂ)⁻¹).restrictScalars
            ℝ)).compContinuousLinearMap
          ((x⁻¹ • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ) :=
  (rfl)

/-- The degree-zero term of `planarMultipoleSeries x` is the constant `planarNewtonianKernel x`. -/
@[simp]
theorem planarMultipoleSeries_apply_zero (x : ℂ) (v : Fin 0 → ℂ) :
    planarMultipoleSeries x 0 v = planarNewtonianKernel x := by
  simp [planarMultipoleSeries_def, FormalMultilinearSeries.restrictScalars,
    FormalMultilinearSeries.ofScalars]

/-- In positive degree `k + 1`, `planarMultipoleSeries x` evaluates to
`(2 * π * (k + 1))⁻¹ * Re ((∏ i, v i) / x ^ (k + 1))`. -/
@[simp]
theorem planarMultipoleSeries_apply_succ (x : ℂ) (k : ℕ) (v : Fin (k + 1) → ℂ) :
    planarMultipoleSeries x (k + 1) v =
      (2 * Real.pi * (k + 1))⁻¹ * ((∏ i, v i) / x ^ (k + 1)).re := by
  have hprod : (∏ i : Fin (k + 1), x⁻¹ * v i) = (∏ i, v i) / x ^ (k + 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, inv_pow, div_eq_mul_inv,
      mul_comm]
  have hre (z : ℂ) : (((k : ℂ) + 1)⁻¹ * z).re = ((k : ℝ) + 1)⁻¹ * z.re := by
    rw [show ((k : ℂ) + 1)⁻¹ = (((k + 1 : ℝ)⁻¹ : ℝ) : ℂ) by simp, Complex.re_ofReal_mul]
  simp [-Complex.mul_re, -List.ofFn_succ, planarMultipoleSeries_def,
    FormalMultilinearSeries.restrictScalars, FormalMultilinearSeries.ofScalars, List.prod_ofFn,
    hprod, hre]
  ring

/-- On the diagonal, the `(k + 1)`-st multipole term is
`(2 * π * (k + 1))⁻¹ * Re ((y / x) ^ (k + 1))`. -/
theorem planarMultipoleSeries_apply_const_succ (x y : ℂ) (k : ℕ) :
    (planarMultipoleSeries x (k + 1) fun _ ↦ y) =
      (2 * Real.pi * (k + 1))⁻¹ * ((y / x) ^ (k + 1)).re := by
  simp [div_pow]

/-- At the origin, `planarMultipoleSeries 0` is the zero series. -/
@[simp]
theorem planarMultipoleSeries_zero : planarMultipoleSeries 0 = 0 := by
  ext k v
  cases k <;> simp

/-- For `N + 1` terms, the partial sum of `planarMultipoleSeries x` splits into the constant
`G(x)` and the harmonic modes `1 ≤ k ≤ N`. -/
theorem planarMultipoleSeries_partialSum_succ (x y : ℂ) (N : ℕ) :
    (planarMultipoleSeries x).partialSum (N + 1) y =
      planarNewtonianKernel x +
        ∑ k ∈ Finset.Ico 1 (N + 1), (2 * Real.pi * k)⁻¹ * ((y / x) ^ k).re := by
  rw [FormalMultilinearSeries.partialSum, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N),
    planarMultipoleSeries_apply_zero]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  cases k with
  | zero => simp at hk
  | succ m => simpa [Nat.cast_add, Nat.cast_one] using planarMultipoleSeries_apply_const_succ x y m

/-! ### The explicit holomorphic multipole polynomial -/

/-- **The holomorphic multipole polynomial of the planar Newtonian kernel.**
Its real part evaluates to `(planarMultipoleSeries x).partialSum N` at every point of `ℂ`. -/
def planarMultipolePolynomial (x : ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N,
    Polynomial.monomial k
      (if k = 0 then (planarNewtonianKernel x : ℂ)
      else ((2 * Real.pi * k : ℝ) : ℂ)⁻¹ * (x ^ k)⁻¹)

/-- The defining sum for `planarMultipolePolynomial`. -/
theorem planarMultipolePolynomial_def (x : ℂ) (N : ℕ) :
    planarMultipolePolynomial x N =
      ∑ k ∈ Finset.range N,
        Polynomial.monomial k
          (if k = 0 then (planarNewtonianKernel x : ℂ)
          else ((2 * Real.pi * k : ℝ) : ℂ)⁻¹ * (x ^ k)⁻¹) :=
  (rfl)

/-- The `0`-term multipole polynomial is zero. -/
@[simp]
theorem planarMultipolePolynomial_zero_right (x : ℂ) :
    planarMultipolePolynomial x 0 = 0 := by
  simp [planarMultipolePolynomial_def]

/-- At the origin, every multipole polynomial is zero. -/
@[simp]
theorem planarMultipolePolynomial_zero_left (N : ℕ) :
    planarMultipolePolynomial 0 N = 0 := by
  rw [planarMultipolePolynomial_def]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  split_ifs with hk <;> simp [hk]

/-- Extending the truncation order by one adds the `N`-th complex multipole mode. -/
theorem planarMultipolePolynomial_succ (x : ℂ) (N : ℕ) :
    planarMultipolePolynomial x (N + 1) =
      planarMultipolePolynomial x N +
        Polynomial.monomial N
          (if N = 0 then (planarNewtonianKernel x : ℂ)
          else ((2 * Real.pi * N : ℝ) : ℂ)⁻¹ * (x ^ N)⁻¹) :=
  Finset.sum_range_succ _ _

/-- Explicit coefficients of `planarMultipolePolynomial x N`. -/
theorem coeff_planarMultipolePolynomial (x : ℂ) (N k : ℕ) :
    (planarMultipolePolynomial x N).coeff k =
      if k < N then
        if k = 0 then (planarNewtonianKernel x : ℂ)
        else ((2 * Real.pi * k : ℝ) : ℂ)⁻¹ * (x ^ k)⁻¹
      else 0 := by
  rw [planarMultipolePolynomial_def, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range]

/-- `planarMultipolePolynomial x N` has degree at most `N - 1`. -/
theorem natDegree_planarMultipolePolynomial_le (x : ℂ) (N : ℕ) :
    (planarMultipolePolynomial x N).natDegree ≤ N - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hkN : ¬k < N := by lia
  simp [coeff_planarMultipolePolynomial, hkN]

/-- **Real part of the holomorphic multipole polynomial.** Evaluating
`planarMultipolePolynomial x N` at `y` and taking the real part recovers
`(planarMultipoleSeries x).partialSum N y`. -/
@[simp]
theorem eval_planarMultipolePolynomial_re (x : ℂ) (N : ℕ) (y : ℂ) :
    ((planarMultipolePolynomial x N).eval y).re =
      (planarMultipoleSeries x).partialSum N y := by
  rw [planarMultipolePolynomial_def, FormalMultilinearSeries.partialSum,
    ← Polynomial.coe_evalRingHom, map_sum (Polynomial.evalRingHom y), Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Polynomial.coe_evalRingHom, Polynomial.eval_monomial,
      planarMultipoleSeries_apply_const_succ]
    have hc : (((2 * Real.pi * ↑(k + 1) : ℝ) : ℂ)⁻¹ * (x ^ (k + 1))⁻¹ * y ^ (k + 1)) =
        (((2 * Real.pi * (k + 1))⁻¹ : ℝ) : ℂ) * ((y / x) ^ (k + 1)) := by
      rw [← Complex.ofReal_inv, div_pow, div_eq_mul_inv]
      push_cast
      ring
    rw [hc, Complex.re_ofReal_mul]

/-! ### Harmonicity, power series representation, and `C^k` approximation on `ℂ` -/

/-- Every homogeneous term of `planarMultipoleSeries x` is harmonic on all of `ℂ`. -/
theorem harmonicAt_planarMultipoleSeries_apply (x : ℂ) (k : ℕ) (z : ℂ) :
    HarmonicAt (fun y ↦ planarMultipoleSeries x k fun _ ↦ y) z := by
  cases k with
  | zero => simp
  | succ k =>
    have hfun : (fun y ↦ planarMultipoleSeries x (k + 1) fun _ ↦ y) =
        (2 * Real.pi * (k + 1))⁻¹ • fun y : ℂ ↦ ((y / x) ^ (k + 1)).re := by
      ext y
      simp [div_pow]
    rw [hfun]
    have han : AnalyticAt ℂ (fun y : ℂ ↦ (y / x) ^ (k + 1)) z := by
      simp only [div_eq_mul_inv]
      exact (analyticAt_id.mul analyticAt_const).pow (k + 1)
    exact han.harmonicAt_re.const_smul

/-- Every partial sum of `planarMultipoleSeries x` is harmonic on all of `ℂ`. -/
theorem harmonicAt_planarMultipoleSeries_partialSum (x : ℂ) (N : ℕ) (z : ℂ) :
    HarmonicAt ((planarMultipoleSeries x).partialSum N) z :=
  HarmonicAt.sum fun k _ ↦ harmonicAt_planarMultipoleSeries_apply x k z

/-- **The exterior multipole expansion of the planar Newtonian kernel.** For every nonzero pole
`x : ℂ`, `y ↦ planarNewtonianKernel (x - y)` has the power series `planarMultipoleSeries x` at the
origin on the open disk `eball 0 ‖x‖₊`. -/
theorem hasFPowerSeriesOnBall_planarNewtonianKernel_sub {x : ℂ} (hx : x ≠ 0) :
    HasFPowerSeriesOnBall (fun y ↦ planarNewtonianKernel (x - y))
      (planarMultipoleSeries x) 0 ‖x‖₊ := by
  set u : ℂ →L[ℝ] ℂ := (x⁻¹ • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
  have hu0 : u 0 = 0 := map_zero u
  have hc := ((2 * Real.pi)⁻¹ • Complex.reCLM).comp_hasFPowerSeriesOnBall
    (hasFPowerSeriesOnBall_neg_clog_one_sub.restrictScalars (𝕜 := ℝ))
  rw [← hu0] at hc
  have hcomp := hc.compContinuousLinearMap
  have hurad : (1 : ℝ≥0∞) / ‖u‖ₑ = ‖x‖₊ := by
    have hunorm : ‖u‖ = ‖x‖⁻¹ := by
      simp [u, ContinuousLinearMap.norm_restrictScalars, norm_smul, ContinuousLinearMap.norm_id]
    rw [← ofReal_norm, hunorm, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hx)]
    simp [ofReal_norm, eNorm_eq_nnNorm]
  rw [hurad] at hcomp
  have hconst : HasFPowerSeriesOnBall (fun _ : ℂ ↦ planarNewtonianKernel x)
      (constFormalMultilinearSeries ℝ ℂ (planarNewtonianKernel x)) 0 ‖x‖₊ :=
    (hasFPowerSeriesOnBall_const (c := planarNewtonianKernel x) (e := 0)).mono
      (by simpa using hx) ENNReal.coe_lt_top.le
  rw [planarMultipoleSeries_def]
  refine (hconst.add hcomp).congr fun y hy ↦ ?_
  have hyx : ‖y‖ < ‖x‖ := by
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm] at hy
    exact_mod_cast hy
  have hquot_lt : ‖x⁻¹ * y‖ < 1 := by
    rw [norm_mul, norm_inv]
    exact (inv_mul_lt_iff₀ (norm_pos_iff.2 hx)).2 (by simpa using hyx)
  have h1sub : 1 - x⁻¹ * y ≠ 0 := by
    intro h0
    have h1 : ‖x⁻¹ * y‖ = 1 := by rw [← sub_eq_zero.1 h0, norm_one]
    exact hquot_lt.ne h1
  have hfac : x - y = x * (1 - x⁻¹ * y) := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  simp only [Pi.add_apply, Function.comp_apply, u, ContinuousLinearMap.coe_restrictScalars',
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply, Complex.neg_re,
    Complex.log_re]
  rw [hfac, planarNewtonianKernel_mul hx h1sub, planarNewtonianKernel_def (1 - x⁻¹ * y)]
  ring

/-- **Power series of the planar Newtonian kernel at a nonzero point.** At every `a ≠ 0`,
`planarNewtonianKernel` is represented by `planarMultipoleSeries (-a)` on the open disk
`eball a ‖a‖₊` reaching to the pole at `0`. -/
theorem hasFPowerSeriesOnBall_planarNewtonianKernel {a : ℂ} (ha : a ≠ 0) :
    HasFPowerSeriesOnBall planarNewtonianKernel (planarMultipoleSeries (-a)) a ‖a‖₊ := by
  have h := (hasFPowerSeriesOnBall_planarNewtonianKernel_sub (neg_ne_zero.2 ha)).comp_sub a
  convert h using 1
  · ext y
    have hy : -a - (y - a) = -y := by ring
    rw [hy, planarNewtonianKernel_neg]
  · simp
  · simp

/-- **Sharp convergence radius of the planar multipole series.** For `x ≠ 0`, the radius of
convergence of `planarMultipoleSeries x` is `‖x‖₊`, the distance from the origin to the pole. -/
theorem radius_planarMultipoleSeries {x : ℂ} (hx : x ≠ 0) :
    (planarMultipoleSeries x).radius = ‖x‖₊ := by
  refine le_antisymm ?_ (hasFPowerSeriesOnBall_planarNewtonianKernel_sub hx).r_le
  by_contra! hlt
  have hmem : x ∈ Metric.eball (0 : ℂ) (planarMultipoleSeries x).radius := by
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm]
    exact hlt
  have hs := ((planarMultipoleSeries x).summable_norm_apply hmem).comp_injective
    (add_left_injective 1)
  have hterm : (fun k : ℕ ↦ ‖planarMultipoleSeries x (k + 1) fun _ ↦ x‖) =
      fun k : ℕ ↦ (2 * Real.pi)⁻¹ * ((k + 1 : ℕ) : ℝ)⁻¹ := by
    ext k
    simp [hx, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
    ring
  rw [Function.comp_def, hterm] at hs
  have hharm : Summable fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)⁻¹ := by
    simpa [← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne'] using hs.mul_left (2 * Real.pi)
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).1 hharm)

/-- For every `x : ℂ`, the convergence radius of `planarMultipoleSeries x` is at least `‖x‖₊`. -/
theorem le_radius_planarMultipoleSeries (x : ℂ) :
    (‖x‖₊ : ℝ≥0∞) ≤ (planarMultipoleSeries x).radius := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (radius_planarMultipoleSeries hx).ge

/-- **Pointwise exterior multipole series.** Whenever `‖y‖ < ‖x‖`, the diagonal multipole terms
sum to `planarNewtonianKernel (x - y)`. -/
theorem hasSum_planarNewtonianKernel_sub {x y : ℂ} (hy : ‖y‖ < ‖x‖) :
    HasSum (fun k : ℕ ↦ planarMultipoleSeries x k fun _ ↦ y)
      (planarNewtonianKernel (x - y)) := by
  have hx : x ≠ 0 := norm_pos_iff.1 ((norm_nonneg y).trans_lt hy)
  have hmem : y ∈ Metric.eball (0 : ℂ) ‖x‖₊ := by
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm]
    exact_mod_cast hy
  simpa using (hasFPowerSeriesOnBall_planarNewtonianKernel_sub hx).hasSum hmem

/-- **Uniform `C^k` convergence of the planar multipole partial sums.** On every closed disk
`closedBall 0 r` strictly inside `ball 0 ‖x‖`, the `k`-th iterated derivatives of the partial sums
of `planarMultipoleSeries x` converge uniformly to the `k`-th iterated derivative of
`y ↦ planarNewtonianKernel (x - y)`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_planarMultipoleSeries_partialSum
    {x : ℂ} {r : ℝ} (hr : r < ‖x‖) (k : ℕ) :
    TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k ((planarMultipoleSeries x).partialSum N))
      (iteratedFDeriv ℝ k fun y ↦ planarNewtonianKernel (x - y)) atTop
      (closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [Metric.closedBall_eq_empty.2 hr0]
    exact tendstoUniformlyOn_empty
  have hx : x ≠ 0 := norm_pos_iff.1 (hr0.trans_lt hr)
  have h0 : HarmonicAt (fun y ↦ planarNewtonianKernel (x - y)) 0 := by
    have hfun : (fun z ↦ planarNewtonianKernel (z - x)) =
        fun z ↦ planarNewtonianKernel (x - z) :=
      funext fun z ↦ planarNewtonianKernel_sub_comm z x
    simpa [hfun] using harmonicAt_planarNewtonianKernel_sub (Ne.symm hx)
  have hlt : ENNReal.ofReal r < ‖x‖₊ := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
    exact (ENNReal.ofReal_lt_ofReal_iff (norm_pos_iff.2 hx)).2 hr
  have hp := hasFPowerSeriesOnBall_planarNewtonianKernel_sub hx
  simpa using hp.tendstoUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt h0 hlt k

/-- **Uniform `C^k` convergence of the real parts of the holomorphic multipole polynomials.** -/
theorem tendstoUniformlyOn_iteratedFDeriv_eval_planarMultipolePolynomial_re
    {x : ℂ} {r : ℝ} (hr : r < ‖x‖) (k : ℕ) :
    TendstoUniformlyOn
      (fun N ↦ iteratedFDeriv ℝ k fun y ↦ ((planarMultipolePolynomial x N).eval y).re)
      (iteratedFDeriv ℝ k fun y ↦ planarNewtonianKernel (x - y)) atTop
      (closedBall 0 r) := by
  have hfun (N : ℕ) :
      (fun y : ℂ ↦ ((planarMultipolePolynomial x N).eval y).re) =
        (planarMultipoleSeries x).partialSum N := by
    ext y
    exact eval_planarMultipolePolynomial_re x N y
  simpa [hfun] using tendstoUniformlyOn_iteratedFDeriv_planarMultipoleSeries_partialSum hr k

/-! ### Two-dimensional real inner product spaces and `EuclideanSpace ℝ (Fin 2)` -/

/-- **Power series of `y ↦ log ‖y‖` in a two-dimensional real inner product space.**
At every nonzero point `a`, `y ↦ log ‖y‖` admits a formal power series of exact convergence radius
`‖a‖₊` representing it on `eball a ‖a‖₊`, whose homogeneous terms are harmonic on the whole
space. -/
theorem exists_hasFPowerSeriesOnBall_log_norm_of_finrank_eq_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 2) {a : E} (ha : a ≠ 0) :
    ∃ p : FormalMultilinearSeries ℝ E ℝ,
      p.radius = ‖a‖₊ ∧
        HasFPowerSeriesOnBall (fun y ↦ Real.log ‖y‖) p a ‖a‖₊ ∧
        ∀ k z, HarmonicAt (fun y ↦ p k fun _ ↦ y) z := by
  have : Nontrivial E := ⟨⟨a, 0, ha⟩⟩
  let l : E ≃ₗᵢ[ℝ] ℂ := ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr.trans
    Complex.orthonormalBasisOneI.repr.symm
  have hla : l a ≠ 0 := by simpa using ha
  have hser0 : HasFPowerSeriesOnBall (-(2 * Real.pi) • planarNewtonianKernel)
      (-(2 * Real.pi) • planarMultipoleSeries (-l a))
      (l.toLinearIsometry.toContinuousLinearMap a) ‖l a‖₊ := by
    rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    exact (hasFPowerSeriesOnBall_planarNewtonianKernel hla).const_smul (c := -(2 * Real.pi))
  have hser := hser0.compContinuousLinearMap
  have hrad_ball : (‖l a‖₊ : ℝ≥0∞) / ‖l.toLinearIsometry.toContinuousLinearMap‖ₑ = ‖a‖₊ := by
    simp
  rw [hrad_ball] at hser
  have hlog : HasFPowerSeriesOnBall (fun y ↦ Real.log ‖y‖)
      ((-(2 * Real.pi) • planarMultipoleSeries (-l a)).compContinuousLinearMap
        l.toLinearIsometry.toContinuousLinearMap) a ‖a‖₊ := by
    refine hser.congr fun y _ ↦ ?_
    simp only [Pi.smul_apply, Function.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, planarNewtonianKernel_def, l.norm_map, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
  have hharm_log : HarmonicAt (fun y ↦ Real.log ‖y‖) a := by
    simpa using harmonicAt_log_norm_sub_of_finrank_eq_two hE (x := a) (a := 0) ha
  refine ⟨_, ?_, hlog, fun k z ↦ hlog.hasFPowerSeriesAt.harmonicAt_apply hharm_log k z⟩
  rw [FormalMultilinearSeries.radius_compContinuousLinearMap_linearIsometryEquiv_eq,
    FormalMultilinearSeries.radius_smul_eq _ (neg_ne_zero.2 Real.two_pi_pos.ne'),
    radius_planarMultipoleSeries (neg_ne_zero.2 hla)]
  simp

/-- **Sharp exterior multipole expansion of `y ↦ log ‖x - y‖` in two dimensions.**
In any two-dimensional real inner product space, for every pole `x ≠ 0` the function
`y ↦ log ‖x - y‖` has a power series at the origin of exact convergence radius `‖x‖₊`, representing
it on `eball 0 ‖x‖₊`, whose homogeneous terms are harmonic on the whole space. -/
theorem exists_hasFPowerSeriesOnBall_log_norm_sub_of_finrank_eq_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 2) {x : E} (hx : x ≠ 0) :
    ∃ p : FormalMultilinearSeries ℝ E ℝ,
      p.radius = ‖x‖₊ ∧
        HasFPowerSeriesOnBall (fun y ↦ Real.log ‖x - y‖) p 0 ‖x‖₊ ∧
        ∀ k z, HarmonicAt (fun y ↦ p k fun _ ↦ y) z := by
  obtain ⟨p, hrad, hp, hharm⟩ :=
    exists_hasFPowerSeriesOnBall_log_norm_of_finrank_eq_two hE (neg_ne_zero.2 hx)
  refine ⟨p, by simpa using hrad, ?_, hharm⟩
  convert hp.comp_sub x using 1
  · ext y
    rw [norm_sub_rev]
  · simp
  · simp

/-- **Harmonic polynomial approximation of `y ↦ log ‖x - y‖` on `EuclideanSpace ℝ (Fin 2)`.**
For every pole `x : EuclideanSpace ℝ (Fin 2)`, there is a sequence of functions `P N` harmonic on
all of `EuclideanSpace ℝ (Fin 2)` and belonging to `polynomialsDegLE (Fin 2) N` whose iterated
derivatives of every order `k` converge uniformly to those of `y ↦ log ‖x - y‖` on every closed
ball `closedBall 0 r` with `r < ‖x‖`. -/
theorem exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_log_norm_sub
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ P : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ N z, HarmonicAt (P N) z) ∧
        (∀ N, P N ∈ polynomialsDegLE (Fin 2) N) ∧
        ∀ {r : ℝ}, r < ‖x‖ → ∀ k : ℕ,
          TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
            (iteratedFDeriv ℝ k fun y ↦ Real.log ‖x - y‖) atTop (closedBall 0 r) := by
  rcases eq_or_ne x 0 with rfl | hx
  · refine ⟨fun _ _ ↦ 0, fun _ _ ↦ harmonicAt_const 0,
      fun N ↦ const_mem_polynomialsDegLE (Fin 2) N 0, fun {r} hr _ ↦ ?_⟩
    rw [norm_zero] at hr
    rw [Metric.closedBall_eq_empty.2 hr]
    exact tendstoUniformlyOn_empty
  obtain ⟨p, -, hp, -⟩ :=
    exists_hasFPowerSeriesOnBall_log_norm_sub_of_finrank_eq_two finrank_euclideanSpace_fin hx
  have h0 : HarmonicAt (fun y ↦ Real.log ‖x - y‖) 0 := by
    have hfun : (fun z ↦ Real.log ‖z - x‖) = fun z ↦ Real.log ‖x - z‖ :=
      funext fun z ↦ congrArg Real.log (norm_sub_rev z x)
    simpa [hfun] using
      harmonicAt_log_norm_sub_of_finrank_eq_two finrank_euclideanSpace_fin (Ne.symm hx)
  refine ⟨p.partialSum, fun N z ↦ hp.hasFPowerSeriesAt.harmonicAt_partialSum h0 N z,
    fun N ↦ polynomialsDegLE_mono _ (Nat.sub_le N 1) (p.partialSum_mem_polynomialsDegLE N),
    fun {r} hr k ↦ ?_⟩
  have hlt : ENNReal.ofReal r < ‖x‖₊ := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
    exact (ENNReal.ofReal_lt_ofReal_iff (norm_pos_iff.2 hx)).2 hr
  simpa using hp.tendstoUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt h0 hlt k

end TauCeti
