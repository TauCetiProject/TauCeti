/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Principal complex powers: scaling, sector inversion, and holomorphic products

Multiplication of a complex number by a nonnegative real scalar is compatible with principal
complex powers.  Away from zero, this follows because positive scaling does not cross the branch
cut of the principal logarithm; the zero cases follow from the totalized definition of `cpow`.

Taking the principal power `u ^ (r⁻¹ : ℝ)` of a nonzero `u` divides its argument by `r`, so
raising the result back to the power `r` returns `u` — but only as long as the intermediate
argument stays inside the principal range `(-π, π]`, which is where `Complex.cpow_mul` may be
applied.  For a positive real exponent `r` that range is reached exactly on the sector
`-(r * π) < arg u ≤ r * π`.

Products `∏ i, (1 - a i * w) ^ e i` are holomorphic near zero, with derivative
`-∑ i, e i * a i` and second derivative
`(∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2` at zero. The quadratic difference
quotient tends to half that second derivative. These coefficients describe the integrand of
a Schwarz--Christoffel map in the reciprocal coordinate at infinity.

## Main results

* `TauCeti.ofReal_mul_cpow` -- a principal power splits across a nonnegative real factor.
* `TauCeti.ofReal_pow_cpow` -- a principal power of a natural power of a nonnegative real
  multiplies the exponents.
* `TauCeti.cpow_sum` -- a principal power of a finite sum splits into a product for a nonzero
  complex base.
* `TauCeti.ofReal_exp_cpow` -- a principal power of a positive real exponential is an exponential.
* `TauCeti.cpow_inv_cpow_of_arg_mem_Ioc` -- raising an inverse principal power recovers its
  base on a suitable sector.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-- A principal complex power splits across multiplication by a nonnegative real scalar:
`((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w` for all complex `z` and `w`, without a branch
hypothesis on `z`.  This generalizes `Complex.mul_cpow_ofReal_nonneg` to a complex second factor;
the proof follows Mathlib's. -/
theorem ofReal_mul_cpow {r : ℝ} (hr : 0 ≤ r) (z w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  rcases eq_or_ne w 0 with (rfl | hw)
  · simp only [Complex.cpow_zero, mul_one]
  rcases eq_or_lt_of_le hr with (rfl | hr')
  · rw [Complex.ofReal_zero, zero_mul, Complex.zero_cpow hw, zero_mul]
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [Complex.zero_cpow hw]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr'.ne') hz),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr'.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr' hz, add_mul, Complex.exp_add]
  rw [Complex.ofReal_log hr]

/-- A principal complex power of a natural power of a nonnegative real multiplies the exponents:
`((r : ℂ) ^ n) ^ s = (r : ℂ) ^ (n * s)`.  The argument of `(r : ℂ)` is `0`, so the principal branch
is not crossed. -/
theorem ofReal_pow_cpow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (s : ℂ) :
    ((r : ℂ) ^ n) ^ s = (r : ℂ) ^ (n * s) := by
  have harg : (r : ℂ).arg = 0 := arg_ofReal_of_nonneg hr
  rw [cpow_nat_mul' (by simp [harg, Real.pi_pos]) (by simp [harg, Real.pi_pos.le])]

/-- A principal complex power with nonzero base takes a finite sum of exponents to the
corresponding product. -/
theorem cpow_sum {ι : Type*} {x : ℂ} (hx : x ≠ 0) (f : ι → ℂ) (s : Finset ι) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i :=
  map_sum (⟨⟨fun y ↦ x ^ y, Complex.cpow_zero x⟩,
    fun y z ↦ Complex.cpow_add y z hx⟩ : ℂ →+ Additive ℂ) f s

/-- A principal complex power of the positive real `Real.exp t` is `exp (t * s)`: the principal
logarithm of `Real.exp t` is `t`. -/
theorem ofReal_exp_cpow (t : ℝ) (s : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ s = exp (t * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_pos t).ne'),
    ← ofReal_log (Real.exp_pos t).le, Real.log_exp]

/-- The principal power `u ^ (r⁻¹ : ℝ)` raised to the real power `r` is again `u`, for a
positive `r` and a base whose argument lies in the sector `(-(r * π), r * π]`.  The intermediate
argument `arg u / r` then lies in `(-π, π]`, so the principal branch is not crossed. -/
theorem cpow_inv_cpow_of_arg_mem_Ioc {u : ℂ} {r : ℝ} (hr : 0 < r)
    (harg : u.arg ∈ Set.Ioc (-(r * Real.pi)) (r * Real.pi)) :
    (u ^ ((r⁻¹ : ℝ) : ℂ)) ^ (r : ℂ) = u := by
  rw [← Complex.cpow_mul]
  · norm_num [hr.ne']
  · simp only [Complex.mul_im, Complex.log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    calc
      -Real.pi = (-(r * Real.pi)) * r⁻¹ := by field_simp
      _ < u.arg * r⁻¹ := mul_lt_mul_of_pos_right harg.1 (inv_pos.mpr hr)
  · simp only [Complex.mul_im, Complex.log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    calc
      u.arg * r⁻¹ ≤ (r * Real.pi) * r⁻¹ := mul_le_mul_of_nonneg_right harg.2 (inv_nonneg.mpr hr.le)
      _ = Real.pi := by field_simp

/-- The reciprocal-coordinate product of principal powers is holomorphic at zero,
where every base equals one. -/
theorem analyticAt_prod_one_sub_mul_cpow {ι : Type*} [Fintype ι] (a e : ι → ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ∏ i, (1 - a i * w) ^ e i) 0 := by
  have hfactor (i : ι) : AnalyticAt ℂ (fun w : ℂ => (1 - a i * w) ^ e i) 0 :=
    ((analyticAt_const (v := (1 : ℂ))).sub
      ((analyticAt_const (v := a i)).mul analyticAt_id)).cpow
        analyticAt_const (by simp [slitPlane])
  exact Finset.analyticAt_fun_prod Finset.univ (fun i _ => hfactor i)

/-- The derivative at zero of the reciprocal-coordinate product is the negative
weighted sum of its coefficients. -/
theorem hasDerivAt_prod_one_sub_mul_cpow {ι : Type*} [Fintype ι] (a e : ι → ℂ) :
    HasDerivAt (fun w : ℂ => ∏ i, (1 - a i * w) ^ e i) (-∑ i, e i * a i) 0 := by
  classical
  have hfactor (i : ι) : HasDerivAt (fun w : ℂ => (1 - a i * w) ^ e i)
      (-e i * a i) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (a i)).const_sub 1).cpow_const
      (c := e i) (by simp [slitPlane])
  simpa [Finset.sum_neg_distrib] using HasDerivAt.fun_finsetProd
    (u := Finset.univ) (fun i _ => hfactor i)

/-- The second derivative at zero of a product of principal powers. The coefficients and
exponents may be complex; no branch assumptions are needed at zero, where each base is one. -/
theorem hasDerivAt_deriv_prod_one_sub_mul_cpow {ι : Type*} [Fintype ι] (a e : ι → ℂ) :
    HasDerivAt (deriv (fun w : ℂ => ∏ i, (1 - a i * w) ^ e i))
      ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) 0 := by
  classical
  let L : ℂ → ℂ := fun w => ∑ i, log (1 - a i * w) * e i
  let D : ℂ → ℂ := fun w => ∑ i, (-a i) / (1 - a i * w) * e i
  have hbase : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ i, 1 - a i * w ∈ slitPlane := by
    apply eventually_all.mpr
    intro i
    exact (isOpen_slitPlane.preimage (continuous_const.sub
      (continuous_const.mul continuous_id))).mem_nhds (by simp [slitPlane])
  have hL (w : ℂ) (hw : ∀ i, 1 - a i * w ∈ slitPlane) : HasDerivAt L (D w) w := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa [D, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id w).const_mul (a i)).const_sub 1).clog (hw i)).mul_const (e i)
  have hD : HasDerivAt D (-∑ i, e i * a i ^ 2) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((hasDerivAt_const (0 : ℂ) (-a i)).fun_div
        (((hasDerivAt_id (0 : ℂ)).const_mul (a i)).const_sub 1) (by simp)).mul_const (e i)
    convert h using 1
    · rfl -- The sum and quotient are pointwise operations on functions.
    · simp [Finset.sum_neg_distrib, sq, mul_comm, mul_left_comm]
  have hL0 : HasDerivAt L (-∑ i, e i * a i) 0 := by
    simpa [D, mul_comm, Finset.sum_neg_distrib] using hL 0 (by simp [slitPlane])
  have hprod : (fun w : ℂ => ∏ i, (1 - a i * w) ^ e i) =ᶠ[𝓝 0]
      (fun w => exp (L w)) := by
    filter_upwards [hbase] with w hw
    simp only [L, exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    exact cpow_def_of_ne_zero (slitPlane_ne_zero (hw i)) _
  have hderiv : deriv (fun w : ℂ => ∏ i, (1 - a i * w) ^ e i) =ᶠ[𝓝 0]
      (fun w => exp (L w) * D w) := by
    filter_upwards [hprod.deriv, hbase] with w hw hwbase
    rw [hw, (hL w hwbase).cexp.deriv]
  convert ((hL0.cexp).fun_mul hD).congr_of_eventuallyEq hderiv using 1
  simp [L, D, Finset.sum_neg_distrib, mul_comm, sq, sub_eq_add_neg]

/-- The quadratic coefficient in the product of principal powers, expressed as a
second-order difference quotient. The limit is taken in the whole complex plane. -/
theorem tendsto_prod_one_sub_mul_cpow_sub_linear_div_sq {ι : Type*} [Fintype ι]
    (a e : ι → ℂ) :
    Filter.Tendsto (fun w : ℂ =>
      ((∏ i, (1 - a i * w) ^ e i) - 1 + (∑ i, e i * a i) * w) / w ^ 2)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2)) := by
  let q : ℂ → ℂ := fun w => ∏ i, (1 - a i * w) ^ e i
  have hq := analyticAt_prod_one_sub_mul_cpow a e
  have hq' := hasDerivAt_prod_one_sub_mul_cpow a e
  have hq'' := hasDerivAt_deriv_prod_one_sub_mul_cpow a e
  have hseries := hq.hasFPowerSeriesAt.has_fpower_series_dslope_fslope
  have hcoeff : deriv (dslope q 0) 0 =
      ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2 := by
    have h := hseries.deriv
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const_one,
      one_smul, FormalMultilinearSeries.coeff_fslope,
      FormalMultilinearSeries.coeff_ofScalars] at h
    simpa [iteratedDeriv_succ, hq''.deriv] using h
  have hlim := hseries.differentiableAt.hasDerivAt.tendsto_slope_zero
  rw [hcoeff] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := hw
  rw [zero_add, dslope_of_ne q hw0, dslope_same, hq'.deriv]
  simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
  simp only [q, mul_zero, sub_zero, one_cpow, Finset.prod_const_one]
  field_simp
  ring

end TauCeti

end
