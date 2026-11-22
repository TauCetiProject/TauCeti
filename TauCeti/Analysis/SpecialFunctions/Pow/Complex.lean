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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

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

Rescaling the principal `k`-th root, `z ↦ c * (z / z₀) ^ (k⁻¹ : ℂ)`, gives a `k`-th root
function that is complex differentiable at a nonzero `z₀` and takes there any prescribed `k`-th
root `c` of `z₀`, since `z / z₀` stays in the slit plane near `z₀`.

Products `∏ i, (1 - a i * w) ^ e i` are holomorphic near zero, with derivative
`-∑ i, e i * a i` and second derivative
`(∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2` at zero. The quadratic difference
quotient tends to half that second derivative. These coefficients describe the integrand of
a Schwarz--Christoffel map in the reciprocal coordinate at infinity.

For a nonpositive real exponent `r`, the principal power `(t + x) ^ r` of a translate of `x` along
the positive real axis is `O(t ^ r)` for `t > 0` when `x ∈ slitPlane ∪ {0}`, and bounded for
`t ≥ 0` when `x ∈ slitPlane`; in the latter case it is `O((1 + t) ^ r)` for `t ≥ 0`, for a real
exponent `r` of either sign. More generally, for `z ∈ slitPlane`, `t ≥ 0`,
and any complex exponent `s` (with no sign restriction on `s.re`), `‖((t : ℂ) + w) ^ s‖` is bounded
above by `C * (1 + t) ^ s.re` (with `C > 0`) locally uniformly in `w` near `z`, and
`‖((t : ℂ) + z) ^ s‖` is bounded below by `c * (1 + t) ^ s.re` (with `c > 0`) at each fixed
`z ∈ slitPlane`. These bounds control the integrands and parametric derivatives of improper
integrals such as Carlson's elliptic integrals along `(0, ∞)`.

## Main results

* `TauCeti.ofReal_mul_cpow` -- a principal power splits across a nonnegative real factor.
* `TauCeti.ofReal_prod_cpow` -- a principal power splits across a finite product of nonnegative
  reals.
* `TauCeti.mul_cpow_of_arg_add_mem` -- a principal power splits across a product when the
  arguments add in the principal range.
* `TauCeti.mul_cpow_of_re_pos` -- the right-half-plane specialization.
* `TauCeti.ofReal_pow_cpow` -- a principal power of a natural power of a nonnegative real
  multiplies the exponents.
* `TauCeti.ofReal_cpow_conj` -- a principal power of a nonnegative real commutes with complex
  conjugation of the exponent.
* `TauCeti.cpow_sum` -- a principal power of a finite sum splits into a product for a nonzero
  complex base.
* `TauCeti.ofReal_exp_cpow` -- a principal power of a positive real exponential is an exponential.
* `TauCeti.natCast_cpow_ofReal_mul` -- the power `n ^ (c s)` of a positive integer is the
  exponential of `(c log n) s`.
* `TauCeti.cpow_inv_cpow_of_arg_mem_Ioc` -- raising an inverse principal power recovers its
  base on a suitable sector.
* `TauCeti.exists_differentiableAt_pow_eq` -- near a nonzero point, a prescribed `k`-th root
  extends to a `k`-th root function complex differentiable at that point.
* `TauCeti.cpow_mul_inv`, `TauCeti.cpow_add_one'` -- multiplying a principal power by `w⁻¹` or `w`
  lowers or raises the exponent by one, including at the base `0`.
* `TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow`, `TauCeti.exists_norm_ofReal_add_cpow_le`,
  `TauCeti.exists_norm_ofReal_add_cpow_le_mul_one_add_rpow` -- bounds on `(t + x) ^ r` for
  real `r` along the positive real axis; only the last allows `r > 0`.
* `TauCeti.exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow`,
  `TauCeti.exists_pos_mul_one_add_rpow_le_norm_ofReal_add_cpow` -- locally uniform upper and
  pointwise lower bounds comparing `‖((t : ℂ) + w) ^ s‖` with `(1 + t) ^ s.re` for `w` near
  `z ∈ slitPlane`, `t ≥ 0`, and arbitrary `s : ℂ`.
* `TauCeti.exists_ball_slitPlane_cpow_le` -- locally uniform bounds on `w ^ (σ + i y)` and its
  `w`-derivative in `|y|` with exponential rate strictly below `π` around `w₀ ∈ slitPlane`.
* `TauCeti.continuousOn_ofReal_add_cpow`, `TauCeti.continuousOn_ofReal_add_cpow_Ici`,
  `TauCeti.continuous_ofReal_add_cpow_of_re_pos` -- continuity of `t ↦ (t + x) ^ s` on
  `(0, ∞)`, on `[0, ∞)`, and everywhere when `0 < s.re`.
* `TauCeti.ofReal_cpow_mul_inv_mul_inv_cpow` -- for `a > 0` and `w` off the negative real axis,
  `a ^ s * (a⁻¹ * w⁻¹) ^ s = w ^ (-s)`.
* `Complex.exp_log_add_mul` -- split an exponential at a principal logarithm.
* `Complex.cpow_neg_half_mul_self`, `Complex.cpow_neg_half_mul_eq_cpow_half`,
  `Complex.neg_cpow_half_eq_or_eq_neg` -- algebraic identities for principal `±1/2` powers,
  including at `w = 0`, and the sign dichotomy `(-w) ^ (1/2) = ±(I * w ^ (1/2))`.
* `HasDerivAt.cpow_half` -- derivative of `w ↦ f w ^ (1/2)` in the slit plane over any
  nontrivially normed field `𝕜` with `[NormedAlgebra 𝕜 ℂ]`.
* `Complex.tendsto_ofReal_add_cpow_neg` -- for any complex `x` and real `s > 0`,
  `(t + x) ^ (-s)` tends to `0` as the real number `t` tends to `∞`.
* `Complex.tendsto_natCast_cpow_neg_atTop` -- for `0 < re y`, `N ^ (-y)` tends to `0` along the
  natural numbers.
* `Complex.continuousAt_neg_two_cpow_half_mul_inv`,
  `Complex.hasDerivAt_neg_two_cpow_half_mul_inv`,
  `Complex.tendsto_neg_two_cpow_half_mul_inv_atTop` -- continuity at `0`, derivative on `(0, ∞)` and
  limit at `∞` of `t ↦ -2 (t + x) ^ (1/2) (t + y)⁻¹`. Continuity holds for arbitrary `x` and
  `y ≠ 0`; the derivative needs `x, y ∈ slitPlane ∪ {0}`; the limit holds for arbitrary `x` and `y`.
* `Complex.norm_ofReal_cpow_le_exp` -- for `a > 0`, `‖a ^ w‖ ≤ exp (|log a| ‖w‖)`.
* `Complex.norm_one_sub_mul_ofReal_cpow_le` -- for `‖z‖ ≤ 1`, `0 ≤ t < 1`, and any `s : ℂ`,
  `‖(1 - z * t) ^ s‖ ≤ exp (π |s.im|) (2 ^ s.re + (1 - t) ^ s.re)`.
* `Complex.inv_cpow_half_cpow` -- `((z ^ (1/2))⁻¹) ^ w = z ^ (-w / 2)` for all `z, w : ℂ`.
* `Complex.norm_cpow_le_mul_exp_arg`, `Complex.norm_cpow_le_max_mul_exp_arg_of_re_mem_Icc`,
  `Complex.norm_cpow_le_mul_exp` --
  `‖w ^ d‖ ≤ ‖w‖ ^ d.re * exp (|w.arg| * |d.im|) ≤ ‖w‖ ^ d.re * exp (π |d.im|)`, and the
  uniform vertical-strip bound `‖w ^ d‖ ≤ max (‖w‖ ^ a) (‖w‖ ^ b) * exp (|w.arg| * |d.im|)`
  for `d.re ∈ [a, b]` and `w ≠ 0`.
* `Complex.norm_one_add_cpow_le`, `Complex.norm_one_add_ofReal_mul_exp_mul_I_cpow_le` --
  `‖(1 + z) ^ d‖ ≤ exp (π |d.im|) (1 + ‖z‖) ^ max 0 d.re` for `0 ≤ z.re`, and
  `‖(1 + r e^{iθ}) ^ d‖ ≤ exp (π |d.im|) (cos (θ / 2)) ^ min 0 d.re (1 + r) ^ max 0 d.re`
  for `|θ| < π` and `0 ≤ r`.
-/

public section

open Complex ComplexConjugate Filter
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

/-- A principal complex power splits across a finite product of nonnegative reals:
`((∏ i ∈ s, f i : ℝ) : ℂ) ^ z = ∏ i ∈ s, (f i : ℂ) ^ z`. -/
theorem ofReal_prod_cpow {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (z : ℂ) : ((∏ i ∈ s, f i : ℝ) : ℂ) ^ z = ∏ i ∈ s, (f i : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ofReal_mul, ofReal_mul_cpow (hf i (by simp)),
      ← ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

/-- A principal power splits across a product when the sum of the arguments lies in the
principal range `(-π, π]`, including when either factor is zero. -/
theorem mul_cpow_of_arg_add_mem {x y : ℂ}
    (h : arg x + arg y ∈ Set.Ioc (-Real.pi) Real.pi) (w : ℂ) :
    (x * y) ^ w = x ^ w * y ^ w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_cpow hw]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [zero_cpow hw]
  rw [cpow_def_of_ne_zero (mul_ne_zero hx hy), cpow_def_of_ne_zero hx,
    cpow_def_of_ne_zero hy, log_mul hx hy h, add_mul, exp_add]

/-- A principal power splits across a product of two numbers in the open right half-plane.
Their arguments add without crossing the branch cut. -/
theorem mul_cpow_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (w : ℂ) :
    (x * y) ^ w = x ^ w * y ^ w := by
  have hax := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hay := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  exact mul_cpow_of_arg_add_mem ⟨by linarith, by linarith⟩ w

/-- A principal complex power of a natural power of a nonnegative real multiplies the exponents:
`((r : ℂ) ^ n) ^ s = (r : ℂ) ^ (n * s)`.  The argument of `(r : ℂ)` is `0`, so the principal branch
is not crossed. -/
theorem ofReal_pow_cpow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (s : ℂ) :
    ((r : ℂ) ^ n) ^ s = (r : ℂ) ^ (n * s) := by
  have harg : (r : ℂ).arg = 0 := arg_ofReal_of_nonneg hr
  rw [cpow_nat_mul' (by simp [harg, Real.pi_pos]) (by simp [harg, Real.pi_pos.le])]

/-- A principal complex power of a nonnegative real commutes with conjugation of the exponent:
`(r : ℂ) ^ conj s = conj ((r : ℂ) ^ s)`.  The argument of `(r : ℂ)` is `0`, so this is
`Complex.cpow_conj` without its branch hypothesis. -/
theorem ofReal_cpow_conj {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    (r : ℂ) ^ conj s = conj ((r : ℂ) ^ s) := by
  rw [Complex.cpow_conj _ _ (by simp [arg_ofReal_of_nonneg hr, Real.pi_pos.ne]), conj_ofReal]

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

/-- For a positive integer `n` and real `c`, the power `n ^ (c s)` is the exponential of the
real multiple `(c log n) s`. -/
theorem natCast_cpow_ofReal_mul {n : ℕ} (hn : n ≠ 0) (c : ℝ) (s : ℂ) :
    (n : ℂ) ^ ((c : ℂ) * s) = exp (((c * Real.log n : ℝ) : ℂ) * s) := by
  rw [cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← natCast_log]
  push_cast
  ring_nf

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

/-- The power coordinate `I * f ^ (1 / β)` is injective on a set where `f` is injective and
`f` is recovered by raising its principal `β`-th root to the `β`-th power. -/
theorem injOn_I_mul_cpow_inv {S : Set ℂ} {f : ℂ → ℂ} {β : ℝ} (hinj : Set.InjOn f S)
    (hrecover : ∀ z ∈ S, (f z ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = f z) :
    Set.InjOn (fun z => I * f z ^ ((β⁻¹ : ℝ) : ℂ)) S := fun z hz w hw hzw => by
  have hp : f z ^ ((β⁻¹ : ℝ) : ℂ) = f w ^ ((β⁻¹ : ℝ) : ℂ) := mul_left_cancel₀ I_ne_zero hzw
  exact hinj hz hw (by rw [← hrecover z hz, ← hrecover w hw, hp])

/-- **A local holomorphic branch of the `k`-th root.** Near a nonzero `z₀` with a chosen `k`-th
root `c`, there is a `k`-th root function which is complex differentiable at `z₀` and takes the
value `c` there, namely `z ↦ c * (z / z₀) ^ (k⁻¹ : ℂ)`. -/
theorem exists_differentiableAt_pow_eq {z₀ c : ℂ} {k : ℕ} (hk : k ≠ 0) (hz₀ : z₀ ≠ 0)
    (hc : c ^ k = z₀) :
    ∃ f : ℂ → ℂ, DifferentiableAt ℂ f z₀ ∧ f z₀ = c ∧ ∀ z, f z ^ k = z := by
  refine ⟨fun z ↦ c * (z / z₀) ^ (k⁻¹ : ℂ), ?_, by simp [div_self hz₀], fun z ↦ ?_⟩
  · exact ((differentiableAt_id.div_const _).cpow_const (by simp [div_self hz₀])).const_mul c
  · rw [mul_pow, cpow_nat_inv_pow _ hk, hc, mul_div_cancel₀ _ hz₀]

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
  have hseries := hq.hasFPowerSeriesAt.dslope_fslope
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

/-- Multiplying a principal power by the inverse of its base lowers the exponent by one:
`w ^ s * w⁻¹ = w ^ (s - 1)`. Away from `s = 1` this also holds at `w = 0`, where both sides
vanish. -/
theorem cpow_mul_inv {s : ℂ} (hs : s ≠ 1) (w : ℂ) : w ^ s * w⁻¹ = w ^ (s - 1) := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [inv_zero, mul_zero, zero_cpow (sub_ne_zero.mpr hs)]
  · rw [cpow_sub _ _ hw, cpow_one, div_eq_mul_inv]

/-- Multiplying a principal power by its base raises the exponent by one:
`w ^ (s + 1) = w ^ s * w`. Away from `s + 1 = 0` this also holds at `w = 0`, where both sides
vanish. -/
theorem cpow_add_one' {s : ℂ} (hs : s + 1 ≠ 0) (w : ℂ) : w ^ (s + 1) = w ^ s * w := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [zero_cpow hs, mul_zero]
  · rw [cpow_add _ _ hw, cpow_one]

/-- For `x ∈ slitPlane ∪ {0}` and a real exponent `r ≤ 0`, the principal power `(t + x) ^ r` is
`O(t ^ r)` for `t > 0`. -/
theorem exists_norm_ofReal_add_cpow_le_mul_rpow {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) {r : ℝ}
    (hr : r ≤ 0) : ∃ C, ∀ t : ℝ, 0 < t → ‖((t : ℂ) + x) ^ (r : ℂ)‖ ≤ C * t ^ r := by
  simp only [Complex.norm_cpow_real]
  rcases hx with hx | hx
  · obtain ⟨c, hc, h⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hx
    refine ⟨c ^ r, fun t ht => ?_⟩
    have h1 : c * t ≤ ‖(t : ℂ) + x‖ := by
      have : c * (1 + t) ≤ ‖x + (t : ℂ)‖ := h x (Metric.mem_ball_self hc) ⟨t, ht.le⟩
      rw [add_comm]
      nlinarith
    rw [← Real.mul_rpow hc.le ht.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 hr
  · refine ⟨1, fun t ht => ?_⟩
    rw [Set.mem_singleton_iff.mp hx, add_zero, Complex.norm_real,
      Real.norm_of_nonneg ht.le, one_mul]

/-- Near any `z ∈ slitPlane`, the principal power `((t : ℂ) + w) ^ s` is bounded by a constant
multiple of `(1 + t) ^ s.re` uniformly in `w` and in `t ≥ 0`, with no sign restriction on `s`. -/
theorem exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow {z : ℂ} (hz : z ∈ slitPlane)
    (s : ℂ) :
    ∃ U ∈ 𝓝 z, U ⊆ slitPlane ∧ ∃ C, 0 < C ∧
      ∀ w ∈ U, ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + w) ^ s‖ ≤ C * (1 + t) ^ s.re := by
  obtain ⟨c, hc, hlow⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  set M : ℝ := 1 + ‖z‖ + c
  have hM : 1 ≤ M := by
    have : 0 ≤ ‖z‖ := norm_nonneg z
    linarith
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  refine ⟨Metric.ball z c ∩ slitPlane,
    Filter.inter_mem (Metric.ball_mem_nhds z hc) (isOpen_slitPlane.mem_nhds hz),
    Set.inter_subset_right,
    max (c ^ s.re) (M ^ s.re) * Real.exp (Real.pi * |s.im|), by positivity, ?_⟩
  intro w hw t ht
  have hw_ball : w ∈ Metric.ball z c := hw.1
  have h1t : 0 < 1 + t := by linarith
  -- Lower bound `c * (1 + t) ≤ ‖(t : ℂ) + w‖` from the uniform slit-plane distance estimate.
  have hlower : c * (1 + t) ≤ ‖(t : ℂ) + w‖ := by
    rw [add_comm (t : ℂ) w]
    exact hlow w hw_ball ⟨t, ht⟩
  -- Upper bound `‖(t : ℂ) + w‖ ≤ M * (1 + t)` from the triangle inequality on `ball z c`.
  have hupper : ‖(t : ℂ) + w‖ ≤ M * (1 + t) := by
    have h := one_add_norm_add_le (t : ℂ) w
    rw [Complex.norm_real, Real.norm_of_nonneg ht] at h
    have hw_norm : ‖w‖ ≤ ‖z‖ + c := (norm_lt_of_mem_ball hw_ball).le
    nlinarith [norm_nonneg w, mul_le_mul_of_nonneg_right hw_norm h1t.le]
  -- Bound the radial factor `‖(t : ℂ) + w‖ ^ s.re` according to the sign of `s.re`.
  have hrpow : ‖(t : ℂ) + w‖ ^ s.re ≤ max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re := by
    rcases le_or_gt s.re 0 with hs | hs
    · calc ‖(t : ℂ) + w‖ ^ s.re
          ≤ (c * (1 + t)) ^ s.re := Real.rpow_le_rpow_of_nonpos (by positivity) hlower hs
        _ = c ^ s.re * (1 + t) ^ s.re := Real.mul_rpow hc.le h1t.le
        _ ≤ max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re := by
          gcongr
          exact le_max_left _ _
    · calc ‖(t : ℂ) + w‖ ^ s.re
          ≤ (M * (1 + t)) ^ s.re := Real.rpow_le_rpow (norm_nonneg _) hupper hs.le
        _ = M ^ s.re * (1 + t) ^ s.re := Real.mul_rpow hM0.le h1t.le
        _ ≤ max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re := by
          gcongr
          exact le_max_right _ _
  -- Bound the angular factor `1 / exp (arg * s.im) ≤ exp (π * |s.im|)`.
  have hexp := Complex.inv_exp_arg_mul_le_exp_pi_mul_abs ((t : ℂ) + w) s.im
  calc ‖((t : ℂ) + w) ^ s‖
      ≤ ‖(t : ℂ) + w‖ ^ s.re / Real.exp (((t : ℂ) + w).arg * s.im) :=
        Complex.norm_cpow_le _ _
    _ = ‖(t : ℂ) + w‖ ^ s.re * (Real.exp (((t : ℂ) + w).arg * s.im))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re) * Real.exp (Real.pi * |s.im|) :=
        mul_le_mul hrpow hexp (by positivity) (by positivity)
    _ = max (c ^ s.re) (M ^ s.re) * Real.exp (Real.pi * |s.im|) * (1 + t) ^ s.re := by ring

/-- For `x ∈ slitPlane` and any real exponent `r`, the principal power `(t + x) ^ r` is
`O((1 + t) ^ r)` for `t ≥ 0`. -/
theorem exists_norm_ofReal_add_cpow_le_mul_one_add_rpow {x : ℂ} (hx : x ∈ slitPlane) (r : ℝ) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + x) ^ (r : ℂ)‖ ≤ C * (1 + t) ^ r := by
  obtain ⟨U, hU, -, C, hC, h⟩ := exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hx r
  exact ⟨C, hC, fun t ht => by simpa using h x (mem_of_mem_nhds hU) t ht⟩

/-- For `x ∈ slitPlane` and a real exponent `r ≤ 0`, the principal power `(t + x) ^ r` is bounded
for `t ≥ 0`. -/
theorem exists_norm_ofReal_add_cpow_le {x : ℂ} (hx : x ∈ slitPlane) {r : ℝ} (hr : r ≤ 0) :
    ∃ C, ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + x) ^ (r : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_norm_ofReal_add_cpow_le_mul_one_add_rpow hx r
  exact ⟨C, fun t ht => (h t ht).trans <| mul_le_of_le_one_right hC.le <|
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hr⟩

/-- For `z ∈ slitPlane` and any `s : ℂ`, `‖((t : ℂ) + z) ^ s‖` is bounded below by a positive
multiple of `(1 + t) ^ s.re` for all `t ≥ 0`. -/
theorem exists_pos_mul_one_add_rpow_le_norm_ofReal_add_cpow {z : ℂ} (hz : z ∈ slitPlane)
    (s : ℂ) :
    ∃ c, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → c * (1 + t) ^ s.re ≤ ‖((t : ℂ) + z) ^ s‖ := by
  obtain ⟨U, hU, _, C, hC, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hz (-s)
  have hzU : z ∈ U := mem_of_mem_nhds hU
  refine ⟨C⁻¹, inv_pos.mpr hC, fun t ht => ?_⟩
  have h1t : 0 < 1 + t := by linarith
  have hne : ((t : ℂ) + z) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (slitPlane_ne_zero (ofReal_add_mem_slitPlane hz ht))]
    exact Complex.exp_ne_zero _
  -- Rewrite `C * ((1 + t) ^ s.re)⁻¹ = (C⁻¹ * (1 + t) ^ s.re)⁻¹` and invert.
  have h' : ‖((t : ℂ) + z) ^ s‖⁻¹ ≤ (C⁻¹ * (1 + t) ^ s.re)⁻¹ := by
    calc ‖((t : ℂ) + z) ^ s‖⁻¹
        ≤ C * (1 + t) ^ (-s).re := by
          simpa [Complex.cpow_neg, norm_inv] using hbound z hzU t ht
      _ = (C⁻¹ * (1 + t) ^ s.re)⁻¹ := by
          rw [Complex.neg_re, Real.rpow_neg h1t.le, mul_inv_rev, inv_inv, mul_comm]
  exact (inv_le_inv₀ (norm_pos_iff.mpr hne) (by positivity)).mp h'

/-- Around any `w₀ ∈ slitPlane`, there is an open ball inside `slitPlane` on which
`w ^ (σ + i y)` and its `w`-derivative `(σ + i y) w ^ (σ + i y - 1)` satisfy uniform exponential
bounds in `|y|` with rate strictly below `Real.pi`. -/
theorem exists_ball_slitPlane_cpow_le {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) (σ : ℝ) :
    ∃ ε > 0, ∃ θ < Real.pi, ∃ M > 0, ∀ w ∈ Metric.ball w₀ ε,
      w ∈ slitPlane ∧
        (∀ y : ℝ, ‖w ^ ((σ : ℂ) + y * I)‖ ≤ M * Real.exp (θ * |y|)) ∧
        (∀ y : ℝ, ‖((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)‖ ≤
          M * (1 + |y|) * Real.exp (θ * |y|)) := by
  have hr₀ : 0 < ‖w₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hw₀)
  have harg₀ : |w₀.arg| < Real.pi :=
    abs_lt.mpr ⟨neg_pi_lt_arg w₀, (arg_le_pi w₀).lt_of_ne (slitPlane_arg_ne_pi hw₀)⟩
  set θ : ℝ := (|w₀.arg| + Real.pi) / 2
  have hθ_lt : θ < Real.pi := by dsimp [θ]; linarith
  have hnhds : {w : ℂ | w ∈ slitPlane ∧ ‖w₀‖ / 2 < ‖w‖ ∧ ‖w‖ < 2 * ‖w₀‖ ∧ |w.arg| < θ} ∈ 𝓝 w₀ :=
    Filter.inter_mem (isOpen_slitPlane.mem_nhds hw₀) <|
      Filter.inter_mem
        (continuous_norm.continuousAt.eventually (Ioi_mem_nhds (half_lt_self hr₀))) <|
        Filter.inter_mem
          (continuous_norm.continuousAt.eventually (Iio_mem_nhds (by linarith)))
          ((continuous_abs.continuousAt.comp (continuousAt_arg hw₀)).eventually
            (Iio_mem_nhds (by dsimp [θ]; linarith)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let B (ρ : ℝ) : ℝ := max ((‖w₀‖ / 2) ^ ρ) ((2 * ‖w₀‖) ^ ρ)
  have hB_nonneg (ρ : ℝ) : 0 ≤ B ρ :=
    (Real.rpow_nonneg (by positivity) ρ).trans (le_max_left _ _)
  -- General vertical-line `cpow` bound at real part `ρ` on the annulus-sector neighborhood.
  have hcpow_le {w : ℂ} (hws : w ∈ slitPlane) (hw1 : ‖w₀‖ / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 2 * ‖w₀‖)
      (hwarg : |w.arg| < θ) (ρ y : ℝ) :
      ‖w ^ ((ρ : ℂ) + y * I)‖ ≤ B ρ * Real.exp (θ * |y|) := by
    have hrpow : ‖w‖ ^ ρ ≤ B ρ := by
      rcases le_total 0 ρ with hρ | hρ
      · exact (Real.rpow_le_rpow (by positivity) hw2 hρ).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos (by positivity) hw1 hρ).trans (le_max_left _ _)
    have hexp : -(w.arg * y) ≤ θ * |y| :=
      (neg_le_abs _).trans <| (abs_mul w.arg y).le.trans
        (mul_le_mul_of_nonneg_right hwarg.le (abs_nonneg y))
    rw [norm_cpow_of_ne_zero (slitPlane_ne_zero hws), div_eq_mul_inv, ← Real.exp_neg]
    have hre : ((ρ : ℂ) + y * I).re = ρ := by simp
    have him : ((ρ : ℂ) + y * I).im = y := by simp
    rw [hre, him]
    exact mul_le_mul hrpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (hB_nonneg ρ)
  set M : ℝ := max (B σ) (max 1 |σ| * B (σ - 1)) + 1
  have hM : 0 < M := by
    have : 0 ≤ max (B σ) (max 1 |σ| * B (σ - 1)) := (hB_nonneg σ).trans (le_max_left _ _)
    dsimp [M]; linarith
  refine ⟨ε, hε, θ, hθ_lt, M, hM, fun w hw ↦ ?_⟩
  obtain ⟨hws, hw1, hw2, hwarg⟩ := hball hw
  refine ⟨hws, fun y ↦ ?_, fun y ↦ ?_⟩
  · exact (hcpow_le hws hw1.le hw2.le hwarg σ y).trans <|
      mul_le_mul_of_nonneg_right
        (by dsimp [M]; linarith [le_max_left (B σ) (max 1 |σ| * B (σ - 1))]) (Real.exp_pos _).le
  · have hsub (y : ℝ) : (σ : ℂ) + y * I - 1 = ((σ - 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    have hlin (y : ℝ) : ‖(σ : ℂ) + y * I‖ ≤ max 1 |σ| * (1 + |y|) :=
      calc ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := by
              simpa using norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I)
        _ ≤ max 1 |σ| * 1 + max 1 |σ| * |y| :=
            add_le_add (by simp) (le_mul_of_one_le_left (abs_nonneg y) (le_max_left 1 |σ|))
        _ = max 1 |σ| * (1 + |y|) := by ring
    rw [norm_mul, hsub y]
    calc ‖(σ : ℂ) + y * I‖ * ‖w ^ (((σ - 1 : ℝ) : ℂ) + y * I)‖
        ≤ (max 1 |σ| * (1 + |y|)) * (B (σ - 1) * Real.exp (θ * |y|)) :=
          mul_le_mul (hlin y) (hcpow_le hws hw1.le hw2.le hwarg (σ - 1) y)
            (norm_nonneg _) (by positivity)
      _ = (max 1 |σ| * B (σ - 1)) * (1 + |y|) * Real.exp (θ * |y|) := by ring
      _ ≤ M * (1 + |y|) * Real.exp (θ * |y|) := by
          gcongr; dsimp [M]; linarith [le_max_right (B σ) (max 1 |σ| * B (σ - 1))]

/-- For `x ∈ slitPlane ∪ {0}` and any complex exponent `s`, the principal power `(t + x) ^ s` is
continuous in the real variable `t > 0`. -/
theorem continuousOn_ofReal_add_cpow {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) (s : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) + x) ^ s) (Set.Ioi 0) := fun _ ht =>
  ((Complex.continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
    (ofReal_add_mem_slitPlane_of_mem_union hx ht)).continuousWithinAt

/-- For `x ∈ slitPlane` and any complex exponent `s`, the principal power `(t + x) ^ s` is
continuous in the real variable `t ≥ 0`. -/
theorem continuousOn_ofReal_add_cpow_Ici {x : ℂ} (hx : x ∈ slitPlane) (s : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) + x) ^ s) (Set.Ici 0) := fun _ ht =>
  ((Complex.continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
    (ofReal_add_mem_slitPlane hx ht)).continuousWithinAt

/-- For any `x` and a complex exponent `s` with `0 < s.re`, the principal power `(t + x) ^ s` is
continuous in the real variable `t`. -/
theorem continuous_ofReal_add_cpow_of_re_pos {x : ℂ} {s : ℂ} (hs : 0 < s.re) :
    Continuous (fun t : ℝ => ((t : ℂ) + x) ^ s) := by
  by_cases him : x.im = 0
  · -- `t + x` is the real number `t + x.re`, and real-base powers are continuous.
    have hx : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have h := (Complex.continuous_ofReal_cpow_const hs).comp
      (continuous_id.add (continuous_const (y := x.re)))
    convert h using 2 with t
    rw [hx]
    simp
  · refine continuous_iff_continuousAt.2 fun t => ?_
    exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + x)
      (Complex.continuousAt_cpow_const_of_re_pos (Or.inr (by simpa using him)) hs) (by fun_prop)

/-- For `w` off the negative real axis and `p ≥ 0`, the principal powers combine:
`w⁻ʳ * pʳ = (p / w)ʳ`. -/
theorem one_div_cpow_mul_ofReal_rpow {w : ℂ} (hw : w.arg ≠ Real.pi) {p : ℝ} (hp : 0 ≤ p) (r : ℝ) :
    (1 / w ^ (r : ℂ)) * ((p ^ r : ℝ) : ℂ) = ((p : ℂ) / w) ^ (r : ℂ) := by
  rw [div_eq_mul_inv (p : ℂ) w, ofReal_mul_cpow hp, Complex.inv_cpow w (r : ℂ) hw,
    ← Complex.ofReal_cpow hp, one_div, mul_comm]

/-- For `a > 0` and `w` off the negative real axis, the principal powers combine:
`a ^ s * (a⁻¹ * w⁻¹) ^ s = w ^ (-s)`. -/
theorem ofReal_cpow_mul_inv_mul_inv_cpow {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w.arg ≠ Real.pi)
    (s : ℂ) : (a : ℂ) ^ s * ((a : ℂ)⁻¹ * w⁻¹) ^ s = w ^ (-s) := by
  have has : (a : ℂ) ^ s ≠ 0 := by simp [ha.ne']
  rw [mul_cpow (by simpa [← ofReal_inv, arg_ofReal_of_nonneg (inv_nonneg.2 ha.le)]
      using arg_mem_Ioc w⁻¹),
    inv_cpow_ofReal_nonneg ha.le, inv_cpow _ _ hw, cpow_neg]
  field_simp

end TauCeti

namespace Complex

/-- An exponential based at a principal logarithm splits into a principal power and the
exponential of the remaining summand. -/
theorem exp_log_add_mul {z : ℂ} (hz : z ≠ 0) (w e : ℂ) :
    exp ((log z + w) * e) = z ^ e * exp (w * e) := by
  rw [add_mul, exp_add, cpow_def_of_ne_zero hz]

/-- The product of two principal powers `w ^ (-1/2)` is `w⁻¹`, including at `w = 0`. -/
theorem cpow_neg_half_mul_self (w : ℂ) : w ^ (-(1 / 2) : ℂ) * w ^ (-(1 / 2) : ℂ) = w⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [← cpow_add _ _ hw]
    norm_num [cpow_neg_one]

/-- Multiplying the principal power `w ^ (-1/2)` by `w` gives `w ^ (1/2)`, including at
`w = 0`. -/
theorem cpow_neg_half_mul_eq_cpow_half (w : ℂ) : w ^ (-(1 / 2) : ℂ) * w = w ^ (1 / 2 : ℂ) := by
  rw [← TauCeti.cpow_add_one' (by norm_num)]
  norm_num

/-- For any complex `x` and real `s > 0`, `(t + x) ^ (-s)` tends to `0` as the real number `t`
tends to `∞`. -/
theorem tendsto_ofReal_add_cpow_neg (x : ℂ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t : ℝ => ((t : ℂ) + x) ^ (-(s : ℂ))) atTop (𝓝 0) := by
  -- `‖t + x‖ ≥ t - ‖x‖` by the triangle inequality.
  have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) + x‖) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-‖x‖) tendsto_id)
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h := norm_add_le ((t : ℂ) + x) (-x)
    rw [add_neg_cancel_right, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht] at h
    simp only [id]
    linarith
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simp only [← Complex.ofReal_neg, Complex.norm_cpow_real]
  exact (tendsto_rpow_neg_atTop hs).comp hnorm

/-- For `0 < re y`, `N ^ (-y)` tends to `0` along the natural numbers. -/
theorem tendsto_natCast_cpow_neg_atTop {y : ℂ} (hy : 0 < y.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (-y)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine ((tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [norm_natCast_cpow_of_pos hN, neg_re, Function.comp_apply]

/-- The function `t ↦ -2 (t + x)^(1/2) (t + y)⁻¹` is continuous at `0`, even when
`x = 0` (as `re (1/2) > 0`). -/
theorem continuousAt_neg_two_cpow_half_mul_inv {x y : ℂ} (hy : y ≠ 0) :
    ContinuousAt
      (fun t : ℝ => -2 * ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y)⁻¹) 0 := by
  have hc2 : ContinuousAt (fun t : ℝ => ((t : ℂ) + y)⁻¹) 0 :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + y).continuousAt.inv₀
      (by rwa [ofReal_zero, zero_add])
  exact (continuousAt_const.mul
    (TauCeti.continuous_ofReal_add_cpow_of_re_pos (by norm_num)).continuousAt).mul hc2

/-- The derivative of `t ↦ -2 (t + x)^(1/2) (t + y)⁻¹` on `(0, ∞)`:
`(t + x)^(-1/2) (t + y)⁻¹ - 2 (y - x) (t + x)^(-1/2) (t + y)^(-1/2) (t + y)^(-1/2) (t + y)⁻¹`.
For the Carlson integrals this is the `R_C(x, y)` integrand minus `2 (y - x)` times the
`R_D(x, y, y)` integrand. -/
theorem hasDerivAt_neg_two_cpow_half_mul_inv {x y : ℂ}
    (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane ∪ {0}) :
    ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => -2 * ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y)⁻¹)
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y)⁻¹ -
        2 * (y - x) * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y)⁻¹)) t := by
  intro t ht
  have htx : (t : ℂ) + x ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane_of_mem_union hx ht
  have hty : (t : ℂ) + y ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane_of_mem_union hy ht
  have hty_ne : (t : ℂ) + y ≠ 0 := slitPlane_ne_zero hty
  have hd1 : HasDerivAt (fun s : ℝ => ((s : ℂ) + x) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * ((t : ℂ) + x) ^ ((1 / 2 : ℂ) - 1) * 1) t := by
    simpa using (((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := (1 / 2 : ℂ))
      htx).comp_ofReal
  have hd2 : HasDerivAt (fun s : ℝ => ((s : ℂ) + y)⁻¹) (-(((t : ℂ) + y) ^ 2)⁻¹) t := by
    simpa [div_eq_mul_inv] using (((hasDerivAt_id (t : ℂ)).add_const y).inv hty_ne).comp_ofReal
  refine ((hd1.const_mul (-2 : ℂ)).fun_mul hd2).congr_deriv ?_
  simp only [mul_one]
  have hpow1 : ((t : ℂ) + x) ^ ((1 / 2 : ℂ) - 1) = ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) := by norm_num
  have hpow2 := (cpow_neg_half_mul_eq_cpow_half ((t : ℂ) + x)).symm
  rw [hpow1, hpow2]
  set u : ℂ := ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)
  set v : ℂ := (t : ℂ) + y
  have hv : v ^ (-(1 / 2) : ℂ) * v ^ (-(1 / 2) : ℂ) = v⁻¹ := cpow_neg_half_mul_self _
  have hv_inv : v * v⁻¹ = 1 := mul_inv_cancel₀ hty_ne
  have hv2 : (v ^ 2)⁻¹ = v⁻¹ * v⁻¹ := by rw [sq, mul_inv]
  have htx_eq : (t : ℂ) + x = v - (y - x) := by simp [v]; ring
  rw [hv2, htx_eq, mul_assoc u, hv]
  linear_combination (2 * u * v⁻¹) * hv_inv

/-- The function `t ↦ -2 (t + x)^(1/2) (t + y)⁻¹` tends to `0` as `t → ∞`. -/
theorem tendsto_neg_two_cpow_half_mul_inv_atTop {x y : ℂ} :
    Tendsto (fun t : ℝ => -2 * ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y)⁻¹) atTop (𝓝 0) := by
  have h0 : Tendsto
      (fun t : ℝ => 2 * (1 + ‖x‖) ^ (1 / 2 : ℝ) * 4 * (1 + t) ^ (-(1 / 2) : ℝ))
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_mul
      (2 * (1 + ‖x‖) ^ (1 / 2 : ℝ) * 4)
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop (max 1 (2 * ‖y‖))] with t ht'
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht'
  have hty : 2 * ‖y‖ ≤ t := (le_max_right _ _).trans ht'
  have ht : 0 ≤ t := by linarith
  have h1t : 0 < 1 + t := by linarith
  -- Far out, `‖t + y‖ ≥ t - ‖y‖ ≥ t / 2 ≥ (1 + t) / 4`.
  have hCy : ‖((t : ℂ) + y)⁻¹‖ ≤ 4 * (1 + t)⁻¹ := by
    have hlow : (1 + t) / 4 ≤ ‖(t : ℂ) + y‖ := by
      have h := norm_add_le ((t : ℂ) + y) (-y)
      rw [add_neg_cancel_right, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht] at h
      linarith
    rw [norm_inv]
    calc ‖(t : ℂ) + y‖⁻¹ ≤ ((1 + t) / 4)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 4 * (1 + t)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have htx_le : ‖(t : ℂ) + x‖ ≤ (1 + ‖x‖) * (1 + t) := by
    calc ‖(t : ℂ) + x‖ ≤ ‖(t : ℂ)‖ + ‖x‖ := norm_add_le _ _
      _ = t + ‖x‖ := by rw [norm_real, Real.norm_of_nonneg ht]
      _ ≤ (1 + ‖x‖) * (1 + t) := by nlinarith [norm_nonneg x]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hcpow_le : ‖((t : ℂ) + x) ^ (1 / 2 : ℂ)‖ ≤
      (1 + ‖x‖) ^ (1 / 2 : ℝ) * (1 + t) ^ (1 / 2 : ℝ) := by
    rw [hhalf, norm_cpow_real, ← Real.mul_rpow (by positivity) h1t.le]
    exact Real.rpow_le_rpow (norm_nonneg _) htx_le (by norm_num)
  have hrpow : (1 + t) ^ (1 / 2 : ℝ) * (1 + t)⁻¹ = (1 + t) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add h1t]; norm_num
  simp only [norm_mul, norm_neg, norm_ofNat]
  calc 2 * ‖((t : ℂ) + x) ^ (1 / 2 : ℂ)‖ * ‖((t : ℂ) + y)⁻¹‖
      ≤ 2 * ((1 + ‖x‖) ^ (1 / 2 : ℝ) * (1 + t) ^ (1 / 2 : ℝ)) * (4 * (1 + t)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcpow_le zero_le_two) hCy
          (norm_nonneg _) (by positivity)
    _ = 2 * (1 + ‖x‖) ^ (1 / 2 : ℝ) * 4 * ((1 + t) ^ (1 / 2 : ℝ) * (1 + t)⁻¹) := by ring
    _ = 2 * (1 + ‖x‖) ^ (1 / 2 : ℝ) * 4 * (1 + t) ^ (-(1 / 2) : ℝ) := by rw [hrpow]

/-- The principal power of a complex number `u` by a real exponent `r` has positive imaginary part
when `arg u * r` lies in `(0, π)`. -/
theorem im_cpow_ofReal_pos {u : ℂ} {r : ℝ} (h0 : 0 < arg u * r) (hπ : arg u * r < Real.pi) :
    0 < (u ^ (r : ℂ)).im := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h0
  rw [cpow_ofReal_im]
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hu) _)
    (Real.sin_pos_of_pos_of_lt_pi h0 hπ)

/-- The principal power of a complex number by a real exponent `r` is real when `arg u * r` is `0`
or `π`. -/
theorem im_cpow_ofReal_eq_zero {u : ℂ} {r : ℝ} (h : arg u * r = 0 ∨ arg u * r = Real.pi) :
    (u ^ (r : ℂ)).im = 0 := by
  rw [cpow_ofReal_im]
  rcases h with h | h <;> rw [h] <;> simp

/-- A real power of a positive real number grows at most exponentially in the exponent. -/
theorem norm_ofReal_cpow_le_exp {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ‖(a : ℂ) ^ w‖ ≤ Real.exp (|Real.log a| * ‖w‖) := by
  rw [norm_cpow_eq_rpow_re_of_pos ha, Real.rpow_def_of_pos ha]
  exact Real.exp_le_exp.mpr <| (le_abs_self _).trans <| by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_re_le_norm w) (abs_nonneg _)

/-- On the closed unit disk `‖z‖ ≤ 1` and for `0 ≤ t < 1`, the principal power `(1 - z * t) ^ s`
has norm at most `exp (π * |s.im|) * (2 ^ s.re + (1 - t) ^ s.re)` for any complex exponent `s`. -/
theorem norm_one_sub_mul_ofReal_cpow_le (s : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ‖(1 - z * (t : ℂ)) ^ s‖ ≤
      Real.exp (Real.pi * |s.im|) * (2 ^ s.re + (1 - t) ^ s.re) := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht₁
  have hzt_le : ‖z * (t : ℂ)‖ ≤ t := by
    rw [norm_mul, Complex.norm_of_nonneg ht₀]
    exact mul_le_of_le_one_left ht₀ hz
  have h_low : 1 - t ≤ ‖(1 : ℂ) - z * (t : ℂ)‖ := by
    linarith [norm_sub_norm_le (1 : ℂ) (z * (t : ℂ)), norm_one (α := ℂ)]
  have h_high : ‖(1 : ℂ) - z * (t : ℂ)‖ ≤ 2 :=
    (norm_sub_le 1 (z * (t : ℂ))).trans (by rw [norm_one]; linarith)
  have hexp := inv_exp_arg_mul_le_exp_pi_mul_abs (1 - z * (t : ℂ)) s.im
  have hrpow : ‖(1 : ℂ) - z * (t : ℂ)‖ ^ s.re ≤ 2 ^ s.re + (1 - t) ^ s.re := by
    rcases le_total 0 s.re with hre | hre
    · exact (Real.rpow_le_rpow (norm_nonneg _) h_high hre).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg h1t_pos.le _))
    · exact (Real.rpow_le_rpow_of_nonpos h1t_pos h_low hre).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg zero_le_two _))
  calc ‖(1 - z * (t : ℂ)) ^ s‖
      ≤ ‖(1 : ℂ) - z * (t : ℂ)‖ ^ s.re *
          (Real.exp (arg (1 - z * (t : ℂ)) * s.im))⁻¹ := by
        rw [← div_eq_mul_inv]; exact norm_cpow_le _ _
    _ ≤ (2 ^ s.re + (1 - t) ^ s.re) * Real.exp (Real.pi * |s.im|) :=
        mul_le_mul hrpow hexp (inv_nonneg.mpr (Real.exp_pos _).le)
          (add_nonneg (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg h1t_pos.le _))
    _ = Real.exp (Real.pi * |s.im|) * (2 ^ s.re + (1 - t) ^ s.re) := mul_comm _ _

/-- Raising the reciprocal `(z ^ (1 / 2))⁻¹` of the principal half-power to any complex exponent `w`
gives `z ^ (-w / 2)` for all `z, w : ℂ`. -/
theorem inv_cpow_half_cpow (z w : ℂ) : (z ^ (1 / 2 : ℂ))⁻¹ ^ w = z ^ (-w / 2) := by
  have him : (log z * -(1 / 2 : ℂ)).im = -arg z / 2 := by simp [div_eq_mul_inv, log_im]
  rw [← cpow_neg, ← cpow_mul _ (by rw [him]; linarith [arg_le_pi z, Real.pi_pos])
    (by rw [him]; linarith [neg_pi_lt_arg z, Real.pi_pos])]
  congr 1
  ring

/-- For any complex base `w` and exponent `d`,
`‖w ^ d‖ ≤ ‖w‖ ^ d.re * exp (|w.arg| * |d.im|)`. -/
theorem norm_cpow_le_mul_exp_arg (w d : ℂ) :
    ‖w ^ d‖ ≤ ‖w‖ ^ d.re * Real.exp (|w.arg| * |d.im|) := by
  calc ‖w ^ d‖ ≤ ‖w‖ ^ d.re / Real.exp (w.arg * d.im) := norm_cpow_le w d
    _ = ‖w‖ ^ d.re * Real.exp (-(w.arg * d.im)) := by rw [div_eq_mul_inv, Real.exp_neg]
    _ ≤ ‖w‖ ^ d.re * Real.exp (|w.arg| * |d.im|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (Real.rpow_nonneg (norm_nonneg w) _)
        rw [← abs_mul]
        exact neg_le_abs _

/-- On a vertical strip `d.re ∈ [a, b]`, a nonzero base `w` satisfies the uniform bound
`‖w ^ d‖ ≤ max (‖w‖ ^ a) (‖w‖ ^ b) * exp (|w.arg| * |d.im|)`. -/
theorem norm_cpow_le_max_mul_exp_arg_of_re_mem_Icc {w : ℂ} (hw : w ≠ 0) {a b : ℝ} {d : ℂ}
    (hd : d.re ∈ Set.Icc a b) :
    ‖w ^ d‖ ≤ max (‖w‖ ^ a) (‖w‖ ^ b) * Real.exp (|w.arg| * |d.im|) := by
  refine (norm_cpow_le_mul_exp_arg w d).trans <| mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rcases le_total 1 ‖w‖ with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hd.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hw) h1 hd.1).trans (le_max_left _ _)

/-- For any complex base `w` and exponent `d`, `‖w ^ d‖ ≤ ‖w‖ ^ d.re * exp (π * |d.im|)`. -/
theorem norm_cpow_le_mul_exp (w d : ℂ) :
    ‖w ^ d‖ ≤ ‖w‖ ^ d.re * Real.exp (Real.pi * |d.im|) := by
  calc ‖w ^ d‖ ≤ ‖w‖ ^ d.re / Real.exp (w.arg * d.im) := norm_cpow_le w d
    _ = ‖w‖ ^ d.re * (Real.exp (w.arg * d.im))⁻¹ := div_eq_mul_inv _ _
    _ ≤ ‖w‖ ^ d.re * Real.exp (Real.pi * |d.im|) :=
        mul_le_mul_of_nonneg_left (inv_exp_arg_mul_le_exp_pi_mul_abs w d.im)
          (Real.rpow_nonneg (norm_nonneg w) _)

/-- For `z` in the closed right half-plane (`0 ≤ z.re`) and any `d : ℂ`,
`‖(1 + z) ^ d‖ ≤ exp (π * |d.im|) * (1 + ‖z‖) ^ max 0 d.re`. -/
theorem norm_one_add_cpow_le {z : ℂ} (hz : 0 ≤ z.re) (d : ℂ) :
    ‖(1 + z) ^ d‖ ≤ Real.exp (Real.pi * |d.im|) * (1 + ‖z‖) ^ max 0 d.re := by
  have hrpow : ‖1 + z‖ ^ d.re ≤ (1 + ‖z‖) ^ max 0 d.re := by
    rcases le_or_gt d.re 0 with hd | hd
    · rw [max_eq_left hd, Real.rpow_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_one_add hz) hd
    · rw [max_eq_right hd.le]
      exact Real.rpow_le_rpow (norm_nonneg _) ((norm_add_le 1 z).trans_eq (by simp)) hd.le
  exact (norm_cpow_le_mul_exp _ _).trans <|
    (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le)

/-- Along any ray `1 + r * exp (θ * I)` avoiding the negative real axis (`|θ| < π`, `0 ≤ r`),
`‖(1 + r * exp (θ * I)) ^ d‖ ≤ exp (π * |d.im|) * (cos (θ / 2)) ^ min 0 d.re *
(1 + r) ^ max 0 d.re`. -/
theorem norm_one_add_ofReal_mul_exp_mul_I_cpow_le {θ r : ℝ} (hθ : |θ| < Real.pi)
    (hr : 0 ≤ r) (d : ℂ) :
    ‖(1 + (r : ℂ) * exp ((θ : ℂ) * I)) ^ d‖ ≤
      Real.exp (Real.pi * |d.im|) * (Real.cos (θ / 2)) ^ min 0 d.re *
        (1 + r) ^ max 0 d.re := by
  set w : ℂ := 1 + (r : ℂ) * exp ((θ : ℂ) * I)
  obtain ⟨hθ₁, hθ₂⟩ := abs_lt.mp hθ
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hw_lo : Real.cos (θ / 2) ≤ ‖w‖ :=
    (le_mul_of_one_le_left hc.le (by linarith)).trans
      (one_add_mul_cos_div_two_le_norm_one_add_ofReal_mul_exp_mul_I θ r)
  have hw_hi : ‖w‖ ≤ 1 + r :=
    (norm_one_add_ofReal_mul_exp_mul_I_le θ r).trans_eq (by rw [abs_of_nonneg hr])
  have hrpow : ‖w‖ ^ d.re ≤ (Real.cos (θ / 2)) ^ min 0 d.re * (1 + r) ^ max 0 d.re := by
    rcases le_or_gt d.re 0 with hd | hd
    · rw [min_eq_right hd, max_eq_left hd, Real.rpow_zero, mul_one]
      exact Real.rpow_le_rpow_of_nonpos hc hw_lo hd
    · rw [min_eq_left hd.le, max_eq_right hd.le, Real.rpow_zero, one_mul]
      exact Real.rpow_le_rpow (norm_nonneg _) hw_hi hd.le
  exact (norm_cpow_le_mul_exp w d).trans <|
    (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le).trans_eq (by ring)

/-- For every complex number `w`, the principal square root `(-w) ^ (1 / 2 : ℂ)` equals either
`I * w ^ (1 / 2 : ℂ)` or `-(I * w ^ (1 / 2 : ℂ))`, since both sides square to `-w`. -/
theorem neg_cpow_half_eq_or_eq_neg (w : ℂ) :
    (-w) ^ (1 / 2 : ℂ) = I * w ^ (1 / 2 : ℂ) ∨
      (-w) ^ (1 / 2 : ℂ) = -(I * w ^ (1 / 2 : ℂ)) :=
  sq_eq_sq_iff_eq_or_eq_neg.mp <| by rw [mul_pow, I_sq]; simp [one_div]

end Complex

/-- Derivative of the principal square root `w ↦ f w ^ (1 / 2 : ℂ)` at a point where `f x` lies
in `Complex.slitPlane`: the derivative is `f' / (2 * f x ^ (1 / 2 : ℂ))`. The variable ranges over
any nontrivially normed field `𝕜` over which `ℂ` is a normed algebra, such as `ℝ` or `ℂ`. -/
theorem HasDerivAt.cpow_half {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {f : 𝕜 → ℂ} {f' : ℂ} {x : 𝕜} (hf : HasDerivAt f f' x) (hx : f x ∈ Complex.slitPlane) :
    HasDerivAt (fun w : 𝕜 ↦ f w ^ (1 / 2 : ℂ)) (f' / (2 * f x ^ (1 / 2 : ℂ))) x := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) hx).hasDerivAt.comp x hf
  have hm : f x ^ ((1 / 2 : ℂ) - 1) * f x ^ (1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ (slitPlane_ne_zero hx)]
    norm_num
  have h0 : f x ^ (1 / 2 : ℂ) ≠ 0 := by simp [cpow_eq_zero_iff, slitPlane_ne_zero hx]
  exact h.congr_deriv (by rw [eq_inv_of_mul_eq_one_left hm]; field_simp [h0])

end
