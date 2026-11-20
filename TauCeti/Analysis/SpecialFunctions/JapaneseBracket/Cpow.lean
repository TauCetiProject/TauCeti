/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Complex powers of the Japanese bracket

On a real normed space `E`, write `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)` for the Japanese bracket. For a
complex number `z` its complex power is Mathlib's complex power of the positive real
`1 + ‖x‖ ^ 2`,

`⟨x⟩ ^ z = (1 + ‖x‖ ^ 2) ^ (z / 2) = exp (z log (1 + ‖x‖ ^ 2) / 2)`
(`TauCeti.japaneseBracketCpow z x`). Naming it lets it be passed as a Fourier symbol.

For real `z = s` this is the real power `(1 + ‖x‖ ^ 2) ^ (s / 2)`, the symbol of the Bessel
potential of order `s`. In general its modulus is the real power of order `re z`, so an
imaginary power `⟨x⟩ ^ (i y)` has modulus one. The powers are multiplicative in the exponent, and
`z ↦ ⟨x⟩ ^ z` is entire with derivative `⟨x⟩ ^ z log ⟨x⟩`. When the domain is a real inner product
space, the function `x ↦ ⟨x⟩ ^ z` has temperate growth for each `z`. On a finite-dimensional real
inner product space it is therefore a Fourier multiplier on Schwartz functions: these are the
Bessel potentials of complex order, which depend holomorphically on the order and are used to
interpolate operators between Bessel-potential spaces.

In `x`, the power `⟨x⟩ ^ z` is a symbol of order `re z`: its `k`-th derivative is
`O((1 + ‖z‖) ^ k ⟨x⟩ ^ (re z - k))`, with a constant independent of `z`. The derivative
`D ⟨x⟩ ^ z = z ⟨x⟩ ^ (z - 2) ⟪x, ·⟫` is a power of order `re z - 2` times a linear map, and the
bound follows by induction on `k` with the Leibniz rule; each derivative costs at most one factor
`1 + ‖z‖`. For `re z ≤ 0` this is Mihlin's condition with a constant polynomial in `z`, which is
what makes the imaginary powers `⟨ξ⟩ ^ (i τ)` multipliers on `Lᵖ` with norm polynomial in `τ`.

## Main declarations

* `TauCeti.japaneseBracketCpow z x`: the complex power `⟨x⟩ ^ z`, with its exponential form
  `TauCeti.japaneseBracketCpow_eq_exp`.
* `TauCeti.japaneseBracketCpow_ofReal`: for real `s` it is `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TauCeti.norm_japaneseBracketCpow`: `‖⟨x⟩ ^ z‖ = (1 + ‖x‖ ^ 2) ^ (re z / 2)`.
* `TauCeti.japaneseBracketCpow_add`: `⟨x⟩ ^ (z + w) = ⟨x⟩ ^ z ⟨x⟩ ^ w`, with
  `TauCeti.japaneseBracketCpow_neg` and `TauCeti.japaneseBracketCpow_conj`.
* `TauCeti.hasDerivAt_japaneseBracketCpow`: the derivative in the exponent, and the uniform
  second-order remainder bound `TauCeti.norm_japaneseBracketCpow_add_sub_sub_le`.
* `TauCeti.hasTemperateGrowth_japaneseBracketCpow`: on a real inner product space,
  `x ↦ ⟨x⟩ ^ z` has temperate growth.
* `TauCeti.contDiff_japaneseBracketCpow` and `TauCeti.hasFDerivAt_japaneseBracketCpow`:
  `x ↦ ⟨x⟩ ^ z` is smooth, with derivative `z ⟨x⟩ ^ (z - 2) ⟪x, ·⟫`.
* `TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le`: the symbol estimates
  `‖D^k ⟨x⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ k (1 + ‖x‖ ^ 2) ^ ((re z - k) / 2)`, uniformly in `z`.
* `TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow`: for `re z ≤ 0`, Mihlin's
  condition `‖D^k ⟨ξ⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ k / ‖ξ‖ ^ k`.
* `TauCeti.exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le`: the real-order case,
  symbol estimates of order `s` for the complex Bessel weight `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
-/

public section

noncomputable section

namespace TauCeti

open Complex

variable {E : Type*} [NormedAddCommGroup E]

/-- The complex power `⟨x⟩ ^ z = (1 + ‖x‖ ^ 2) ^ (z / 2)` of the Japanese bracket
`⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`, as Mathlib's complex power `Complex.cpow` of the positive real
`1 + ‖x‖ ^ 2`. -/
def japaneseBracketCpow (z : ℂ) (x : E) : ℂ :=
  ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ (z / 2)

theorem japaneseBracketCpow_def (z : ℂ) (x : E) :
    japaneseBracketCpow z x = ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ (z / 2) := (rfl)

/-- Since the base is a positive real, `⟨x⟩ ^ z = exp (z log (1 + ‖x‖ ^ 2) / 2)`. -/
theorem japaneseBracketCpow_eq_exp (z : ℂ) (x : E) :
    japaneseBracketCpow z x = exp (z * (Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ)) := by
  rw [japaneseBracketCpow, cpow_def_of_ne_zero (ofReal_ne_zero.2 (by positivity)),
    ← ofReal_log (by positivity)]
  push_cast
  ring_nf

/-- For a real exponent `s`, the complex power is the real power `(1 + ‖x‖ ^ 2) ^ (s / 2)`. -/
theorem japaneseBracketCpow_ofReal (s : ℝ) (x : E) :
    japaneseBracketCpow (s : ℂ) x = (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := by
  rw [japaneseBracketCpow, ofReal_cpow (by positivity)]
  push_cast
  rfl

@[simp]
theorem japaneseBracketCpow_zero (x : E) : japaneseBracketCpow 0 x = 1 := by
  rw [japaneseBracketCpow, zero_div, cpow_zero]

@[simp]
theorem japaneseBracketCpow_zero_right (z : ℂ) : japaneseBracketCpow z (0 : E) = 1 := by
  simp [japaneseBracketCpow]

@[simp]
theorem japaneseBracketCpow_neg_right (z : ℂ) (x : E) :
    japaneseBracketCpow z (-x) = japaneseBracketCpow z x := by
  rw [japaneseBracketCpow, japaneseBracketCpow, norm_neg]

@[simp]
theorem japaneseBracketCpow_ne_zero (z : ℂ) (x : E) : japaneseBracketCpow z x ≠ 0 := by
  rw [japaneseBracketCpow_eq_exp]
  exact exp_ne_zero _

/-- The power of order `-z` is the reciprocal of the power of order `z`. -/
theorem japaneseBracketCpow_neg (z : ℂ) (x : E) :
    japaneseBracketCpow (-z) x = (japaneseBracketCpow z x)⁻¹ := by
  rw [japaneseBracketCpow, japaneseBracketCpow, neg_div, cpow_neg]

/-- The power of order `conj z` is the complex conjugate of the power of order `z`. -/
@[simp]
theorem japaneseBracketCpow_conj (z : ℂ) (x : E) :
    japaneseBracketCpow (starRingEnd ℂ z) x = starRingEnd ℂ (japaneseBracketCpow z x) := by
  rw [japaneseBracketCpow_eq_exp, japaneseBracketCpow_eq_exp, ← exp_conj, map_mul, conj_ofReal]

/-- The modulus of `⟨x⟩ ^ z` is the real power of order `re z`. -/
@[simp]
theorem norm_japaneseBracketCpow (z : ℂ) (x : E) :
    ‖japaneseBracketCpow z x‖ = (1 + ‖x‖ ^ 2) ^ (z.re / 2) := by
  rw [japaneseBracketCpow, norm_cpow_eq_rpow_re_of_pos (by positivity), div_ofNat_re]

/-- The complex powers are multiplicative in the exponent. -/
theorem japaneseBracketCpow_add (z w : ℂ) (x : E) :
    japaneseBracketCpow (z + w) x = japaneseBracketCpow z x * japaneseBracketCpow w x := by
  rw [japaneseBracketCpow, add_div, cpow_add _ _ (ofReal_ne_zero.2 (by positivity))]
  rfl

/-- The derivative of `z ↦ ⟨x⟩ ^ z` is `⟨x⟩ ^ z log ⟨x⟩`, with `log ⟨x⟩ = log (1 + ‖x‖ ^ 2) / 2`. -/
theorem hasDerivAt_japaneseBracketCpow (z : ℂ) (x : E) :
    HasDerivAt (fun w ↦ japaneseBracketCpow w x)
      (japaneseBracketCpow z x * (Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ)) z := by
  convert ((hasDerivAt_id z).div_const 2).const_cpow
    (.inl (ofReal_ne_zero.2 (by positivity : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0))) using 1
  · rfl
  · rw [japaneseBracketCpow, id, ← ofReal_log (by positivity)]
    push_cast
    ring

/-- The second-order remainder of `w ↦ ⟨x⟩ ^ w` at `z` is bounded uniformly in `x` by a
bracket power: for `‖h‖ ≤ 1`,
`‖⟨x⟩ ^ (z + h) - ⟨x⟩ ^ z - h ⟨x⟩ ^ z log ⟨x⟩‖ ≤ ‖h‖ ^ 2 (1 + ‖x‖ ^ 2) ^ ((re z + 3) / 2)`. -/
theorem norm_japaneseBracketCpow_add_sub_sub_le (z : ℂ) {h : ℂ} (hh : ‖h‖ ≤ 1) (x : E) :
    ‖japaneseBracketCpow (z + h) x - japaneseBracketCpow z x -
        h * (japaneseBracketCpow z x * (Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ))‖ ≤
      ‖h‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ ((z.re + 3) / 2) := by
  set y := 1 + ‖x‖ ^ 2 with hy_def
  have hy : 1 ≤ y := by simp only [hy_def]; nlinarith [sq_nonneg ‖x‖]
  have hy0 : 0 < y := by linarith
  set L := Real.log y / 2 with hL_def
  have hL0 : 0 ≤ L := by simp only [hL_def]; exact div_nonneg (Real.log_nonneg hy) zero_le_two
  -- `exp L = √y`, and `L ≤ √y` since `log √y ≤ √y - 1`.
  have hexpL : Real.exp L = y ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hy0, hL_def]
    ring_nf
  have hLle : L ≤ y ^ (1 / 2 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 (1 / 2 : ℝ))
    rw [Real.log_rpow hy0, ← hL_def.trans (by ring : Real.log y / 2 = 1 / 2 * Real.log y)] at h1
    linarith
  have hLsq : L ^ 2 ≤ y := by
    calc L ^ 2 ≤ (y ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ hL0 hLle 2
      _ = y := by rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  -- Factor out `⟨x⟩ ^ z` and bound `exp (h L) - 1 - h L` by `‖h L‖ ^ 2 exp ‖h L‖`.
  have hfactor : japaneseBracketCpow (z + h) x - japaneseBracketCpow z x -
      h * (japaneseBracketCpow z x * (L : ℂ)) =
      japaneseBracketCpow z x *
        (exp (h * L) - ∑ m ∈ Finset.range 2, (h * L) ^ m / m.factorial) := by
    simp [japaneseBracketCpow_eq_exp, hy_def, hL_def, Finset.sum_range_succ, add_mul, exp_add]
    ring
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp (h * (L : ℂ)) 2
  have hhL : ‖h * (L : ℂ)‖ = ‖h‖ * L := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL0]
  rw [hhL] at hrem
  have hexp : Real.exp (‖h‖ * L) ≤ y ^ (1 / 2 : ℝ) := by
    rw [← hexpL]
    exact Real.exp_le_exp.2 (mul_le_of_le_one_left hL0 hh)
  rw [hfactor, norm_mul, norm_japaneseBracketCpow]
  calc y ^ (z.re / 2) * ‖exp (h * L) - ∑ m ∈ Finset.range 2, (h * L) ^ m / m.factorial‖
      ≤ y ^ (z.re / 2) * ((‖h‖ * L) ^ 2 * Real.exp (‖h‖ * L)) := by gcongr
    _ ≤ y ^ (z.re / 2) * ((‖h‖ ^ 2 * y) * y ^ (1 / 2 : ℝ)) := by
        rw [mul_pow]
        gcongr
    _ = ‖h‖ ^ 2 * y ^ ((z.re + 3) / 2) := by
        rw [show (z.re + 3) / 2 = z.re / 2 + 1 + 1 / 2 by ring,
          Real.rpow_add hy0, Real.rpow_add hy0, Real.rpow_one]
        ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- On a real inner product space `H`, the complex power `x ↦ ⟨x⟩ ^ z` of the Japanese bracket
has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_japaneseBracketCpow (z : ℂ) :
    (japaneseBracketCpow z : H → ℂ).HasTemperateGrowth := by
  -- Factor `⟨x⟩ ^ z` into the real power `(1 + ‖x‖ ^ 2) ^ (re z / 2)` and the unimodular factor
  -- `exp (i im z log (1 + ‖x‖ ^ 2) / 2)`.
  have h : (japaneseBracketCpow z : H → ℂ) =
      (fun x : H ↦ (((1 + ‖x‖ ^ 2) ^ (z.re / 2) : ℝ) : ℂ)) *
        ((fun t : ℝ ↦ exp (t * I)) ∘ fun x : H ↦ z.im / 2 * Real.log (1 + ‖x‖ ^ 2)) := by
    funext x
    have hre : japaneseBracketCpow (z.re : ℂ) x = (((1 + ‖x‖ ^ 2) ^ (z.re / 2) : ℝ) : ℂ) :=
      japaneseBracketCpow_ofReal z.re x
    rw [Pi.mul_apply, Function.comp_apply, ← hre]
    conv_lhs => rw [← re_add_im z]
    rw [japaneseBracketCpow_add]
    simp only [japaneseBracketCpow_eq_exp]
    push_cast
    ring_nf
  rw [h]
  refine Function.HasTemperateGrowth.mul (by fun_prop) ?_
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- The complex power `x ↦ ⟨x⟩ ^ z` of the Japanese bracket is smooth. -/
@[fun_prop]
theorem contDiff_japaneseBracketCpow (z : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (japaneseBracketCpow z : H → ℂ) := by
  have hbase : ContDiff ℝ n fun x : H ↦ 1 + ‖x‖ ^ 2 := contDiff_const.add (contDiff_norm_sq ℝ)
  have hlog : ContDiff ℝ n fun x : H ↦ Real.log (1 + ‖x‖ ^ 2) / 2 :=
    (hbase.log fun x ↦ by positivity).div_const 2
  rw [funext (japaneseBracketCpow_eq_exp z)]
  exact (contDiff_const.mul (ofRealCLM.contDiff.comp hlog)).cexp

/-- The derivative of `x ↦ ⟨x⟩ ^ z` is `z ⟨x⟩ ^ (z - 2) ⟪x, ·⟫`. -/
theorem hasFDerivAt_japaneseBracketCpow (z : ℂ) (x : H) :
    HasFDerivAt (japaneseBracketCpow z)
      ((z * japaneseBracketCpow (z - 2) x) • (ofRealCLM ∘L innerSL ℝ x)) x := by
  have hbase : HasFDerivAt (fun x : H ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ))
      (ofRealCLM ∘L (2 • innerSL ℝ x)) x :=
    ofRealCLM.hasFDerivAt.comp x ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1)
  have hpow := (Complex.hasStrictDerivAt_cpow_const (c := z / 2)
    (ofReal_mem_slitPlane.2 (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2))).hasDerivAt
  refine (hpow.comp_hasFDerivAt x hbase).congr_fderiv ?_
  ext v
  simp only [japaneseBracketCpow]
  rw [show (z - 2) / 2 = z / 2 - 1 by ring]
  simp only [ofReal_add, ofReal_one, ofReal_pow, ContinuousLinearMap.comp_smul, smul_apply,
    ContinuousLinearMap.comp_apply, coe_innerSL_apply, ofRealCLM_apply, nsmul_eq_mul,
    Nat.cast_ofNat, smul_eq_mul]
  ring

/-- The real-bilinear map `(x, v) ↦ z ⟪x, v⟫`, with complex values. -/
private def innerSLSmul (z : ℂ) : H →L[ℝ] H →L[ℝ] ℂ :=
  ContinuousLinearMap.compL ℝ H ℝ ℂ (z • ofRealCLM) ∘L innerSL ℝ

private theorem innerSLSmul_apply_apply (z : ℂ) (x v : H) :
    innerSLSmul z x v = z * (inner ℝ x v : ℝ) := by
  have h : innerSL ℝ x v = inner ℝ x v := innerSL_apply_apply ℝ x v
  simp [innerSLSmul, h]

private theorem norm_innerSLSmul_le (z : ℂ) : ‖innerSLSmul (H := H) z‖ ≤ 1 + ‖z‖ := by
  refine (ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg z) fun x y ↦ ?_).trans
    (by linarith [norm_nonneg z])
  rw [innerSLSmul_apply_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x y) (norm_nonneg z)

/-- The derivative of `x ↦ ⟨x⟩ ^ z` is `⟨x⟩ ^ (z - 2)` times the linear map `v ↦ z ⟪x, v⟫`. -/
private theorem fderiv_japaneseBracketCpow (z : ℂ) :
    fderiv ℝ (japaneseBracketCpow z : H → ℂ) =
      fun x ↦ japaneseBracketCpow (z - 2) x • innerSLSmul z x := by
  funext x
  rw [(hasFDerivAt_japaneseBracketCpow z x).fderiv]
  ext v
  have h : innerSL ℝ x v = inner ℝ x v := innerSL_apply_apply ℝ x v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, h, ofRealCLM_apply, smul_eq_mul,
    innerSLSmul_apply_apply]
  ring

/-- The orders `z` and `z - 2` have comparable sizes: for `i ≤ k`,
`(1 + ‖z - 2‖) ^ i (1 + ‖z‖) ≤ 3 ^ i (1 + ‖z‖) ^ (k + 1)`. -/
private theorem one_add_norm_sub_two_pow_mul_le (z : ℂ) {i k : ℕ} (hik : i ≤ k) :
    (1 + ‖z - 2‖) ^ i * (1 + ‖z‖) ≤ 3 ^ i * (1 + ‖z‖) ^ (k + 1) := by
  have hz : ‖z - 2‖ ≤ ‖z‖ + 2 := (norm_sub_le _ _).trans (by simp)
  calc (1 + ‖z - 2‖) ^ i * (1 + ‖z‖) ≤ (3 * (1 + ‖z‖)) ^ i * (1 + ‖z‖) := by
        gcongr
        linarith [norm_nonneg z]
    _ = 3 ^ i * ((1 + ‖z‖) ^ i * (1 + ‖z‖) ^ 1) := by rw [mul_pow]; ring
    _ ≤ 3 ^ i * (1 + ‖z‖) ^ (k + 1) := by
        rw [← pow_add]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by omega)) (by positivity)

/-- **Derivative bounds for complex powers of the Japanese bracket.** For every `k` there is a
constant `C` such that, for every complex order `z`,

`‖D^k ⟨x⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ k (1 + ‖x‖ ^ 2) ^ ((re z - k) / 2)`.

So `⟨x⟩ ^ z` is a symbol of order `re z`, and its symbol seminorms grow at most polynomially in
the order `z`. For an imaginary order `z = i τ` these are the bounds that make `⟨ξ⟩ ^ (i τ)` a
Mihlin multiplier with constant `O((1 + |τ|) ^ k)`. -/
theorem exists_norm_iteratedFDeriv_japaneseBracketCpow_le (k : ℕ) :
    ∃ C, ∀ (z : ℂ) (x : H), ‖iteratedFDeriv ℝ k (japaneseBracketCpow z) x‖ ≤
      C * (1 + ‖z‖) ^ k * (1 + ‖x‖ ^ 2) ^ ((z.re - k) / 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · refine ⟨1, fun z x ↦ ?_⟩
    simp
  -- The derivative is `⟨x⟩ ^ (z - 2)` times the linear map `v ↦ z ⟪x, v⟫`; apply the Leibniz rule
  -- to this product and the induction hypothesis to the order `z - 2`.
  choose! C hC using fun i (hi : i ≤ k) ↦ ih i (Nat.lt_succ_of_le hi)
  refine ⟨∑ i ∈ Finset.range (k + 1), k.choose i * max (C i) 0 * 3 ^ i, fun z x ↦ ?_⟩
  have hg (i : ℕ) (hi : i ≤ k) (x : H) :
      ‖iteratedFDeriv ℝ i (japaneseBracketCpow (z - 2)) x‖ ≤
        max (C i) 0 * (1 + ‖z - 2‖) ^ i * (1 + ‖x‖ ^ 2) ^ ((z.re - 2) / 2 - i / 2) := by
    have he : ((z - 2).re - i) / 2 = (z.re - 2) / 2 - i / 2 := by
      simp only [sub_re, re_ofNat]
      ring
    refine (hC i hi (z - 2) x).trans ?_
    rw [he]
    gcongr
    exact le_max_left _ _
  rw [← norm_iteratedFDeriv_fderiv, fderiv_japaneseBracketCpow]
  refine ((innerSLSmul z).norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow
    (contDiff_japaneseBracketCpow (z - 2)) hg x).trans ?_
  have hexp : (z.re - 2) / 2 + 1 / 2 - k / 2 = (z.re - (k + 1 : ℕ)) / 2 := by
    push_cast
    ring
  rw [hexp]
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  -- Each derivative of `⟨x⟩ ^ (z - 2)` costs `1 + ‖z - 2‖`, and the linear map costs `1 + ‖z‖`.
  calc (k.choose i : ℝ) * (max (C i) 0 * (1 + ‖z - 2‖) ^ i) * ‖innerSLSmul z‖ *
        (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2)
      = k.choose i * max (C i) 0 * ((1 + ‖z - 2‖) ^ i * ‖innerSLSmul z‖) *
          (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
        ring
    _ ≤ k.choose i * max (C i) 0 * ((1 + ‖z - 2‖) ^ i * (1 + ‖z‖)) *
          (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
        gcongr
        exact norm_innerSLSmul_le z
    _ ≤ k.choose i * max (C i) 0 * (3 ^ i * (1 + ‖z‖) ^ (k + 1)) *
          (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
        gcongr _ * ?_ * _
        exact one_add_norm_sub_two_pow_mul_le z hik
    _ = _ := by ring

/-- **The complex Bessel weight is a symbol.** The complex-valued bracket power
`(1 + ‖x‖ ^ 2) ^ (s / 2)` satisfies the symbol estimates of order `s`:
`‖D^k (1 + ‖x‖ ^ 2) ^ (s / 2)‖ ≤ C (1 + ‖x‖ ^ 2) ^ ((s - k) / 2)`. It is the symbol of the Bessel
potential of order `s`, the power `⟨x⟩ ^ s` of real order. -/
theorem exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le (s : ℝ) (k : ℕ) :
    ∃ C, ∀ x : H, ‖iteratedFDeriv ℝ k (fun x : H ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) x‖ ≤
      C * (1 + ‖x‖ ^ 2) ^ ((s - k) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_japaneseBracketCpow_le (H := H) k
  refine ⟨C * (1 + |s|) ^ k, fun x ↦ ?_⟩
  have h : (fun x : H ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) = japaneseBracketCpow (s : ℂ) :=
    funext fun x ↦ (japaneseBracketCpow_ofReal s x).symm
  simpa only [h, norm_real, Real.norm_eq_abs, ofReal_re] using hC s x

/-- **Complex powers of nonpositive real part are Mihlin multipliers.** For every `k` there is a
constant `C` such that, for every complex order `z` with `re z ≤ 0` and every `ξ ≠ 0`,
`‖D^k ⟨ξ⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ k / ‖ξ‖ ^ k`. This is Mihlin's condition, with a constant growing
polynomially in `z`. -/
theorem exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow (k : ℕ) :
    ∃ C, ∀ z : ℂ, z.re ≤ 0 → ∀ ξ : H, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ k (japaneseBracketCpow z) ξ‖ ≤ C * (1 + ‖z‖) ^ k / ‖ξ‖ ^ k := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_japaneseBracketCpow_le (H := H) k
  refine ⟨max C 0, fun z hz ξ hξ ↦ (hC z ξ).trans ?_⟩
  have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hexp : (1 + ‖ξ‖ ^ 2) ^ ((z.re - k) / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)
  calc C * (1 + ‖z‖) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((z.re - k) / 2)
      ≤ max C 0 * (1 + ‖z‖) ^ k * (1 / ‖ξ‖ ^ k) := by
        gcongr
        · exact le_max_left _ _
        · exact hexp.trans (Real.one_add_sq_rpow_neg_le hξ' k)
    _ = _ := by ring

end TauCeti
