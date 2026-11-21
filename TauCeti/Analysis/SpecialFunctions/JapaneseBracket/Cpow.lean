/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

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

Each derivative in `x` lowers the order by one, at the price of a factor polynomial in `z`:

`‖D^k ⟨x⟩ ^ z‖ ≤ C_k (1 + ‖z‖) ^ k ⟨x⟩ ^ (re z - k)`,

with `C_k` independent of `z`. The derivative of `⟨x⟩ ^ z` is `z ⟨x⟩ ^ (z - 2) ⟪x, ·⟫`, so the
estimate follows by induction on `k` from the Leibniz rule. For `re z ≤ 0` and `x ≠ 0` the right
side is at most `C_k (1 + ‖z‖) ^ k / ‖x‖ ^ k`: the symbols `⟨x⟩ ^ z` of nonpositive real part,
in particular the imaginary powers, satisfy Mihlin's condition with a constant growing
polynomially in `z`. This is what makes the Bessel potentials of imaginary order bounded on `Lᵖ`
for `1 < p < ∞` with norm polynomial in the order, the estimate behind Stein's interpolation
of the spaces `H^{s,p}`.

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
* `TauCeti.hasFDerivAt_japaneseBracketCpow`: the derivative in `x` is `z ⟨x⟩ ^ (z - 2) ⟪x, ·⟫`.
* `TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le`: the derivative bounds
  `‖D^k ⟨x⟩ ^ z‖ ≤ C_k (1 + ‖z‖) ^ k ⟨x⟩ ^ (re z - k)`, uniformly in `z`.
* `TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow`: Mihlin's condition
  `‖D^k ⟨x⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ N / ‖x‖ ^ k` for `k ≤ N`, uniformly in `z` with `re z ≤ 0`.
-/

public section

noncomputable section

namespace TauCeti

open Complex
open scoped ContDiff NNReal

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

/-- The complex power `x ↦ ⟨x⟩ ^ z` of the Japanese bracket is smooth, indeed analytic: it is
`w ↦ w ^ (z / 2)`, analytic on the slit plane, composed with `x ↦ 1 + ‖x‖ ^ 2`. -/
@[fun_prop]
theorem contDiff_japaneseBracketCpow {n : WithTop ℕ∞} (z : ℂ) :
    ContDiff ℝ n (japaneseBracketCpow z : H → ℂ) := by
  have hg : ContDiffOn ℝ n (fun w : ℂ ↦ w ^ (z / 2)) slitPlane :=
    ((analyticOnNhd_id.cpow analyticOnNhd_const fun _ hw ↦ hw).restrictScalars).contDiffOn
      isOpen_slitPlane.uniqueDiffOn
  exact hg.comp_contDiff (ofRealCLM.contDiff.comp (contDiff_const.add (contDiff_norm_sq ℝ)))
    fun x ↦ ofReal_mem_slitPlane.2 (by positivity)

/-- **The derivative of `⟨x⟩ ^ z` in `x`** is `z ⟨x⟩ ^ (z - 2) ⟪x, ·⟫`: differentiating
`(1 + ‖x‖ ^ 2) ^ (z / 2)` gives `(z / 2) (1 + ‖x‖ ^ 2) ^ (z / 2 - 1) 2 ⟪x, ·⟫`. -/
theorem hasFDerivAt_japaneseBracketCpow (z : ℂ) (x : H) :
    HasFDerivAt (japaneseBracketCpow z)
      (japaneseBracketCpow (z - 2) x • z • ofRealCLM.comp (innerSL ℝ x)) x := by
  have hq : HasFDerivAt (fun y : H ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ))
      (ofRealCLM.comp (2 • innerSL ℝ x)) x :=
    ofRealCLM.hasFDerivAt.comp x ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1)
  have hmem : ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 (by positivity)
  have hg := ((hasStrictDerivAt_cpow_const (c := z / 2) hmem).hasDerivAt.hasFDerivAt.restrictScalars
    ℝ).comp x hq
  rw [funext (japaneseBracketCpow_def z)]
  refine hg.congr_fderiv ?_
  ext v
  simp [japaneseBracketCpow, show (z - 2) / 2 = z / 2 - 1 by ring]
  ring

/-- The derivative of `⟨x⟩ ^ z` in `x`, as a function of `x`. -/
theorem fderiv_japaneseBracketCpow (z : ℂ) :
    fderiv ℝ (japaneseBracketCpow z : H → ℂ) =
      fun x ↦ japaneseBracketCpow (z - 2) x • z • ofRealCLM.comp (innerSL ℝ x) :=
  funext fun x ↦ (hasFDerivAt_japaneseBracketCpow z x).fderiv

/-- One term of the Leibniz expansion of `D^k (⟨x⟩ ^ (z - 2) • L x)`, for a continuous linear map
`L` of norm at most `c ‖z‖`: if `D^i ⟨x⟩ ^ (z - 2)` satisfies the bound of order `i`, the term is
bounded by the bracket power of order `k + 1` times `(1 + ‖z‖) ^ (k + 1)`. -/
private theorem choose_mul_norm_iteratedFDeriv_mul_norm_iteratedFDeriv_le {k i : ℕ} (hik : i ≤ k)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) {z : ℂ} {x : H} {L : H →L[ℝ] H →L[ℝ] ℂ}
    (hL : ‖L‖ ≤ ‖z‖ * c)
    (h₁ : ‖iteratedFDeriv ℝ i (japaneseBracketCpow (z - 2)) x‖ ≤
      C * (1 + ‖z - 2‖) ^ i * (1 + ‖x‖ ^ 2) ^ (((z - 2).re - i) / 2)) :
    (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (japaneseBracketCpow (z - 2)) x‖ *
        ‖iteratedFDeriv ℝ (k - i) L x‖ ≤
      k.choose i * C * 3 ^ i * c * (1 + ‖z‖) ^ (k + 1) *
        (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
  have hw : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have h₂ := L.norm_iteratedFDeriv_le_one_add_norm_sq_rpow (k - i) x
  have hz2 : 1 + ‖z - 2‖ ≤ 3 * (1 + ‖z‖) := by
    have := norm_sub_le z 2
    simp only [Complex.norm_ofNat] at this
    linarith
  have hpow : (1 + ‖z - 2‖) ^ i * ‖z‖ ≤ 3 ^ i * (1 + ‖z‖) ^ (k + 1) := by
    calc (1 + ‖z - 2‖) ^ i * ‖z‖ ≤ (3 * (1 + ‖z‖)) ^ i * (1 + ‖z‖) := by
          gcongr
          linarith
      _ = 3 ^ i * (1 + ‖z‖) ^ (i + 1) := by rw [mul_pow]; ring
      _ ≤ 3 ^ i * (1 + ‖z‖) ^ (k + 1) := by gcongr; linarith
  -- The bracket exponents of the two factors add up to `(re z - (k + 1)) / 2`.
  have hexp : (1 + ‖x‖ ^ 2) ^ (((z - 2).re - i) / 2) *
      (1 + ‖x‖ ^ 2) ^ ((1 - (k - i : ℕ) : ℝ) / 2) =
        (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
    rw [← Real.rpow_add hw, Nat.cast_sub hik, Complex.sub_re]
    congr 1
    push_cast
    norm_num
    ring
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (japaneseBracketCpow (z - 2)) x‖ *
        ‖iteratedFDeriv ℝ (k - i) L x‖
      ≤ k.choose i * (C * (1 + ‖z - 2‖) ^ i * (1 + ‖x‖ ^ 2) ^ (((z - 2).re - i) / 2)) *
          (‖z‖ * c * (1 + ‖x‖ ^ 2) ^ ((1 - (k - i : ℕ) : ℝ) / 2)) := by
        gcongr
        exact h₂.trans (by gcongr)
    _ = k.choose i * C * c * ((1 + ‖z - 2‖) ^ i * ‖z‖) *
          (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
        rw [← hexp]
        ring
    _ ≤ k.choose i * C * c * (3 ^ i * (1 + ‖z‖) ^ (k + 1)) *
          (1 + ‖x‖ ^ 2) ^ ((z.re - (k + 1 : ℕ)) / 2) := by
        gcongr
    _ = _ := by ring

/-- **Derivative bounds for the complex powers of the Japanese bracket, uniform in the order.**
For every `k` there is a constant `C`, independent of `z`, such that
`‖D^k ⟨x⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ k (1 + ‖x‖ ^ 2) ^ ((re z - k) / 2)`. Each derivative in `x` gains
a factor `⟨x⟩⁻¹` and costs at most a factor `1 + ‖z‖`. -/
theorem exists_norm_iteratedFDeriv_japaneseBracketCpow_le (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (z : ℂ) (x : H), ‖iteratedFDeriv ℝ k (japaneseBracketCpow z) x‖ ≤
      C * (1 + ‖z‖) ^ k * (1 + ‖x‖ ^ 2) ^ ((z.re - k) / 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · exact ⟨1, zero_le_one, fun z x ↦ by simp⟩
  · choose! C hC0 hC using fun i (hi : i ≤ k) ↦ ih i (Nat.lt_succ_of_le hi)
    -- The derivative of `⟨x⟩ ^ z` is `⟨x⟩ ^ (z - 2)` times the linear map `x ↦ z ⟪x, ·⟫`.
    set Λ : H →L[ℝ] H →L[ℝ] ℂ := (ContinuousLinearMap.compL ℝ H ℝ ℂ ofRealCLM).comp (innerSL ℝ)
    refine ⟨∑ i ∈ Finset.range (k + 1), k.choose i * C i * 3 ^ i * ‖Λ‖,
      Finset.sum_nonneg fun i hi ↦ by
        have := hC0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        positivity,
      fun z x ↦ ?_⟩
    have hfd : fderiv ℝ (japaneseBracketCpow z : H → ℂ) =
        fun y ↦ japaneseBracketCpow (z - 2) y • (z • Λ) y := by
      rw [fderiv_japaneseBracketCpow]
      funext y
      ext v
      simp [Λ]
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    refine (norm_iteratedFDeriv_smul_le (contDiff_japaneseBracketCpow (n := ∞) (z - 2))
      (z • Λ).contDiff x (mod_cast le_top)).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact choose_mul_norm_iteratedFDeriv_mul_norm_iteratedFDeriv_le hik (hC0 i hik) (norm_nonneg Λ)
      (ContinuousLinearMap.opNorm_smul_le z Λ) (hC i hik (z - 2) x)

/-- **Mihlin's condition for the powers of the Japanese bracket of nonpositive real part.** For
every `N` there is a constant `C` such that for every `z` with `re z ≤ 0`, in particular every
imaginary `z`, the symbol `ξ ↦ ⟨ξ⟩ ^ z` satisfies Mihlin's condition of order `N` with constant
`C (1 + ‖z‖) ^ N`: `‖D^k ⟨ξ⟩ ^ z‖ ≤ C (1 + ‖z‖) ^ N / ‖ξ‖ ^ k` for `k ≤ N` and `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z : ℂ, z.re ≤ 0 → ∀ k ≤ N, ∀ ξ : H, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ k (japaneseBracketCpow z) ξ‖ ≤
        ((C * (1 + ‖z‖₊) ^ N : ℝ≥0) : ℝ) / ‖ξ‖ ^ k := by
  choose C hC0 hC using fun k : ℕ ↦ exists_norm_iteratedFDeriv_japaneseBracketCpow_le (H := H) k
  refine ⟨∑ k ∈ Finset.range (N + 1), (C k).toNNReal, fun z hz k hk ξ hξ ↦ ?_⟩
  have hCk : C k ≤ ∑ k ∈ Finset.range (N + 1), ((C k).toNNReal : ℝ) := by
    rw [← Real.coe_toNNReal _ (hC0 k)]
    exact Finset.single_le_sum (f := fun k ↦ ((C k).toNNReal : ℝ)) (fun _ _ ↦ by positivity)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have hz1 : (1 + ‖z‖) ^ k ≤ (1 + ‖z‖) ^ N := pow_le_pow_right₀ (by simp) hk
  calc ‖iteratedFDeriv ℝ k (japaneseBracketCpow z) ξ‖
      ≤ C k * (1 + ‖z‖) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((z.re - k) / 2) := hC k z ξ
    _ ≤ (∑ k ∈ Finset.range (N + 1), ((C k).toNNReal : ℝ)) * (1 + ‖z‖) ^ N *
          (1 / ‖ξ‖ ^ k) := by
        have := hC0 k
        gcongr
        -- Since `re z ≤ 0`, the bracket power has order at most `-k`.
        calc (1 + ‖ξ‖ ^ 2) ^ ((z.re - k) / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) :=
              Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)
          _ ≤ 1 / ‖ξ‖ ^ k := Real.one_add_sq_rpow_neg_le (norm_pos_iff.2 hξ) k
    _ = _ := by
        push_cast
        ring

end TauCeti
