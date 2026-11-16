/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Distribution.TemperateGrowth

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

end TauCeti
