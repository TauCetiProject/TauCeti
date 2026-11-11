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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Complex powers of the Japanese bracket

On a real normed space `E`, write `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)` for the Japanese bracket. For a
complex number `z` its complex power is

`⟨x⟩ ^ z = exp (z log ⟨x⟩) = exp (z log (1 + ‖x‖ ^ 2) / 2)`
(`TauCeti.japaneseBracketCpow z x`).

For real `z = s` this is the real power `(1 + ‖x‖ ^ 2) ^ (s / 2)`, the symbol of the Bessel
potential of order `s`. In general its modulus is the real power of order `re z`, so an
imaginary power `⟨x⟩ ^ (i y)` has modulus one. The powers are multiplicative in the exponent, and
`z ↦ ⟨x⟩ ^ z` is entire with derivative `⟨x⟩ ^ z log ⟨x⟩`. For each `z` the function
`x ↦ ⟨x⟩ ^ z` has temperate growth, so it is a Fourier multiplier on Schwartz functions: these are
the Bessel potentials of complex order, which depend holomorphically on the order and are used to
interpolate operators between Bessel-potential spaces.

## Main declarations

* `TauCeti.japaneseBracketCpow z x`: the complex power `⟨x⟩ ^ z`.
* `TauCeti.japaneseBracketCpow_ofReal`: for real `s` it is `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TauCeti.norm_japaneseBracketCpow`: `‖⟨x⟩ ^ z‖ = (1 + ‖x‖ ^ 2) ^ (re z / 2)`.
* `TauCeti.japaneseBracketCpow_add`: `⟨x⟩ ^ (z + w) = ⟨x⟩ ^ z ⟨x⟩ ^ w`.
* `TauCeti.hasDerivAt_japaneseBracketCpow`: the derivative in the exponent, and the uniform
  second-order remainder bound `TauCeti.norm_japaneseBracketCpow_add_sub_sub_le`.
* `TauCeti.hasTemperateGrowth_log_one_add_norm_sq`: `x ↦ log (1 + ‖x‖ ^ 2)` has temperate growth.
* `TauCeti.hasTemperateGrowth_japaneseBracketCpow`: `x ↦ ⟨x⟩ ^ z` has temperate growth.
-/

public section

noncomputable section

namespace TauCeti

open Complex

variable {E : Type*} [NormedAddCommGroup E]

/-- The complex power `⟨x⟩ ^ z = exp (z log (1 + ‖x‖ ^ 2) / 2)` of the Japanese bracket
`⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`. -/
def japaneseBracketCpow (z : ℂ) (x : E) : ℂ :=
  exp (z * (Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ))

theorem japaneseBracketCpow_def (z : ℂ) (x : E) :
    japaneseBracketCpow z x = exp (z * (Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ)) := (rfl)

/-- For a real exponent `s`, the complex power is the real power `(1 + ‖x‖ ^ 2) ^ (s / 2)`. -/
theorem japaneseBracketCpow_ofReal (s : ℝ) (x : E) :
    japaneseBracketCpow (s : ℂ) x = (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := by
  rw [japaneseBracketCpow, Real.rpow_def_of_pos (by positivity), ← ofReal_mul, ← ofReal_exp]
  ring_nf

@[simp]
theorem japaneseBracketCpow_zero (x : E) : japaneseBracketCpow 0 x = 1 := by
  simp [japaneseBracketCpow]

/-- The modulus of `⟨x⟩ ^ z` is the real power of order `re z`. -/
theorem norm_japaneseBracketCpow (z : ℂ) (x : E) :
    ‖japaneseBracketCpow z x‖ = (1 + ‖x‖ ^ 2) ^ (z.re / 2) := by
  rw [japaneseBracketCpow, norm_exp, re_mul_ofReal, Real.rpow_def_of_pos (by positivity)]
  ring_nf

/-- The complex powers are multiplicative in the exponent. -/
theorem japaneseBracketCpow_add (z w : ℂ) (x : E) :
    japaneseBracketCpow (z + w) x = japaneseBracketCpow z x * japaneseBracketCpow w x := by
  simp only [japaneseBracketCpow, add_mul, exp_add]

/-- The derivative of `z ↦ ⟨x⟩ ^ z` is `⟨x⟩ ^ z log ⟨x⟩`, with `log ⟨x⟩ = log (1 + ‖x‖ ^ 2) / 2`. -/
theorem hasDerivAt_japaneseBracketCpow (z : ℂ) (x : E) :
    HasDerivAt (fun w ↦ japaneseBracketCpow w x)
      (japaneseBracketCpow z x * (Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ)) z := by
  simpa [japaneseBracketCpow] using ((hasDerivAt_id z).mul_const
    ((Real.log (1 + ‖x‖ ^ 2) / 2 : ℝ) : ℂ)).cexp

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
    simp [japaneseBracketCpow, hy_def, hL_def, Finset.sum_range_succ, add_mul, exp_add]
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

/-- The logarithm `x ↦ log (1 + ‖x‖ ^ 2)` of the squared Japanese bracket has temperate growth:
it grows like `‖x‖ ^ 2`, and its derivative `(1 + ‖x‖ ^ 2)⁻¹ D‖x‖ ^ 2` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_log_one_add_norm_sq :
    (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2)).HasTemperateGrowth := by
  have hderiv (x : H) : HasFDerivAt (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2))
      ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ) • fderiv ℝ (fun x : H ↦ ‖x‖ ^ 2) x) x := by
    have h := (((contDiff_norm_sq ℝ (E := H) (n := 1)).differentiable one_ne_zero).differentiableAt
      (x := x)).hasFDerivAt.const_add 1
    rw [Real.rpow_neg_one]
    exact h.log (ne_of_gt (by positivity))
  have hfd : fderiv ℝ (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2)) =
      (fun x : H ↦ (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) • fderiv ℝ (fun x : H ↦ ‖x‖ ^ 2) :=
    funext fun x ↦ (hderiv x).fderiv
  refine Function.HasTemperateGrowth.of_fderiv (k := 2) (C := 1) ?_
    (fun x ↦ (hderiv x).differentiableAt) fun x ↦ ?_
  · rw [hfd]
    exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow H (-1)).smul
      (Function.hasTemperateGrowth_norm_sq H).fderiv
  · have hle : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    rw [Real.norm_of_nonneg (Real.log_nonneg hle), one_mul]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ‖x‖ ^ 2)
    nlinarith [norm_nonneg x]

/-- The complex power `x ↦ ⟨x⟩ ^ z` of the Japanese bracket has temperate growth. It is the
product of the real power `(1 + ‖x‖ ^ 2) ^ (re z / 2)` and the unimodular factor
`exp (i im z log (1 + ‖x‖ ^ 2) / 2)`. -/
@[fun_prop]
theorem hasTemperateGrowth_japaneseBracketCpow (z : ℂ) :
    (japaneseBracketCpow z : H → ℂ).HasTemperateGrowth := by
  have h : (japaneseBracketCpow z : H → ℂ) =
      (fun x : H ↦ (((1 + ‖x‖ ^ 2) ^ (z.re / 2) : ℝ) : ℂ)) *
        ((fun t : ℝ ↦ exp (t * I)) ∘ fun x : H ↦ z.im / 2 * Real.log (1 + ‖x‖ ^ 2)) := by
    funext x
    have hre : japaneseBracketCpow (z.re : ℂ) x = (((1 + ‖x‖ ^ 2) ^ (z.re / 2) : ℝ) : ℂ) :=
      japaneseBracketCpow_ofReal z.re x
    rw [Pi.mul_apply, Function.comp_apply, ← hre]
    conv_lhs => rw [← re_add_im z]
    rw [japaneseBracketCpow_add]
    simp only [japaneseBracketCpow]
    push_cast
    ring_nf
  rw [h]
  refine Function.HasTemperateGrowth.mul (by fun_prop) ?_
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

end TauCeti
