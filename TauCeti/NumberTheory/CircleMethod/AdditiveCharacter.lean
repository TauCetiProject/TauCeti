/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.Normed.Group.AddCircle.Trigonometric
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The additive character `e(α) = exp(2πiα)` and geometric sums

This file sets up the additive toolkit of the Hardy–Littlewood circle method on `ℝ / ℤ`.

* `TauCeti.expTwoPiI α = e(α) = exp(2πiα)`, the additive character of `ℝ` trivial on `ℤ`. It is
  the coercion of Mathlib's `Real.fourierChar` to `ℂ` (`TauCeti.expTwoPiI_eq_fourierChar`); the
  file records its algebraic API (additivity, inverses, conjugation, powers, periodicity, real and
  imaginary parts, the kernel `ℤ`, and `TauCeti.stdAddChar_intCast_eq_expTwoPiI` linking it to
  `ZMod.stdAddChar`) in the form used by exponential sums.
* `TauCeti.integral_expTwoPiI_intCast`: orthogonality, `∫₀¹ e(mα) dα = 1_{m = 0}` for `m : ℤ`.
  This is what turns a count of solutions of an additive equation into an integral over `[0, 1]`.
* `TauCeti.distInt α = ‖α‖ = |α - round α|`, the distance from `α` to the nearest integer. It is
  the norm of `α` in `UnitAddCircle` (`TauCeti.distInt_eq_norm`), hence `1`-periodic, even and at
  most `1 / 2`, and it controls the sine: `2‖α‖ ≤ |sin (πα)|`
  (`Real.two_mul_norm_unitAddCircle_le_abs_sin`).
* `TauCeti.sum_expTwoPiI_eq`: the geometric sum
  `∑_{n=1}^N e(nβ) = e(β) (e(Nβ) - 1) / (e(β) - 1)` off the integers,
  `TauCeti.norm_sum_Ioc_expTwoPiI_eq` for its exact modulus `|sin (πNβ)| / |sin (πβ)|`, and
  `TauCeti.norm_sum_expTwoPiI_le`, the bound `|∑_{n=1}^N e(nβ)| ≤ min(N, 1 / (2‖β‖))`, with its
  forms `TauCeti.norm_sum_Ioc_expTwoPiI_le` and `TauCeti.norm_sum_Ioc_expTwoPiI_mul_div_le`.

The bound `1 / (2‖β‖)` is stated with the value `N` when `‖β‖ = 0`, by an explicit `if`: with
Lean's convention `1 / 0 = 0` the minimum would be `0` there, while the sum has norm exactly `N`
at the integers (`TauCeti.sum_expTwoPiI_of_distInt_eq_zero`). The capped minimum
`if ‖x‖ = 0 then Y else min(Y, 1 / ‖x‖)` is monotone in the cap `Y`
(`TauCeti.ite_min_inv_distInt_le_of_le`).

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000, Chapter 25.
* R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Cambridge Tracts in Mathematics 125,
  1997, Chapter 2.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-! ### The additive character -/

/-- The additive character `e(α) = exp(2πiα)` of `ℝ`, with kernel `ℤ`. It is the coercion of
`Real.fourierChar` to `ℂ` (`expTwoPiI_eq_fourierChar`). -/
def expTwoPiI (α : ℝ) : ℂ :=
  Complex.exp (2 * π * I * α)

theorem expTwoPiI_def (α : ℝ) : expTwoPiI α = Complex.exp (2 * π * I * α) := (rfl)

/-- `e(α)` is the value of Mathlib's Fourier character `Real.fourierChar` at `α`. -/
theorem expTwoPiI_eq_fourierChar (α : ℝ) : expTwoPiI α = (Real.fourierChar α : ℂ) := by
  rw [expTwoPiI_def, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

@[simp]
theorem expTwoPiI_zero : expTwoPiI 0 = 1 := by
  simp [expTwoPiI_def]

theorem expTwoPiI_add (α β : ℝ) : expTwoPiI (α + β) = expTwoPiI α * expTwoPiI β := by
  rw [expTwoPiI_def, expTwoPiI_def, expTwoPiI_def, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expTwoPiI_neg (α : ℝ) : expTwoPiI (-α) = (expTwoPiI α)⁻¹ := by
  rw [expTwoPiI_def, expTwoPiI_def, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem expTwoPiI_sub (α β : ℝ) : expTwoPiI (α - β) = expTwoPiI α / expTwoPiI β := by
  rw [sub_eq_add_neg, expTwoPiI_add, expTwoPiI_neg, div_eq_mul_inv]

@[simp]
theorem norm_expTwoPiI (α : ℝ) : ‖expTwoPiI α‖ = 1 := by
  rw [expTwoPiI_eq_fourierChar, Circle.norm_coe]

theorem expTwoPiI_ne_zero (α : ℝ) : expTwoPiI α ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem conj_expTwoPiI (α : ℝ) : (starRingEnd ℂ) (expTwoPiI α) = expTwoPiI (-α) := by
  rw [expTwoPiI_def, expTwoPiI_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem expTwoPiI_natCast_mul (n : ℕ) (α : ℝ) : expTwoPiI (n * α) = expTwoPiI α ^ n := by
  rw [expTwoPiI_def, expTwoPiI_def, ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  ring

theorem expTwoPiI_intCast_mul (m : ℤ) (α : ℝ) : expTwoPiI (m * α) = expTwoPiI α ^ m := by
  rw [expTwoPiI_def, expTwoPiI_def, ← Complex.exp_intCast_mul]
  congr 1
  push_cast
  ring

/-- `e(α) = 1` exactly when `α` is an integer. -/
theorem expTwoPiI_eq_one_iff {α : ℝ} : expTwoPiI α = 1 ↔ ∃ m : ℤ, α = m := by
  rw [expTwoPiI_def, Complex.exp_eq_one_iff]
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m, ?_⟩, fun ⟨m, hm⟩ ↦ ⟨m, by rw [hm]; push_cast; ring⟩⟩
  exact_mod_cast mul_left_cancel₀ h2πI (hm.trans (mul_comm _ _))

@[simp]
theorem expTwoPiI_intCast (m : ℤ) : expTwoPiI m = 1 :=
  expTwoPiI_eq_one_iff.2 ⟨m, rfl⟩

@[simp]
theorem expTwoPiI_natCast (n : ℕ) : expTwoPiI n = 1 := by
  exact_mod_cast expTwoPiI_intCast n

@[simp]
theorem expTwoPiI_one : expTwoPiI 1 = 1 := by
  exact_mod_cast expTwoPiI_natCast 1

@[simp]
theorem expTwoPiI_ofNat (n : ℕ) [n.AtLeastTwo] : expTwoPiI (ofNat(n) : ℝ) = 1 :=
  expTwoPiI_natCast n

@[simp]
theorem expTwoPiI_add_intCast (α : ℝ) (m : ℤ) : expTwoPiI (α + m) = expTwoPiI α := by
  rw [expTwoPiI_add, expTwoPiI_intCast, mul_one]

/-- `e` is `1`-periodic. -/
theorem expTwoPiI_periodic : Function.Periodic expTwoPiI 1 := fun α ↦ by
  rw [expTwoPiI_add, expTwoPiI_one, mul_one]

/-- `‖e(α) - 1‖ = 2 |sin (πα)|`. -/
theorem norm_expTwoPiI_sub_one (α : ℝ) : ‖expTwoPiI α - 1‖ = 2 * |Real.sin (π * α)| := by
  rw [norm_sub_rev, expTwoPiI_def, UpperHalfPlane.norm_one_sub_exp_two_pi_I_mul, abs_mul,
    abs_two]

/-- Euler's formula for `e(α)`: `e(α) = cos (2πα) + sin (2πα) * I`. -/
theorem expTwoPiI_eq_cos_add_sin_mul_I (α : ℝ) :
    expTwoPiI α = (Real.cos (2 * π * α) : ℂ) + (Real.sin (2 * π * α) : ℂ) * I := by
  have harg : (2 * (π : ℂ) * I * α : ℂ) = ((2 * π * α : ℝ) : ℂ) * I := by push_cast; ring
  rw [expTwoPiI_def, harg, Complex.exp_mul_I]
  norm_cast

@[simp]
theorem re_expTwoPiI (α : ℝ) : (expTwoPiI α).re = Real.cos (2 * π * α) := by
  simp only [expTwoPiI_eq_cos_add_sin_mul_I, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp]
theorem im_expTwoPiI (α : ℝ) : (expTwoPiI α).im = Real.sin (2 * π * α) := by
  simp only [expTwoPiI_eq_cos_add_sin_mul_I, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one, mul_zero, add_zero]

/-- `e(α) + e(-α) = 2 cos (2πα)`. -/
theorem expTwoPiI_add_neg_eq_cos (α : ℝ) :
    expTwoPiI α + expTwoPiI (-α) = 2 * (Real.cos (2 * π * α) : ℂ) := by
  simp only [expTwoPiI_eq_cos_add_sin_mul_I, mul_neg, Real.cos_neg, Real.sin_neg, ofReal_neg]
  ring

/-- `e(α) - e(-α) = 2 i sin (2πα)`. -/
theorem expTwoPiI_sub_neg_eq_sin (α : ℝ) :
    expTwoPiI α - expTwoPiI (-α) = 2 * I * (Real.sin (2 * π * α) : ℂ) := by
  simp only [expTwoPiI_eq_cos_add_sin_mul_I, mul_neg, Real.cos_neg, Real.sin_neg, ofReal_neg]
  ring

/-- Mathlib's `ZMod.stdAddChar` evaluated at an integer `k` is `e(k / q)`. -/
theorem stdAddChar_intCast_eq_expTwoPiI {q : ℕ} [NeZero q] (k : ℤ) :
    ZMod.stdAddChar (k : ZMod q) = expTwoPiI ((k : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, expTwoPiI_def]
  congr 1
  push_cast
  ring

/-- Mathlib's `ZMod.stdAddChar` evaluated at `(n : ZMod q) * (b : ZMod q)` is `e(b * n / q)`. -/
theorem stdAddChar_intCast_mul_natCast {q : ℕ} [NeZero q] (n : ℤ) (b : ℕ) :
    ZMod.stdAddChar ((n : ZMod q) * (b : ZMod q)) = expTwoPiI ((b : ℝ) * n / q) := by
  rw [← Int.cast_natCast b, ← Int.cast_mul, stdAddChar_intCast_eq_expTwoPiI]
  congr 1
  push_cast
  ring

/-- **Orthogonality** on `ℝ / ℤ`: `∫₀¹ e(mα) dα = 1` if `m = 0` and `0` otherwise. -/
theorem integral_expTwoPiI_intCast (m : ℤ) :
    ∫ α in (0 : ℝ)..1, expTwoPiI (m * α) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · simp [hm]
  have hc : (2 * π * I * m : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero, hm]
  have hexp : ∀ α : ℝ, expTwoPiI (m * α) = Complex.exp (2 * π * I * m * α) := fun α ↦ by
    rw [expTwoPiI_def]
    congr 1
    push_cast
    ring
  simp_rw [hexp, integral_exp_mul_complex hc]
  have h1 : Complex.exp (2 * π * I * m) = 1 := Complex.exp_eq_one_iff.2 ⟨m, by ring⟩
  simp [h1]

/-! ### The distance to the nearest integer -/

/-- The distance `‖α‖ = |α - round α|` from `α` to the nearest integer. It is the norm of `α` in
`UnitAddCircle` (`distInt_eq_norm`). -/
def distInt (α : ℝ) : ℝ :=
  |α - round α|

theorem distInt_def (α : ℝ) : distInt α = |α - round α| := (rfl)

/-- `‖α‖` is the norm of the image of `α` in `ℝ / ℤ`. -/
theorem distInt_eq_norm (α : ℝ) : distInt α = ‖(α : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm

theorem distInt_nonneg (α : ℝ) : 0 ≤ distInt α :=
  abs_nonneg _

theorem distInt_le_half (α : ℝ) : distInt α ≤ 1 / 2 :=
  abs_sub_round α

/-- `‖α‖` is at most the distance from `α` to any integer. -/
theorem distInt_le_abs_sub_intCast (α : ℝ) (m : ℤ) : distInt α ≤ |α - m| :=
  round_le α m

/-- `‖α‖ = 0` exactly when `α` is an integer. -/
theorem distInt_eq_zero_iff {α : ℝ} : distInt α = 0 ↔ ∃ m : ℤ, α = m := by
  rw [distInt_def, abs_eq_zero, sub_eq_zero]
  refine ⟨fun h ↦ ⟨_, h⟩, ?_⟩
  rintro ⟨m, rfl⟩
  rw [round_intCast]

@[simp]
theorem distInt_intCast (m : ℤ) : distInt m = 0 :=
  distInt_eq_zero_iff.2 ⟨m, rfl⟩

@[simp]
theorem distInt_natCast (n : ℕ) : distInt n = 0 := by
  exact_mod_cast distInt_intCast n

@[simp]
theorem distInt_zero : distInt 0 = 0 := by
  exact_mod_cast distInt_natCast 0

@[simp]
theorem distInt_one : distInt 1 = 0 := by
  exact_mod_cast distInt_natCast 1

@[simp]
theorem distInt_ofNat (n : ℕ) [n.AtLeastTwo] : distInt (ofNat(n) : ℝ) = 0 :=
  distInt_natCast n

/-- `e(α) = 1` exactly when `‖α‖ = 0`. -/
theorem expTwoPiI_eq_one_iff_distInt_eq_zero {α : ℝ} : expTwoPiI α = 1 ↔ distInt α = 0 := by
  rw [expTwoPiI_eq_one_iff, distInt_eq_zero_iff]

@[simp]
theorem distInt_add_intCast (α : ℝ) (m : ℤ) : distInt (α + m) = distInt α := by
  rw [distInt_def, distInt_def, round_add_intCast, Int.cast_add, add_sub_add_right_eq_sub]

/-- `‖·‖` is `1`-periodic. -/
theorem distInt_periodic : Function.Periodic distInt 1 := fun α ↦ by
  simpa using distInt_add_intCast α 1

@[simp]
theorem distInt_neg (α : ℝ) : distInt (-α) = distInt α := by
  rw [distInt_eq_norm, distInt_eq_norm, AddCircle.coe_neg, norm_neg]

theorem distInt_le_abs (α : ℝ) : distInt α ≤ |α| := by
  simpa using distInt_le_abs_sub_intCast α 0

/-- `‖·‖` is subadditive: `‖α + β‖ ≤ ‖α‖ + ‖β‖`. -/
theorem distInt_add_le (α β : ℝ) : distInt (α + β) ≤ distInt α + distInt β := by
  simp only [distInt_eq_norm, AddCircle.coe_add]
  exact norm_add_le _ _

/-- A fraction `k / q` with `q ∤ k` is at distance at least `1 / q` from the integers. -/
theorem one_div_le_distInt_intCast_div {q : ℕ} {k : ℤ} (hk : ¬(q : ℤ) ∣ k) :
    1 / (q : ℝ) ≤ distInt (k / q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set r := round ((k : ℝ) / q)
  have hne : k - q * r ≠ 0 := fun h ↦ hk ⟨r, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((k - q * r : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hne
  rw [distInt_def, show (k : ℝ) / q - r = ((k - q * r : ℤ) : ℝ) / q by
    push_cast; field_simp, abs_div, abs_of_pos hq']
  exact div_le_div_of_nonneg_right h1 hq'.le

/-! ### Geometric sums -/

/-- At an integer `β`, `∑_{n=1}^N e(nβ) = N`. -/
theorem sum_expTwoPiI_of_distInt_eq_zero (N : ℕ) {β : ℝ} (hβ : distInt β = 0) :
    ∑ n ∈ Finset.Icc 1 N, expTwoPiI (n * β) = N := by
  obtain ⟨m, rfl⟩ := distInt_eq_zero_iff.1 hβ
  simp [expTwoPiI_natCast_mul]

/-- The geometric sum `∑_{n=1}^N e(nβ) = e(β) (e(Nβ) - 1) / (e(β) - 1)` off the integers. -/
theorem sum_expTwoPiI_eq (N : ℕ) {β : ℝ} (hβ : distInt β ≠ 0) :
    ∑ n ∈ Finset.Icc 1 N, expTwoPiI (n * β) =
      expTwoPiI β * (expTwoPiI (N * β) - 1) / (expTwoPiI β - 1) := by
  have h1 : expTwoPiI β ≠ 1 := mt expTwoPiI_eq_one_iff_distInt_eq_zero.1 hβ
  simp_rw [expTwoPiI_natCast_mul]
  rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico h1 (by omega)]
  ring

/-- The trivial bound `|∑_{n=1}^N e(nβ)| ≤ N`. -/
theorem norm_sum_expTwoPiI_le_natCast (N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, expTwoPiI (n * β)‖ ≤ N :=
  (norm_sum_le _ _).trans (by simp)

/-- Off the integers, `|∑_{n=1}^N e(nβ)| ≤ 1 / (2‖β‖)`. -/
theorem norm_sum_expTwoPiI_le_one_div (N : ℕ) {β : ℝ} (hβ : distInt β ≠ 0) :
    ‖∑ n ∈ Finset.Icc 1 N, expTwoPiI (n * β)‖ ≤ 1 / (2 * distInt β) := by
  have hpos : 0 < 2 * distInt β := by
    have := distInt_nonneg β
    positivity
  have hsin : 2 * distInt β ≤ |Real.sin (π * β)| :=
    distInt_eq_norm β ▸ Real.two_mul_norm_unitAddCircle_le_abs_sin β
  have hden : 0 < ‖expTwoPiI β - 1‖ := by
    rw [norm_expTwoPiI_sub_one]
    linarith
  have hnum : ‖expTwoPiI (N * β) - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_expTwoPiI, norm_one]; norm_num)
  rw [sum_expTwoPiI_eq N hβ]
  simp only [norm_div, norm_mul, norm_expTwoPiI, one_mul]
  rw [div_le_div_iff₀ hden hpos, one_mul, norm_expTwoPiI_sub_one β]
  calc ‖expTwoPiI (N * β) - 1‖ * (2 * distInt β) ≤ 2 * (2 * distInt β) := by gcongr
    _ ≤ 2 * |Real.sin (π * β)| := by gcongr

/-- **The geometric-sum bound** `|∑_{n=1}^N e(nβ)| ≤ min(N, 1 / (2‖β‖))`, with the value `N`
when `‖β‖ = 0`. -/
theorem norm_sum_expTwoPiI_le (N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, expTwoPiI (n * β)‖ ≤
      if distInt β = 0 then (N : ℝ) else min (N : ℝ) (1 / (2 * distInt β)) := by
  split_ifs with hβ
  · exact norm_sum_expTwoPiI_le_natCast N β
  · exact le_min (norm_sum_expTwoPiI_le_natCast N β)
      (norm_sum_expTwoPiI_le_one_div N hβ)

/-- Raising the cap `Y` raises the capped minimum `min(Y, 1 / ‖x‖)`, taken to be `Y` when
`‖x‖ = 0`. -/
theorem ite_min_inv_distInt_le_of_le {x Y Y' : ℝ} (h : Y ≤ Y') :
    (if distInt x = 0 then Y else min Y (distInt x)⁻¹) ≤
      if distInt x = 0 then Y' else min Y' (distInt x)⁻¹ := by
  split_ifs
  exacts [h, min_le_min_right _ h]

/-- The geometric-sum bound over an interval of naturals:
`|∑_{A < m ≤ B} e(mβ)| ≤ min(B - A, 1 / (2‖β‖))`, with the value `B - A` when `‖β‖ = 0`. -/
theorem norm_sum_Ioc_expTwoPiI_le (A B : ℕ) (β : ℝ) :
    ‖∑ m ∈ Finset.Ioc A B, expTwoPiI (m * β)‖ ≤
      if distInt β = 0 then ((B - A : ℕ) : ℝ)
      else min ((B - A : ℕ) : ℝ) (1 / (2 * distInt β)) := by
  have hI : Finset.Ioc A B = (Finset.Icc 1 (B - A)).map (addRightEmbedding A) := by
    rw [Finset.map_add_right_Icc]
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have h : ∑ m ∈ Finset.Ioc A B, expTwoPiI (m * β) =
      expTwoPiI (A * β) * ∑ k ∈ Finset.Icc 1 (B - A), expTwoPiI (k * β) := by
    rw [hI, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← expTwoPiI_add, addRightEmbedding_apply, Nat.cast_add, add_mul, add_comm]
  rw [h, norm_mul, norm_expTwoPiI, one_mul]
  exact norm_sum_expTwoPiI_le _ β

/-- Exact modulus of a shifted geometric sum off the integers: for `M : ℤ`, `N : ℕ`, and `β : ℝ`
with `distInt β ≠ 0`, `‖∑ n ∈ Ioc M (M + N), e(nβ)‖ = |sin (π N β)| / |sin (π β)|`. -/
theorem norm_sum_Ioc_expTwoPiI_eq (M : ℤ) (N : ℕ) {β : ℝ} (hβ : distInt β ≠ 0) :
    ‖∑ n ∈ Finset.Ioc M (M + N), expTwoPiI (n * β)‖ =
      |Real.sin (π * N * β)| / |Real.sin (π * β)| := by
  have hshift : ∑ n ∈ Finset.Ioc M (M + N), expTwoPiI (n * β) =
      expTwoPiI (M * β) * ∑ k ∈ Finset.Icc 1 N, expTwoPiI (k * β) := by
    rw [Int.Ioc_eq_finset_map, add_sub_cancel_left, Int.toNat_natCast, Finset.sum_map,
      Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
      Int.cast_add, Int.cast_natCast]
    rw [← expTwoPiI_add]
    congr 1
    push_cast
    ring
  rw [hshift, norm_mul, sum_expTwoPiI_eq N hβ]
  simp only [norm_expTwoPiI, Complex.norm_div, Complex.norm_mul, one_mul, norm_expTwoPiI_sub_one]
  rw [mul_div_mul_left _ _ two_ne_zero, mul_assoc]

/-- Exact modulus of a character-expansion geometric sum: for `1 ≤ b < q`, `M : ℤ`, and `N : ℕ`,
`‖∑ n ∈ Ioc M (M + N), e(b * n / q)‖ = |sin (π * b * N / q)| / sin (π * b / q)`. -/
theorem norm_sum_Ioc_expTwoPiI_mul_div_eq {b q : ℕ} (hb₀ : 1 ≤ b) (hbq : b < q)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q)‖ =
      |Real.sin (π * b * N / q)| / Real.sin (π * b / q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hdist : distInt ((b : ℝ) / q) ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := distInt_eq_zero_iff.mp h
    have hm₀ : (0 : ℝ) < m := hm ▸ div_pos hbpos hqpos
    have hm₁ : (m : ℝ) < 1 := hm ▸ (div_lt_one hqpos).mpr (by exact_mod_cast hbq)
    have : (0 : ℤ) < m := Int.cast_pos.mp hm₀
    have : m < 1 := Int.cast_lt.mp (by exact_mod_cast hm₁)
    omega
  have heq : ∑ n ∈ Finset.Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q) =
      ∑ n ∈ Finset.Ioc M (M + N), expTwoPiI (n * ((b : ℝ) / q)) := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    congr 2
    ring
  have hargN : π * (N : ℝ) * ((b : ℝ) / q) = π * b * N / q := by ring
  have harg1 : π * ((b : ℝ) / q) = π * b / q := by ring
  have hsin_pos : 0 < Real.sin (π * b / q) := by
    simpa only [mul_comm π] using sin_mul_pi_div_pos hbpos (by exact_mod_cast hbq)
  rw [heq, norm_sum_Ioc_expTwoPiI_eq M N hdist, hargN, harg1, abs_of_pos hsin_pos]

/-- Upper bound for a character-expansion geometric sum: for `1 ≤ b < q`, `M : ℤ`, and `N : ℕ`,
`‖∑ n ∈ Ioc M (M + N), e(b * n / q)‖ ≤ min N (sin (π * b / q))⁻¹`. -/
theorem norm_sum_Ioc_expTwoPiI_mul_div_le {b q : ℕ} (hb₀ : 1 ≤ b) (hbq : b < q)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q)‖ ≤
      min (N : ℝ) (Real.sin (π * b / q))⁻¹ := by
  have hsin_pos : 0 < Real.sin (π * b / q) := by
    simpa only [mul_comm π] using
      sin_mul_pi_div_pos (by exact_mod_cast (by omega : 0 < b)) (by exact_mod_cast hbq)
  refine le_min ?_ ?_
  · calc
      ‖∑ n ∈ Finset.Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q)‖
        ≤ ∑ _n ∈ Finset.Ioc M (M + N), ‖expTwoPiI ((b : ℝ) * _n / q)‖ := norm_sum_le _ _
      _ = N := by simp [norm_expTwoPiI, Int.card_Ioc]
  · rw [norm_sum_Ioc_expTwoPiI_mul_div_eq hb₀ hbq, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hsin_pos.le

/-! ### Checks -/

example : expTwoPiI (1 / 2) = -1 := by
  rw [expTwoPiI_def, ← Complex.exp_pi_mul_I]
  congr 1
  push_cast
  ring

example : expTwoPiI (1 / 4) = I := by
  rw [expTwoPiI_def, show 2 * π * I * ((1 / 4 : ℝ) : ℂ) = (π / 2 : ℝ) * I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  simp

/-- Mathlib's `round` rounds half up, and `‖1 / 2‖ = 1 / 2`. -/
example : distInt (1 / 2) = 1 / 2 := by
  norm_num [distInt_def, round_eq]

example : distInt (-0.3) = 0.3 := by
  rw [distInt_neg]
  norm_num [distInt_def, round_eq]

example : distInt 7 = 0 := by
  simp

/-- The `if` in `norm_sum_expTwoPiI_le` is needed: at `β = 0` the sum has norm `N`. -/
example (N : ℕ) : ‖∑ n ∈ Finset.Icc 1 N, expTwoPiI (n * 0)‖ = N := by
  simp

end TauCeti
