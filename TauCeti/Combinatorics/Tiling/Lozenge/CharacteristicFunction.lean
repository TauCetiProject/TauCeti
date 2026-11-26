/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import TauCeti.Analysis.SpecialFunctions.Complex.Exp.NegOfRealMulI
import TauCeti.Analysis.SpecialFunctions.Trigonometric.TwoMulIntMulPi

/-!
# The characteristic function of lozenge type weights and its zeros

For type weights `w = (w₁, w₂, w₃)` of the lozenge dimer model, the characteristic function is
`P_w(θ, φ) = w₃ + w₂ e^{iθ} + w₁ e^{−iφ}` (`TauCeti.lozengeCharFun`), and `w` is liquid when the
strict triangle inequalities hold (`TauCeti.IsLiquidWeights`); liquid weights are positive. For
`d ∈ ℤ²` the normalized Fourier integral of `1 / P_w` is
`G_w(d) = (4π²)⁻¹ ∫∫_{[0,2π]²} e^{i(d₁θ + d₂φ)} / P_w(θ, φ) dθ dφ` (`TauCeti.lozengeKernel`),
the formula by which the references define the infinite inverse Kasteleyn kernel. It is a Bochner
integral, so it is defined for all `w` and equals `0` when `1 / P_w` is not integrable on the
torus. This file does not prove the identities making `G_w` an inverse of the Kasteleyn matrix,
nor the integrability of `1 / P_w` for liquid weights, where `P_w` has zeros.

The main result locates the zeros of `P_w` for liquid `w`
(`TauCeti.lozengeCharFun_eq_zero_iff`): modulo `2π` in each variable they are exactly
`(θ₀, φ₀)` and `(−θ₀, −φ₀)`, where
`θ₀ = arccos ((w₁² − w₂² − w₃²) / (2 w₂ w₃))` and `φ₀ = arccos ((w₂² − w₁² − w₃²) / (2 w₁ w₃))`
(`TauCeti.lozengeZeroAngleFst`, `TauCeti.lozengeZeroAngleSnd`) both lie in `(0, π)`, so
`θ₀, φ₀ ∉ πℤ`. These are the exterior angles `π − θ₁` and `π − θ₂` of the triangle with sides
`w₁, w₂, w₃`, `θ_k` being the angle opposite `w_k`: `P_w(θ, φ) = 0` says that the three vectors
`w₃`, `w₂ e^{iθ}` and `w₁ e^{−iφ}` close up into this triangle. At every zero the partial
derivatives `i w₂ e^{iθ}` and `−i w₁ e^{−iφ}` are linearly independent over `ℝ`
(`TauCeti.linearIndependent_deriv_lozengeCharFun`), that is, the real Jacobian of `P_w` is
invertible there: its determinant is `w₁ w₂ sin(θ + φ)`, and at a zero
`w₁ sin(θ + φ) = −w₃ sin θ ≠ 0` (`TauCeti.mul_sin_add_eq_of_lozengeCharFun_eq_zero`).
Equivalently, the real derivative of `(θ, φ) ↦ P_w(θ, φ)` (`TauCeti.hasFDerivAt_lozengeCharFun`),
which sends `(a, b)` to `a (i w₂ e^{iθ}) + b (−i w₁ e^{−iφ})`, is injective at every zero
(`TauCeti.IsLiquidWeights.exists_hasFDerivAt_injective`).

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Theorem 4.11.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009),
  Section 6.1.
* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  Theorem 4.3.
-/

public section

noncomputable section

open Complex Set MeasureTheory

namespace TauCeti

/-- The characteristic function `P_w(θ, φ) = w₃ + w₂ e^{iθ} + w₁ e^{−iφ}` of the type weights
`w = (w₁, w₂, w₃)`. -/
def lozengeCharFun (w₁ w₂ w₃ θ φ : ℝ) : ℂ :=
  w₃ + w₂ * exp (θ * I) + w₁ * exp (-(φ * I))

/-- The value of the characteristic function. -/
theorem lozengeCharFun_def (w₁ w₂ w₃ θ φ : ℝ) :
    lozengeCharFun w₁ w₂ w₃ θ φ = w₃ + w₂ * exp (θ * I) + w₁ * exp (-(φ * I)) :=
  (rfl)

/-- The characteristic function `P_w` is continuous on `ℝ²`. -/
theorem continuous_lozengeCharFun (w₁ w₂ w₃ : ℝ) :
    Continuous fun p : ℝ × ℝ => lozengeCharFun w₁ w₂ w₃ p.1 p.2 := by
  simp only [lozengeCharFun_def]
  fun_prop

/-- Type weights are liquid when they satisfy the strict triangle inequalities. -/
def IsLiquidWeights (w₁ w₂ w₃ : ℝ) : Prop :=
  w₁ < w₂ + w₃ ∧ w₂ < w₁ + w₃ ∧ w₃ < w₁ + w₂

/-- Liquidity unfolded. -/
theorem isLiquidWeights_iff {w₁ w₂ w₃ : ℝ} :
    IsLiquidWeights w₁ w₂ w₃ ↔ w₁ < w₂ + w₃ ∧ w₂ < w₁ + w₃ ∧ w₃ < w₁ + w₂ :=
  Iff.rfl

/-- The normalized Fourier integral of `1 / P_w`,
`G_w(d) = (4π²)⁻¹ ∫∫_{[0,2π]²} e^{i(d₁θ + d₂φ)} / P_w(θ, φ) dθ dφ`, the formula by which the
references define the infinite inverse Kasteleyn kernel. As a Bochner integral it is total: it
equals `0` when `1 / P_w` is not integrable on the torus, and it is a genuine integral when
`1 / P_w` is integrable, for instance when `P_w` is bounded away from `0`, as for
`w = (1, 1, 3)`. The identities making `G_w` an inverse of the Kasteleyn matrix, and the
integrability of `1 / P_w` for liquid weights, where `P_w` has zeros, are not proved in this
file. -/
def lozengeKernel (w₁ w₂ w₃ : ℝ) (d : ℤ × ℤ) : ℂ :=
  ((4 * Real.pi ^ 2)⁻¹ : ℝ) • ∫ p in Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi),
    exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2

/-- The value of the kernel. -/
theorem lozengeKernel_def (w₁ w₂ w₃ : ℝ) (d : ℤ × ℤ) :
    lozengeKernel w₁ w₂ w₃ d =
      ((4 * Real.pi ^ 2)⁻¹ : ℝ) • ∫ p in Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi),
        exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2 :=
  (rfl)

/-- The angle `θ₀ = arccos ((w₁² − w₂² − w₃²) / (2 w₂ w₃))`. For liquid weights it is the first
coordinate of a zero of `P_w` (`lozengeCharFun_eq_zero_iff`); for other weights `arccos` clamps
its argument and `θ₀` need not belong to any zero. -/
def lozengeZeroAngleFst (w₁ w₂ w₃ : ℝ) : ℝ :=
  Real.arccos ((w₁ ^ 2 - w₂ ^ 2 - w₃ ^ 2) / (2 * w₂ * w₃))

/-- The value of `θ₀`. -/
theorem lozengeZeroAngleFst_def (w₁ w₂ w₃ : ℝ) :
    lozengeZeroAngleFst w₁ w₂ w₃ = Real.arccos ((w₁ ^ 2 - w₂ ^ 2 - w₃ ^ 2) / (2 * w₂ * w₃)) :=
  (rfl)

/-- The angle `φ₀ = arccos ((w₂² − w₁² − w₃²) / (2 w₁ w₃))`. For liquid weights it is the
second coordinate of a zero of `P_w` (`lozengeCharFun_eq_zero_iff`); for other weights `arccos`
clamps its argument and `φ₀` need not belong to any zero. -/
def lozengeZeroAngleSnd (w₁ w₂ w₃ : ℝ) : ℝ :=
  Real.arccos ((w₂ ^ 2 - w₁ ^ 2 - w₃ ^ 2) / (2 * w₁ * w₃))

/-- The value of `φ₀`. -/
theorem lozengeZeroAngleSnd_def (w₁ w₂ w₃ : ℝ) :
    lozengeZeroAngleSnd w₁ w₂ w₃ = Real.arccos ((w₂ ^ 2 - w₁ ^ 2 - w₃ ^ 2) / (2 * w₁ * w₃)) :=
  (rfl)

/-- The real part of `P_w(θ, φ)` is `w₃ + w₂ cos θ + w₁ cos φ`. -/
@[simp]
theorem lozengeCharFun_re (w₁ w₂ w₃ θ φ : ℝ) :
    (lozengeCharFun w₁ w₂ w₃ θ φ).re = w₃ + w₂ * Real.cos θ + w₁ * Real.cos φ := by
  simp only [lozengeCharFun, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    exp_ofReal_mul_I_re, exp_neg_ofReal_mul_I_re]

/-- The imaginary part of `P_w(θ, φ)` is `w₂ sin θ − w₁ sin φ`. -/
@[simp]
theorem lozengeCharFun_im (w₁ w₂ w₃ θ φ : ℝ) :
    (lozengeCharFun w₁ w₂ w₃ θ φ).im = w₂ * Real.sin θ - w₁ * Real.sin φ := by
  simp only [lozengeCharFun, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    exp_ofReal_mul_I_im, exp_neg_ofReal_mul_I_im]
  ring

/-- `P_w(θ, φ) = 0` if and only if `w₃ + w₂ cos θ + w₁ cos φ = 0` and `w₂ sin θ = w₁ sin φ`. -/
theorem lozengeCharFun_eq_zero_iff_re_im {w₁ w₂ w₃ θ φ : ℝ} :
    lozengeCharFun w₁ w₂ w₃ θ φ = 0 ↔
      w₃ + w₂ * Real.cos θ + w₁ * Real.cos φ = 0 ∧ w₂ * Real.sin θ = w₁ * Real.sin φ := by
  rw [Complex.ext_iff, lozengeCharFun_re, lozengeCharFun_im, zero_re, zero_im, sub_eq_zero]

namespace IsLiquidWeights

variable {w₁ w₂ w₃ : ℝ}

/-- Liquid weights are positive: `w₁ > 0`. -/
theorem pos_fst (h : IsLiquidWeights w₁ w₂ w₃) : 0 < w₁ := by
  obtain ⟨_, _, _⟩ := h; linarith

/-- Liquid weights are positive: `w₂ > 0`. -/
theorem pos_snd (h : IsLiquidWeights w₁ w₂ w₃) : 0 < w₂ := by
  obtain ⟨_, _, _⟩ := h; linarith

/-- Liquid weights are positive: `w₃ > 0`. -/
theorem pos_thd (h : IsLiquidWeights w₁ w₂ w₃) : 0 < w₃ := by
  obtain ⟨_, _, _⟩ := h; linarith

/-- Liquidity is symmetric in the first two weights. -/
theorem swap (h : IsLiquidWeights w₁ w₂ w₃) : IsLiquidWeights w₂ w₁ w₃ := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨h₂, h₁, by linarith⟩

/-- For liquid weights the quotient `(w₁² − w₂² − w₃²) / (2 w₂ w₃)` lies in `(−1, 1)`, so it is
the cosine of the zero angle `θ₀` (`cos_lozengeZeroAngleFst`). -/
theorem div_mem_Ioo (h : IsLiquidWeights w₁ w₂ w₃) :
    (w₁ ^ 2 - w₂ ^ 2 - w₃ ^ 2) / (2 * w₂ * w₃) ∈ Ioo (-1) 1 := by
  have h1 := h.pos_fst
  have h2 := h.pos_snd
  have h3 := h.pos_thd
  obtain ⟨ha, hb, hc⟩ := h
  have hd : 0 < 2 * w₂ * w₃ := by positivity
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_one hd]; nlinarith

/-- For liquid weights `θ₀ ∈ (0, π)`. -/
theorem lozengeZeroAngleFst_mem_Ioo (h : IsLiquidWeights w₁ w₂ w₃) :
    lozengeZeroAngleFst w₁ w₂ w₃ ∈ Ioo 0 Real.pi :=
  ⟨Real.arccos_pos.2 h.div_mem_Ioo.2, Real.arccos_lt_pi.2 h.div_mem_Ioo.1⟩

/-- For liquid weights `φ₀ ∈ (0, π)`. -/
theorem lozengeZeroAngleSnd_mem_Ioo (h : IsLiquidWeights w₁ w₂ w₃) :
    lozengeZeroAngleSnd w₁ w₂ w₃ ∈ Ioo 0 Real.pi :=
  h.swap.lozengeZeroAngleFst_mem_Ioo

/-- For liquid weights `cos θ₀ = (w₁² − w₂² − w₃²) / (2 w₂ w₃)`. -/
theorem cos_lozengeZeroAngleFst (h : IsLiquidWeights w₁ w₂ w₃) :
    Real.cos (lozengeZeroAngleFst w₁ w₂ w₃) = (w₁ ^ 2 - w₂ ^ 2 - w₃ ^ 2) / (2 * w₂ * w₃) :=
  Real.cos_arccos h.div_mem_Ioo.1.le h.div_mem_Ioo.2.le

/-- For liquid weights `cos φ₀ = (w₂² − w₁² − w₃²) / (2 w₁ w₃)`. -/
theorem cos_lozengeZeroAngleSnd (h : IsLiquidWeights w₁ w₂ w₃) :
    Real.cos (lozengeZeroAngleSnd w₁ w₂ w₃) = (w₂ ^ 2 - w₁ ^ 2 - w₃ ^ 2) / (2 * w₁ * w₃) :=
  h.swap.cos_lozengeZeroAngleFst

/-- The two zero angles are related by `w₂ sin θ₀ = w₁ sin φ₀`. -/
theorem mul_sin_lozengeZeroAngleFst (h : IsLiquidWeights w₁ w₂ w₃) :
    w₂ * Real.sin (lozengeZeroAngleFst w₁ w₂ w₃) =
      w₁ * Real.sin (lozengeZeroAngleSnd w₁ w₂ w₃) := by
  have h1 := h.pos_fst
  have h2 := h.pos_snd
  have h3 := h.pos_thd
  have hX := h.div_mem_Ioo
  have hY := h.swap.div_mem_Ioo
  rw [lozengeZeroAngleFst, lozengeZeroAngleSnd, Real.sin_arccos, Real.sin_arccos]
  refine (pow_left_inj₀ (mul_nonneg h2.le (Real.sqrt_nonneg _))
    (mul_nonneg h1.le (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith [hX.1, hX.2]),
    Real.sq_sqrt (by nlinarith [hY.1, hY.2])]
  field_simp
  ring

end IsLiquidWeights

variable {w₁ w₂ w₃ θ φ : ℝ}

/-- At a zero of `P_w` with `w₂, w₃ ≠ 0`, `cos θ = (w₁² − w₂² − w₃²) / (2 w₂ w₃)`: the side
`w₁ e^{−iφ} = −(w₃ + w₂ e^{iθ})` has length `w₁`. -/
theorem cos_eq_of_lozengeCharFun_eq_zero (h₂ : w₂ ≠ 0) (h₃ : w₃ ≠ 0)
    (h : lozengeCharFun w₁ w₂ w₃ θ φ = 0) :
    Real.cos θ = (w₁ ^ 2 - w₂ ^ 2 - w₃ ^ 2) / (2 * w₂ * w₃) := by
  obtain ⟨hre, him⟩ := lozengeCharFun_eq_zero_iff_re_im.1 h
  rw [eq_div_iff (by positivity)]
  linear_combination w₁ ^ 2 * Real.sin_sq_add_cos_sq φ -
    (w₁ * Real.cos φ - w₃ - w₂ * Real.cos θ) * hre +
    (w₁ * Real.sin φ + w₂ * Real.sin θ) * him - w₂ ^ 2 * Real.sin_sq_add_cos_sq θ

/-- At a zero of `P_w`, `w₁ sin(θ + φ) = −w₃ sin θ`. -/
theorem mul_sin_add_eq_of_lozengeCharFun_eq_zero (h : lozengeCharFun w₁ w₂ w₃ θ φ = 0) :
    w₁ * Real.sin (θ + φ) = -(w₃ * Real.sin θ) := by
  obtain ⟨hre, him⟩ := lozengeCharFun_eq_zero_iff_re_im.1 h
  rw [Real.sin_add]
  linear_combination Real.sin θ * hre - Real.cos θ * him

/-- For liquid weights, `sin(θ + φ) ≠ 0` at every zero `(θ, φ)` of `P_w`. -/
theorem IsLiquidWeights.sin_add_ne_zero (hw : IsLiquidWeights w₁ w₂ w₃)
    (h : lozengeCharFun w₁ w₂ w₃ θ φ = 0) : Real.sin (θ + φ) ≠ 0 := by
  intro hs
  have h1 := mul_sin_add_eq_of_lozengeCharFun_eq_zero h
  rw [hs, mul_zero, zero_eq_neg, mul_eq_zero] at h1
  have hsin := h1.resolve_left hw.pos_thd.ne'
  have hcos := cos_eq_of_lozengeCharFun_eq_zero hw.pos_snd.ne' hw.pos_thd.ne' h
  have hc := hw.div_mem_Ioo
  rw [← hcos] at hc
  have := Real.sin_sq_add_cos_sq θ
  rw [hsin] at this
  nlinarith [hc.1, hc.2]

/-- **The zeros of the characteristic function.** For liquid weights, `P_w(θ, φ) = 0` if and
only if `(θ, φ)` is `(θ₀, φ₀)` or `(−θ₀, −φ₀)` modulo `2π` in each variable. -/
theorem lozengeCharFun_eq_zero_iff (hw : IsLiquidWeights w₁ w₂ w₃) :
    lozengeCharFun w₁ w₂ w₃ θ φ = 0 ↔ ∃ m n : ℤ,
      (θ = 2 * m * Real.pi + lozengeZeroAngleFst w₁ w₂ w₃ ∧
        φ = 2 * n * Real.pi + lozengeZeroAngleSnd w₁ w₂ w₃) ∨
      (θ = 2 * m * Real.pi - lozengeZeroAngleFst w₁ w₂ w₃ ∧
        φ = 2 * n * Real.pi - lozengeZeroAngleSnd w₁ w₂ w₃) := by
  have h1 := hw.pos_fst
  have h2 := hw.pos_snd
  have h3 := hw.pos_thd
  have hθ₀ := Real.sin_pos_of_pos_of_lt_pi hw.lozengeZeroAngleFst_mem_Ioo.1
    hw.lozengeZeroAngleFst_mem_Ioo.2
  have hφ₀ := Real.sin_pos_of_pos_of_lt_pi hw.lozengeZeroAngleSnd_mem_Ioo.1
    hw.lozengeZeroAngleSnd_mem_Ioo.2
  have hsin := hw.mul_sin_lozengeZeroAngleFst
  constructor
  · intro h
    have hc₁ := cos_eq_of_lozengeCharFun_eq_zero h2.ne' h3.ne' h
    have hc₂ : Real.cos φ = (w₂ ^ 2 - w₁ ^ 2 - w₃ ^ 2) / (2 * w₁ * w₃) := by
      refine cos_eq_of_lozengeCharFun_eq_zero (θ := φ) (φ := θ) h1.ne' h3.ne' ?_
      obtain ⟨hre, him⟩ := lozengeCharFun_eq_zero_iff_re_im.1 h
      exact lozengeCharFun_eq_zero_iff_re_im.2 ⟨by linarith, him.symm⟩
    rw [← hw.cos_lozengeZeroAngleFst, eq_comm, Real.cos_eq_cos_iff] at hc₁
    rw [← hw.cos_lozengeZeroAngleSnd, eq_comm, Real.cos_eq_cos_iff] at hc₂
    obtain ⟨m, hm⟩ := hc₁
    obtain ⟨n, hn⟩ := hc₂
    have him := (lozengeCharFun_eq_zero_iff_re_im.1 h).2
    refine ⟨m, n, ?_⟩
    rcases hm with hm | hm <;> rcases hn with hn | hn
    · exact Or.inl ⟨hm, hn⟩
    · rw [hm, hn, Real.sin_two_mul_int_mul_pi_add, Real.sin_two_mul_int_mul_pi_sub] at him
      nlinarith [mul_pos h2 hθ₀, mul_pos h1 hφ₀]
    · rw [hm, hn, Real.sin_two_mul_int_mul_pi_add, Real.sin_two_mul_int_mul_pi_sub] at him
      nlinarith [mul_pos h2 hθ₀, mul_pos h1 hφ₀]
    · exact Or.inr ⟨hm, hn⟩
  · rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      refine lozengeCharFun_eq_zero_iff_re_im.2 ⟨?_, ?_⟩ <;>
      simp only [Real.sin_two_mul_int_mul_pi_add, Real.sin_two_mul_int_mul_pi_sub,
        Real.cos_two_mul_int_mul_pi_add, Real.cos_two_mul_int_mul_pi_sub,
        hw.cos_lozengeZeroAngleFst, hw.cos_lozengeZeroAngleSnd]
    · field_simp; ring
    · exact hsin
    · field_simp; ring
    · linarith

/-- The partial derivative of `P_w` in `θ` is `i w₂ e^{iθ}`. -/
theorem hasDerivAt_lozengeCharFun_fst (w₁ w₂ w₃ θ φ : ℝ) :
    HasDerivAt (fun θ => lozengeCharFun w₁ w₂ w₃ θ φ) (I * w₂ * exp (θ * I)) θ := by
  have h := ((((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp.const_mul (w₂ : ℂ)).const_add
    (w₃ : ℂ) |>.add_const (w₁ * exp (-(φ * I)))
  simp only [id, ofReal_one, one_mul] at h
  simp only [lozengeCharFun_def]
  convert h using 1
  ring

/-- The partial derivative of `P_w` in `φ` is `−i w₁ e^{−iφ}`. -/
theorem hasDerivAt_lozengeCharFun_snd (w₁ w₂ w₃ θ φ : ℝ) :
    HasDerivAt (fun φ => lozengeCharFun w₁ w₂ w₃ θ φ) (-(I * w₁ * exp (-(φ * I)))) φ := by
  have h := ((((hasDerivAt_id φ).ofReal_comp).mul_const I).neg.cexp.const_mul
    (w₁ : ℂ)).const_add ((w₃ : ℂ) + w₂ * exp (θ * I))
  simp only [id, ofReal_one, one_mul, Pi.neg_apply] at h
  simp only [lozengeCharFun_def]
  convert h using 1
  ring

/-- **The real Jacobian at a zero is invertible.** For liquid weights, at every zero of `P_w`
the two partial derivatives `i w₂ e^{iθ}` and `−i w₁ e^{−iφ}` are linearly independent over
`ℝ`. -/
theorem linearIndependent_deriv_lozengeCharFun (hw : IsLiquidWeights w₁ w₂ w₃)
    (h : lozengeCharFun w₁ w₂ w₃ θ φ = 0) :
    LinearIndependent ℝ ![I * w₂ * exp (θ * I), -(I * w₁ * exp (-(φ * I)))] := by
  have hs := hw.sin_add_ne_zero h
  have hd : w₁ * w₂ * Real.sin (θ + φ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hw.pos_fst.ne' hw.pos_snd.ne') hs
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hre : -(s * (w₂ * Real.sin θ)) - t * (w₁ * Real.sin φ) = 0 := by
    have h' := congrArg re hst
    simp only [add_re, smul_re, smul_eq_mul, neg_re, mul_re, mul_im, I_re, I_im, ofReal_re,
      ofReal_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, exp_neg_ofReal_mul_I_re,
      exp_neg_ofReal_mul_I_im, zero_re] at h'
    linear_combination h'
  have him : s * (w₂ * Real.cos θ) - t * (w₁ * Real.cos φ) = 0 := by
    have h' := congrArg im hst
    simp only [add_im, smul_im, smul_eq_mul, neg_im, mul_re, mul_im, I_re, I_im, ofReal_re,
      ofReal_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, exp_neg_ofReal_mul_I_re,
      exp_neg_ofReal_mul_I_im, zero_im] at h'
    linear_combination h'
  rw [Real.sin_add] at hd
  constructor
  · refine (mul_eq_zero.1 (?_ : s * (w₁ * w₂ * (Real.sin θ * Real.cos φ +
      Real.cos θ * Real.sin φ)) = 0)).resolve_right hd
    linear_combination (-(w₁ * Real.cos φ)) * hre + (w₁ * Real.sin φ) * him
  · refine (mul_eq_zero.1 (?_ : t * (w₁ * w₂ * (Real.sin θ * Real.cos φ +
      Real.cos θ * Real.sin φ)) = 0)).resolve_right hd
    linear_combination (-(w₂ * Real.cos θ)) * hre - (w₂ * Real.sin θ) * him

/-- **The real derivative of `P_w`.** At `x = (θ, φ)`, the derivative of
`(θ, φ) ↦ P_w(θ, φ)` sends `(a, b)` to `a (i w₂ e^{iθ}) + b (−i w₁ e^{−iφ})`, combining the
partial derivatives `TauCeti.hasDerivAt_lozengeCharFun_fst` and
`TauCeti.hasDerivAt_lozengeCharFun_snd`. -/
theorem hasFDerivAt_lozengeCharFun (w₁ w₂ w₃ : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => lozengeCharFun w₁ w₂ w₃ p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (I * w₂ * exp (x.1 * I)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(I * w₁ * exp (-(x.2 * I))))) x := by
  set A : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I
  set B : ℝ × ℝ →L[ℝ] ℂ := -(ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight I
  have hA : HasFDerivAt (fun p : ℝ × ℝ => (p.1 : ℂ) * I) A x := by
    convert A.hasFDerivAt using 1
    funext p
    simp [A, real_smul]
  have hB : HasFDerivAt (fun p : ℝ × ℝ => -((p.2 : ℂ) * I)) B x := by
    convert B.hasFDerivAt using 1
    funext p
    simp [B, real_smul]
  have h := ((hA.cexp.const_mul (w₂ : ℂ)).const_add (w₃ : ℂ)).add (hB.cexp.const_mul (w₁ : ℂ))
  convert h using 1
  · funext p
    simp only [lozengeCharFun_def, Pi.add_apply]
  · refine ContinuousLinearMap.ext fun h => ?_
    simp [A, B, real_smul]
    ring

/-- At a zero of `P_w`, for liquid weights, the real derivative of `P_w` is injective. -/
theorem IsLiquidWeights.exists_hasFDerivAt_injective (hw : IsLiquidWeights w₁ w₂ w₃)
    {x : ℝ × ℝ} (hx : lozengeCharFun w₁ w₂ w₃ x.1 x.2 = 0) :
    ∃ L : ℝ × ℝ →L[ℝ] ℂ, HasFDerivAt (fun p : ℝ × ℝ => lozengeCharFun w₁ w₂ w₃ p.1 p.2) L x ∧
      Function.Injective L := by
  refine ⟨_, hasFDerivAt_lozengeCharFun w₁ w₂ w₃ x, (injective_iff_map_eq_zero _).2
    fun h hh => ?_⟩
  have := (LinearIndependent.pair_iff.1 (linearIndependent_deriv_lozengeCharFun hw hx)) h.1 h.2
    (by simpa using hh)
  exact Prod.ext this.1 this.2

end TauCeti
