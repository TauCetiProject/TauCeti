/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Vertical strips

Mathlib's three-lines theorem is stated on the open strip `verticalStrip a b` and the closed
strip `verticalClosedStrip a b`, the preimages of `Ioo a b` and `Icc a b` under `Complex.re`.
This file records their membership criteria, behavior under reflection, the topological facts used
when applying `DiffContOnCl` on the strip, and the Cauchy rectangle contour-shift identity
`DiffContOnCl.intervalIntegral_add_mul_I_eq` equating vertical line integrals of vertically
periodic holomorphic strip functions.
-/

public section

open Complex Complex.HadamardThreeLines Set
open scoped Interval

namespace TauCeti.Complex.HadamardThreeLines

variable {a b : ℝ} {z : ℂ}

@[simp]
theorem mem_verticalStrip_iff : z ∈ verticalStrip a b ↔ z.re ∈ Ioo a b :=
  Iff.rfl

@[simp]
theorem mem_verticalClosedStrip_iff : z ∈ verticalClosedStrip a b ↔ z.re ∈ Icc a b :=
  Iff.rfl

/-- Reflection by `z ↦ w - z` reverses the real endpoints of an open vertical strip. -/
theorem sub_mem_verticalStrip_iff (w z : ℂ) :
    w - z ∈ verticalStrip a b ↔ z ∈ verticalStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalStrip_iff, mem_Ioo, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection by `z ↦ w - z` reverses the real endpoints of a closed vertical strip. -/
theorem sub_mem_verticalClosedStrip_iff (w z : ℂ) :
    w - z ∈ verticalClosedStrip a b ↔ z ∈ verticalClosedStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalClosedStrip_iff, mem_Icc, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection in the middle of the unit strip preserves open-strip membership. -/
theorem one_sub_mem_verticalStrip_iff :
    1 - z ∈ verticalStrip 0 1 ↔ z ∈ verticalStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalStrip_iff (a := 0) (b := 1) (1 : ℂ) z

/-- Reflection in the middle of the unit strip preserves closed-strip membership. -/
theorem one_sub_mem_verticalClosedStrip_iff :
    1 - z ∈ verticalClosedStrip 0 1 ↔ z ∈ verticalClosedStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalClosedStrip_iff (a := 0) (b := 1) (1 : ℂ) z

theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage continuous_re

theorem verticalStrip_subset_verticalClosedStrip (a b : ℝ) :
    verticalStrip a b ⊆ verticalClosedStrip a b :=
  preimage_mono Ioo_subset_Icc_self

theorem closure_verticalStrip_subset (a b : ℝ) :
    closure (verticalStrip a b) ⊆ verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re]
  exact preimage_mono (closure_minimal Ioo_subset_Icc_self isClosed_Icc)

/-- The closure of a nondegenerate open vertical strip is the corresponding closed strip. -/
@[simp]
theorem closure_verticalStrip (hab : a ≠ b) :
    closure (verticalStrip a b) = verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo hab]; rfl

end TauCeti.Complex.HadamardThreeLines

open TauCeti.Complex.HadamardThreeLines

/-- **Contour shift across a vertical strip.** If `f : ℂ → E` is holomorphic on `verticalStrip a b`
(`a ≤ b`), continuous on its closure, and vertically periodic of period `T` on `[a, b]`, then its
vertical interval integrals along `re z = a` and `re z = b` over `0..T` agree. -/
theorem DiffContOnCl.intervalIntegral_add_mul_I_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {a b : ℝ} (hf : DiffContOnCl ℂ f (verticalStrip a b))
    (hab : a ≤ b) (T : ℝ) (hper : ∀ x ∈ Icc a b, f (x + T * I) = f x) :
    (∫ y : ℝ in 0..T, f (a + y * I)) = ∫ y : ℝ in 0..T, f (b + y * I) := by
  rcases hab.eq_or_lt with rfl | hab
  · rfl
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
    ⟨a, 0⟩ ⟨b, T⟩
    (hf.continuousOn.mono fun z hz => by
      rw [closure_verticalStrip hab.ne]
      simpa [uIcc_of_le hab.le] using hz.1)
    (hf.differentiableOn.mono fun z hz => by
      simpa [min_eq_left hab.le, max_eq_right hab.le] using hz.1)
  have htop : (∫ x : ℝ in a..b, f (x + T * I)) = ∫ x : ℝ in a..b, f (x + (0 : ℝ) * I) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [ofReal_zero, zero_mul, add_zero]
      exact hper x (uIcc_of_le hab.le ▸ hx)
  rw [htop, sub_self, zero_add, sub_eq_zero, smul_right_inj I_ne_zero] at hrect
  exact hrect.symm

/-- Twisting a `T`-vertically periodic strip function by `exp (-(2π m / T) z)` (`m : ℤ`) preserves
vertical `T`-periodicity, so its vertical integrals over `0..T` along `re z = a` and `re z = b`
agree. -/
theorem DiffContOnCl.intervalIntegral_exp_smul_add_mul_I_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b : ℝ}
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) (hab : a ≤ b) (T : ℝ)
    (hper : ∀ x ∈ Icc a b, f (x + T * I) = f x) (m : ℤ) :
    (∫ y : ℝ in 0..T, exp (-(2 * Real.pi * m / T : ℂ) * (a + y * I)) • f (a + y * I)) =
      ∫ y : ℝ in 0..T, exp (-(2 * Real.pi * m / T : ℂ) * (b + y * I)) • f (b + y * I) := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp
  set ω : ℂ := -(2 * Real.pi * m / T : ℂ)
  have hexp : Differentiable ℂ fun z : ℂ => exp (ω * z) := by fun_prop
  refine (hexp.diffContOnCl.smul hf).intervalIntegral_add_mul_I_eq hab T fun x hx => ?_
  have hωT : ω * (T * I) = ((-m : ℤ) : ℂ) * (2 * Real.pi * I) := by
    have : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT
    simp only [ω]; push_cast; field_simp
  simp only [hper x hx, mul_add, Complex.exp_add, hωT, Complex.exp_int_mul_two_pi_mul_I, mul_one]
