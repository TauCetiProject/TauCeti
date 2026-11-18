/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard

/-!
# Vertical strips

Mathlib's three-lines theorem is stated on the open strip `verticalStrip a b` and the closed
strip `verticalClosedStrip a b`, the preimages of `Ioo a b` and `Icc a b` under `Complex.re`.
This file records their membership criteria, behavior under reflection, and the topological
facts used when applying `DiffContOnCl` on the strip. It also introduces the Gaussian damping
factor `TauCeti.Complex.HadamardThreeLines.gaussian δ θ z = exp (δ (z - θ)²)`, which is bounded on
the unit strip, equal to one at `θ`, and decays along vertical lines.
-/

public section

open Complex Complex.HadamardThreeLines Set

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

/-- For `a ≠ b`, the closed strip is the closure of the open strip, so a function continuous on
the closure of the open strip is continuous on its two boundary lines. -/
theorem closure_verticalStrip (hab : a ≠ b) :
    closure (verticalStrip a b) = verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo hab, verticalClosedStrip]

/-! ### A Gaussian damping factor -/

/-- The Gaussian factor `exp (δ (z - θ)²)`. It equals one at `θ` (`gaussian_self`), is bounded on
the unit strip for `δ ≥ 0` (`norm_gaussian_le`) and, for `δ > 0`, tends to zero along every
vertical line (`tendsto_gaussian`). Multiplying by it turns a function bounded on the strip into
one that vanishes at both ends of the strip, without changing its value at `θ`. -/
noncomputable def gaussian (δ θ : ℝ) (z : ℂ) : ℂ :=
  exp (δ * (z - θ) ^ 2)

theorem gaussian_def (δ θ : ℝ) (z : ℂ) : gaussian δ θ z = exp (δ * (z - θ) ^ 2) :=
  (rfl)

@[simp]
theorem gaussian_self (δ θ : ℝ) : gaussian δ θ θ = 1 := by
  simp [gaussian]

theorem differentiable_gaussian (δ θ : ℝ) : Differentiable ℂ (gaussian δ θ) := by
  unfold gaussian
  fun_prop

theorem norm_gaussian (δ θ : ℝ) (z : ℂ) :
    ‖gaussian δ θ z‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [gaussian, norm_exp]
  congr 1
  simp [sq]

/-- For `δ ≥ 0`, the Gaussian factor is bounded on the closed unit strip. -/
theorem norm_gaussian_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖gaussian δ θ z‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_gaussian]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hδ)
  have h : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [hz.1, le_abs_self θ]) (by linarith [hz.2, neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

/-- For `δ ≥ 0` and `0 ≤ θ ≤ 1`, the Gaussian factor is at most `exp δ` on the closed unit
strip. -/
theorem norm_gaussian_le_exp {δ : ℝ} (hδ : 0 ≤ δ) {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (hz : z ∈ verticalClosedStrip 0 1) : ‖gaussian δ θ z‖ ≤ Real.exp δ := by
  rw [norm_gaussian, Real.exp_le_exp]
  obtain ⟨hz0, hz1⟩ := hz
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h : (z.re - θ) ^ 2 - z.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.im]
  nlinarith

/-- For `δ > 0`, the Gaussian factor tends to zero along the vertical line `re z = a`. -/
theorem tendsto_gaussian {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) :
    Filter.Tendsto (fun t : ℝ => gaussian δ θ (a + t * I)) (Filter.cocompact ℝ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Filter.Tendsto (fun t : ℝ => t ^ 2) (Filter.cocompact ℝ) Filter.atTop :=
    ((Filter.tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun t => by simp
  have h : Filter.Tendsto (fun t : ℝ => δ * ((a - θ) ^ 2 - t ^ 2)) (Filter.cocompact ℝ)
      Filter.atBot :=
    ((Filter.tendsto_atBot_add_const_left _ ((a - θ) ^ 2)
      (Filter.tendsto_neg_atTop_atBot.comp hsq)).const_mul_atBot hδ).congr fun t => by
        simp [sub_eq_add_neg]
  have heq : (fun t : ℝ => ‖gaussian δ θ (a + t * I)‖) =
      Real.exp ∘ fun t => δ * ((a - θ) ^ 2 - t ^ 2) := by
    funext t
    simp [norm_gaussian]
  rw [heq]
  exact Real.tendsto_exp_atBot.comp h

end TauCeti.Complex.HadamardThreeLines
