/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Domains and branches of the Legendre functions

The Ferrers functions of the first and second kind (DLMF 14.3.1, 14.3.12) are holomorphic on the
doubly cut plane `D = {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} = ℂ \ ((-∞, -1] ∪ [1, ∞))`, and
the associated Legendre functions `P^μ_ν(z)`, `Q^μ_ν(z)` and Olver's `𝑸^μ_ν(z)` on the cut plane
`U = {z | z - 1 ∈ slitPlane} = ℂ \ (-∞, 1]`. Their definitions multiply a Gauss hypergeometric
function by principal powers: of `(1 + z) / (1 - z)` and of `1 - z²` on `D`, and of
`(z + 1) / (z - 1)`, `z - 1`, `z + 1` and `z` on `U`; the argument of the hypergeometric function is
`(1 - z) / 2` or `z²` on `D`, and `(1 - z) / 2` or `z⁻²` on `U`. This file proves that every one of
these bases lies in the slit plane, so that each power is holomorphic on its domain, and that every
argument lies in the cut plane `{w | 1 - w ∈ slitPlane}` of the hypergeometric function. It also
proves the branch identities between these powers, which hold on the whole domain because the
domain is connected and the two sides are continuous logarithms of one function that agree at a
point.

## Main results

* `Complex.one_sub_sq_mem_slitPlane_iff`: `1 - z² ∈ slitPlane` exactly on `D`, so `D` is open and
  connected (`Complex.isOpen_setOf_one_sub_mem_slitPlane_and_one_add_mem_slitPlane`,
  `Complex.isConnected_setOf_one_sub_mem_slitPlane_and_one_add_mem_slitPlane`).
* `Complex.one_add_div_one_sub_mem_slitPlane_iff`, `Complex.bijOn_one_add_div_one_sub`: the Möbius
  map `z ↦ (1 + z) / (1 - z)` sends `D` bijectively onto the slit plane.
* `Complex.one_sub_sq_cpow`, `Complex.one_add_div_one_sub_cpow`: on `D`,
  `(1 - z²)^s = (1 - z)^s (1 + z)^s` and `((1 + z) / (1 - z))^s = (1 + z)^s (1 - z)^(-s)`.
* `Complex.add_one_div_sub_one_mem_slitPlane`, `Complex.one_sub_inv_sq_mem_slitPlane`: on `U`,
  `(z + 1) / (z - 1)` lies in the slit plane and `z⁻²` in the cut plane of the hypergeometric
  function; `Complex.one_sub_inv_sq_mem_slitPlane_iff` says that `z⁻² ∈ [1, ∞)` only for
  `z ∈ [-1, 1]`.
* `Complex.add_one_div_sub_one_cpow`: on `U`, `((z + 1) / (z - 1))^s = (z + 1)^s (z - 1)^(-s)`.
* `Complex.sq_sub_one_cpow`: for `0 < re z`, `(z² - 1)^s = (z - 1)^s (z + 1)^s`, so the product
  `(z - 1)^s (z + 1)^s`, which is holomorphic on `U`, is the principal power on the right
  half-plane and the principal real power on `(1, ∞)`
  (`Complex.ofReal_sub_one_cpow_mul_ofReal_add_one_cpow`). On the left half-plane the principal
  `(z² - 1)^s` jumps across the imaginary axis, which is why the definition of `𝑸^μ_ν` uses the
  product.
* `Complex.differentiableOn_one_add_div_one_sub_cpow`, `Complex.differentiableOn_one_sub_sq_cpow`,
  `Complex.differentiableOn_add_one_div_sub_one_cpow`,
  `Complex.differentiableOn_sub_one_cpow_mul_add_one_cpow`: the power prefactors are holomorphic on
  their domains.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 5, §12.2 and §15.1.
* NIST *Digital Library of Mathematical Functions*, §14.3 and §14.21(i).
-/

public section

open Set

namespace Complex

/-! ### The doubly cut plane `ℂ \ ((-∞, -1] ∪ [1, ∞))` -/

/-- `1 - z²` lies in the slit plane exactly when `z` lies in the doubly cut plane
`ℂ \ ((-∞, -1] ∪ [1, ∞))`. -/
theorem one_sub_sq_mem_slitPlane_iff {z : ℂ} :
    1 - z ^ 2 ∈ slitPlane ↔ 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane := by
  simp only [mem_slitPlane_iff, sub_re, add_re, one_re, sub_im, add_im, one_im, sq, mul_re,
    mul_im]
  by_cases hy : z.im = 0
  · simp only [hy, mul_zero, sub_zero, zero_mul, add_zero, ne_eq, not_true_eq_false, or_false]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h₁, h₂⟩
      nlinarith
  · have hy' : -z.im ≠ 0 := neg_ne_zero.2 hy
    simp only [zero_sub, ne_eq, zero_add, hy, hy', not_false_eq_true, or_true, and_self,
      iff_true]
    by_cases hx : z.re = 0
    · left
      simp only [hx, zero_mul, zero_sub, sub_neg_eq_add]
      nlinarith [sq_nonneg z.im]
    · right
      intro h
      have : z.re * z.im = 0 := by linarith
      exact (mul_ne_zero hx hy) this

/-- The Möbius map `z ↦ (1 + z) / (1 - z)` takes a value in the slit plane exactly on the doubly
cut plane `ℂ \ ((-∞, -1] ∪ [1, ∞))`. -/
theorem one_add_div_one_sub_mem_slitPlane_iff {z : ℂ} :
    (1 + z) / (1 - z) ∈ slitPlane ↔ 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane := by
  rcases eq_or_ne z 1 with rfl | hz
  · simp [zero_notMem_slitPlane]
  have hN : 0 < normSq (1 - z) := normSq_pos.2 (sub_ne_zero.2 hz.symm)
  -- multiplying by `‖1 - z‖²` turns the quotient into `(1 + z) * conj (1 - z)`, whose real part is
  -- `1 - ‖z‖²` and whose imaginary part is `2 * im z`
  have hmul : ((normSq (1 - z) : ℝ) : ℂ) * ((1 + z) / (1 - z)) =
      (1 + z) * (starRingEnd ℂ) (1 - z) := by
    rw [← mul_conj, mul_comm (1 - z)]
    field_simp [sub_ne_zero.2 hz.symm]
  have hiff : (1 + z) / (1 - z) ∈ slitPlane ↔ (1 + z) * (starRingEnd ℂ) (1 - z) ∈ slitPlane := by
    rw [← hmul]
    refine ⟨TauCeti.ofReal_mul_mem_slitPlane hN, fun h => ?_⟩
    simpa [hN.ne'] using TauCeti.ofReal_mul_mem_slitPlane (inv_pos.2 hN) h
  rw [hiff]
  simp only [mem_slitPlane_iff, mul_re, mul_im, add_re, add_im, sub_re, sub_im, one_re, one_im,
    conj_re, conj_im]
  by_cases hy : z.im = 0
  · simp only [hy, mul_zero, sub_zero, ne_eq, neg_zero, not_true_eq_false, or_false, add_zero,
      zero_mul]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h₁, h₂⟩
      nlinarith
  · have hy' : -z.im ≠ 0 := neg_ne_zero.2 hy
    simp only [zero_sub, ne_eq, zero_add, hy, hy', not_false_eq_true, or_true, and_self,
      iff_true]
    right
    intro h
    exact hy (by linarith)

/-- The Möbius map `z ↦ (1 + z) / (1 - z)` is a bijection from the doubly cut plane
`ℂ \ ((-∞, -1] ∪ [1, ∞))` onto the slit plane. -/
theorem bijOn_one_add_div_one_sub :
    BijOn (fun z : ℂ => (1 + z) / (1 - z)) {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane}
      slitPlane := by
  refine ⟨fun z hz => one_add_div_one_sub_mem_slitPlane_iff.2 hz, fun z₁ hz₁ z₂ hz₂ h => ?_,
    fun w hw => ?_⟩
  · have h₁ := slitPlane_ne_zero hz₁.1
    have h₂ := slitPlane_ne_zero hz₂.1
    rw [div_eq_div_iff h₁ h₂] at h
    linear_combination h / 2
  · have hw₁ : w + 1 ≠ 0 := by
      intro h
      rw [eq_neg_of_add_eq_zero_left h] at hw
      exact (by norm_num [mem_slitPlane_iff] : (-1 : ℂ) ∉ slitPlane) hw
    have hz : (1 + (w - 1) / (w + 1)) / (1 - (w - 1) / (w + 1)) = w := by
      field_simp
      ring
    exact ⟨(w - 1) / (w + 1), one_add_div_one_sub_mem_slitPlane_iff.1 (by rw [hz]; exact hw), hz⟩

/-- The doubly cut plane `ℂ \ ((-∞, -1] ∪ [1, ∞))` is open. -/
theorem isOpen_setOf_one_sub_mem_slitPlane_and_one_add_mem_slitPlane :
    IsOpen {z : ℂ | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} := by
  simpa only [one_sub_sq_mem_slitPlane_iff] using isOpen_setOf_one_sub_pow_mem_slitPlane 2

/-- The doubly cut plane `ℂ \ ((-∞, -1] ∪ [1, ∞))` is connected. -/
theorem isConnected_setOf_one_sub_mem_slitPlane_and_one_add_mem_slitPlane :
    IsConnected {z : ℂ | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} := by
  simpa only [one_sub_sq_mem_slitPlane_iff] using
    isConnected_setOf_one_sub_pow_mem_slitPlane two_pos

/-- The argument `(1 - z) / 2` of the hypergeometric function in the Ferrers function of the first
kind and in `P^μ_ν(z)` lies in its cut plane exactly when `1 + z` lies in the slit plane. -/
theorem one_sub_one_sub_div_two_mem_slitPlane_iff {z : ℂ} :
    1 - (1 - z) / 2 ∈ slitPlane ↔ 1 + z ∈ slitPlane := by
  rw [show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
  simp [mem_slitPlane_iff]

/-- On the doubly cut plane, `log (1 - z²) = log (1 - z) + log (1 + z)`. -/
theorem log_one_sub_sq {z : ℂ} (hz₁ : 1 - z ∈ slitPlane) (hz₂ : 1 + z ∈ slitPlane) :
    log (1 - z ^ 2) = log (1 - z) + log (1 + z) := by
  refine ContinuousOn.eqOn_of_eqOn_exp_comp (L₁ := fun w => log (1 - w ^ 2))
    (L₂ := fun w => log (1 - w) + log (1 + w))
    (s := {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane})
    (hs := isConnected_setOf_one_sub_mem_slitPlane_and_one_add_mem_slitPlane.isPreconnected)
    (fun w hw => (ContinuousAt.clog (f := fun t => 1 - t ^ 2) (by fun_prop)
      (one_sub_sq_mem_slitPlane_iff.2 hw)).continuousWithinAt)
    (fun w hw => ((ContinuousAt.clog (f := fun t => 1 - t) (by fun_prop) hw.1).add
      (ContinuousAt.clog (f := fun t => 1 + t) (by fun_prop) hw.2)).continuousWithinAt)
    (fun w hw => ?_) (x₀ := 0) (by simp) (by simp) ⟨hz₁, hz₂⟩
  simp only [Function.comp_apply]
  rw [exp_add, exp_log (slitPlane_ne_zero (one_sub_sq_mem_slitPlane_iff.2 hw)),
    exp_log (slitPlane_ne_zero hw.1), exp_log (slitPlane_ne_zero hw.2)]
  ring

/-- On the doubly cut plane, the principal power of `1 - z²` splits:
`(1 - z²)^s = (1 - z)^s (1 + z)^s`. -/
theorem one_sub_sq_cpow {z : ℂ} (hz₁ : 1 - z ∈ slitPlane) (hz₂ : 1 + z ∈ slitPlane) (s : ℂ) :
    (1 - z ^ 2) ^ s = (1 - z) ^ s * (1 + z) ^ s := by
  rw [cpow_def_of_ne_zero (slitPlane_ne_zero (one_sub_sq_mem_slitPlane_iff.2 ⟨hz₁, hz₂⟩)),
    cpow_def_of_ne_zero (slitPlane_ne_zero hz₁), cpow_def_of_ne_zero (slitPlane_ne_zero hz₂),
    log_one_sub_sq hz₁ hz₂, add_mul, exp_add]

/-- On the doubly cut plane, `log ((1 + z) / (1 - z)) = log (1 + z) - log (1 - z)`. -/
theorem log_one_add_div_one_sub {z : ℂ} (hz₁ : 1 - z ∈ slitPlane) (hz₂ : 1 + z ∈ slitPlane) :
    log ((1 + z) / (1 - z)) = log (1 + z) - log (1 - z) := by
  refine ContinuousOn.eqOn_of_eqOn_exp_comp (L₁ := fun w => log ((1 + w) / (1 - w)))
    (L₂ := fun w => log (1 + w) - log (1 - w))
    (s := {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane})
    (hs := isConnected_setOf_one_sub_mem_slitPlane_and_one_add_mem_slitPlane.isPreconnected)
    (fun w hw => (ContinuousAt.clog
      ((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
        (slitPlane_ne_zero hw.1)) (one_add_div_one_sub_mem_slitPlane_iff.2 hw)).continuousWithinAt)
    (fun w hw => ((ContinuousAt.clog (f := fun t => 1 + t) (by fun_prop) hw.2).sub
      (ContinuousAt.clog (f := fun t => 1 - t) (by fun_prop) hw.1)).continuousWithinAt)
    (fun w hw => ?_) (x₀ := 0) (by simp) (by simp) ⟨hz₁, hz₂⟩
  simp only [Function.comp_apply]
  rw [exp_sub, exp_log (slitPlane_ne_zero (one_add_div_one_sub_mem_slitPlane_iff.2 hw)),
    exp_log (slitPlane_ne_zero hw.1), exp_log (slitPlane_ne_zero hw.2)]

/-- On the doubly cut plane, the principal power of the Möbius quotient splits:
`((1 + z) / (1 - z))^s = (1 + z)^s (1 - z)^(-s)`. -/
theorem one_add_div_one_sub_cpow {z : ℂ} (hz₁ : 1 - z ∈ slitPlane) (hz₂ : 1 + z ∈ slitPlane)
    (s : ℂ) : ((1 + z) / (1 - z)) ^ s = (1 + z) ^ s * (1 - z) ^ (-s) := by
  rw [cpow_def_of_ne_zero (slitPlane_ne_zero (one_add_div_one_sub_mem_slitPlane_iff.2 ⟨hz₁, hz₂⟩)),
    cpow_def_of_ne_zero (slitPlane_ne_zero hz₁), cpow_def_of_ne_zero (slitPlane_ne_zero hz₂),
    log_one_add_div_one_sub hz₁ hz₂, ← exp_add]
  ring_nf

/-- `z ↦ ((1 + z) / (1 - z))^s` is holomorphic on the doubly cut plane. -/
theorem differentiableOn_one_add_div_one_sub_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => ((1 + z) / (1 - z)) ^ s)
      {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} := by
  refine DifferentiableOn.cpow_const ?_ fun z hz => one_add_div_one_sub_mem_slitPlane_iff.2 hz
  exact ((differentiableOn_const 1).add differentiableOn_id).div
    ((differentiableOn_const 1).sub differentiableOn_id) fun z hz => slitPlane_ne_zero hz.1

/-- `z ↦ (1 - z²)^s` is holomorphic on the doubly cut plane. -/
theorem differentiableOn_one_sub_sq_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z ^ 2) ^ s)
      {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} :=
  ((differentiableOn_const 1).sub (differentiableOn_id.pow 2)).cpow_const
    fun _ hz => one_sub_sq_mem_slitPlane_iff.2 hz

/-! ### The cut plane `ℂ \ (-∞, 1]` -/

/-- A point of the cut plane `ℂ \ (-∞, 1]` lies in the slit plane. -/
theorem mem_slitPlane_of_sub_one_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    z ∈ slitPlane := by
  simpa using TauCeti.add_ofReal_mem_slitPlane hz zero_le_one

/-- On the cut plane `ℂ \ (-∞, 1]`, `z + 1` lies in the slit plane. -/
theorem add_one_mem_slitPlane_of_sub_one_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    z + 1 ∈ slitPlane := by
  convert TauCeti.add_ofReal_mem_slitPlane hz zero_le_two using 1
  push_cast
  ring

/-- On the cut plane `ℂ \ (-∞, 1]`, `(z + 1) / (z - 1)` lies in the slit plane. -/
theorem add_one_div_sub_one_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    (z + 1) / (z - 1) ∈ slitPlane := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact TauCeti.div_mem_slitPlane_of_im_neg (by simpa using h) (by simpa using h)
  · have hre : 1 < z.re := by
      simpa [mem_slitPlane_iff, h] using hz
    have hz' : z = (z.re : ℂ) := ext rfl (by simp [h])
    rw [hz']
    exact_mod_cast ofReal_mem_slitPlane.2 (div_pos (by linarith) (by linarith))
  · exact TauCeti.div_mem_slitPlane_of_im_pos (by simpa using h) (by simpa using h)

/-- `1 - z⁻²` lies in the slit plane unless `z` is a nonzero real number in `[-1, 1]`: the argument
`z⁻²` of the hypergeometric function in `𝑸^μ_ν(z)` lies in `[1, ∞)` only for `z ∈ [-1, 1]`. -/
theorem one_sub_inv_sq_mem_slitPlane_iff {z : ℂ} :
    1 - (z ^ 2)⁻¹ ∈ slitPlane ↔ z ∉ ofReal '' (Icc (-1) 1 \ {0}) := by
  rw [TauCeti.one_sub_inv_mem_slitPlane_iff]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨t, ⟨ht₀, ht₁⟩, ht⟩
    have hre : z.re ^ 2 - z.im ^ 2 = t := by
      have := congrArg re ht
      simp only [ofReal_re, sq, mul_re] at this
      nlinarith
    have him : z.re * z.im = 0 := by
      have := congrArg im ht
      simp only [ofReal_im, sq, mul_im] at this
      linarith
    have hy : z.im = 0 := by
      rcases mul_eq_zero.1 him with h | h
      · nlinarith [sq_nonneg z.im]
      · exact h
    have hx : z.re ≠ 0 := by
      rintro h
      rw [h, hy] at hre
      linarith
    refine ⟨z.re, ⟨⟨?_, ?_⟩, hx⟩, ext rfl (by simp [hy])⟩ <;> nlinarith [sq_nonneg (z.re + 1)]
  · rintro ⟨x, ⟨⟨hx₁, hx₂⟩, hx₀⟩, rfl⟩
    have hx₀' : x ≠ 0 := hx₀
    refine ⟨x ^ 2, ⟨by positivity, by nlinarith⟩, by push_cast; ring⟩

/-- On the cut plane `ℂ \ (-∞, 1]`, the argument `z⁻²` of the hypergeometric function in `𝑸^μ_ν(z)`
lies in its cut plane: `1 - z⁻² ∈ slitPlane`. -/
theorem one_sub_inv_sq_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    1 - (z ^ 2)⁻¹ ∈ slitPlane := by
  rw [one_sub_inv_sq_mem_slitPlane_iff]
  rintro ⟨x, ⟨⟨-, hx⟩, -⟩, rfl⟩
  rw [← ofReal_one, ← ofReal_sub, ofReal_mem_slitPlane] at hz
  linarith

/-- The cut plane `ℂ \ (-∞, 1]` is open. -/
theorem isOpen_setOf_sub_one_mem_slitPlane : IsOpen {z : ℂ | z - 1 ∈ slitPlane} :=
  isOpen_slitPlane.preimage (continuous_id.sub continuous_const)

/-- The cut plane `ℂ \ (-∞, 1]` is star-convex about `2`. -/
theorem starConvex_two_setOf_sub_one_mem_slitPlane :
    StarConvex ℝ (2 : ℂ) {z : ℂ | z - 1 ∈ slitPlane} := by
  have h₁ : StarConvex ℝ ((-1 : ℂ) + 2) slitPlane := by
    norm_num
    exact starConvex_one_slitPlane
  convert h₁.preimage_add_right using 1
  ext z
  simp [neg_add_eq_sub]

/-- The cut plane `ℂ \ (-∞, 1]` is connected. -/
theorem isConnected_setOf_sub_one_mem_slitPlane : IsConnected {z : ℂ | z - 1 ∈ slitPlane} :=
  (starConvex_two_setOf_sub_one_mem_slitPlane.isPathConnected (by norm_num)).isConnected

/-- On the cut plane `ℂ \ (-∞, 1]`, `log ((z + 1) / (z - 1)) = log (z + 1) - log (z - 1)`. -/
theorem log_add_one_div_sub_one {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    log ((z + 1) / (z - 1)) = log (z + 1) - log (z - 1) := by
  refine ContinuousOn.eqOn_of_eqOn_exp_comp (L₁ := fun w => log ((w + 1) / (w - 1)))
    (L₂ := fun w => log (w + 1) - log (w - 1))
    (hs := isConnected_setOf_sub_one_mem_slitPlane.isPreconnected)
    (fun w hw => (ContinuousAt.clog
      ((continuousAt_id.add continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (slitPlane_ne_zero hw)) (add_one_div_sub_one_mem_slitPlane hw)).continuousWithinAt)
    (fun w hw => ((ContinuousAt.clog (f := fun t => t + 1) (by fun_prop)
      (add_one_mem_slitPlane_of_sub_one_mem_slitPlane hw)).sub
      (ContinuousAt.clog (f := fun t => t - 1) (by fun_prop) hw)).continuousWithinAt)
    (fun w hw => ?_) (x₀ := 2) (by norm_num) (by norm_num) hz
  simp only [Function.comp_apply]
  rw [exp_sub, exp_log (slitPlane_ne_zero (add_one_div_sub_one_mem_slitPlane hw)),
    exp_log (slitPlane_ne_zero (add_one_mem_slitPlane_of_sub_one_mem_slitPlane hw)),
    exp_log (slitPlane_ne_zero hw)]

/-- On the cut plane `ℂ \ (-∞, 1]`, the principal power of `(z + 1) / (z - 1)` splits:
`((z + 1) / (z - 1))^s = (z + 1)^s (z - 1)^(-s)`. -/
theorem add_one_div_sub_one_cpow {z : ℂ} (hz : z - 1 ∈ slitPlane) (s : ℂ) :
    ((z + 1) / (z - 1)) ^ s = (z + 1) ^ s * (z - 1) ^ (-s) := by
  rw [cpow_def_of_ne_zero (slitPlane_ne_zero (add_one_div_sub_one_mem_slitPlane hz)),
    cpow_def_of_ne_zero (slitPlane_ne_zero (add_one_mem_slitPlane_of_sub_one_mem_slitPlane hz)),
    cpow_def_of_ne_zero (slitPlane_ne_zero hz), log_add_one_div_sub_one hz, ← exp_add]
  ring_nf

/-- On the part `{z | z - 1 ∈ slitPlane ∧ 0 < re z}` of the cut plane in the right half-plane,
`log (z² - 1) = log (z - 1) + log (z + 1)`: that part is star-convex about `2`, and `z² - 1` lies
in the slit plane there. -/
private theorem log_sq_sub_one_of_sub_one_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane)
    (hre : 0 < z.re) : log (z ^ 2 - 1) = log (z - 1) + log (z + 1) := by
  set W := {z : ℂ | z - 1 ∈ slitPlane} ∩ {z : ℂ | 0 < z.re}
  have hW : IsPreconnected W :=
    (starConvex_two_setOf_sub_one_mem_slitPlane.inter
      ((convex_halfSpace_re_gt 0).starConvex (by simp))).isPathConnected
      ⟨by norm_num, by simp⟩ |>.isConnected.isPreconnected
  -- `z² - 1` lies in the slit plane on `W`
  have hsq : ∀ w ∈ W, w ^ 2 - 1 ∈ slitPlane := by
    rintro w ⟨hw, hw'⟩
    have hw'' : w - 1 ∈ slitPlane := hw
    have hw''' : 0 < w.re := hw'
    rw [mem_slitPlane_iff] at hw'' ⊢
    simp only [sub_re, one_re, sub_im, one_im, sub_zero, sq, mul_re, mul_im] at hw'' ⊢
    by_cases hy : w.im = 0
    · left
      simp only [hy, ne_eq, not_true_eq_false, or_false] at hw''
      nlinarith
    · right
      have := mul_ne_zero hw'''.ne' hy
      intro h'
      exact this (by linarith)
  refine ContinuousOn.eqOn_of_eqOn_exp_comp (L₁ := fun w => log (w ^ 2 - 1))
    (L₂ := fun w => log (w - 1) + log (w + 1)) (hs := hW)
    (fun w hw => (ContinuousAt.clog (f := fun t => t ^ 2 - 1) (by fun_prop)
      (hsq w hw)).continuousWithinAt)
    (fun w hw => ((ContinuousAt.clog (f := fun t => t - 1) (by fun_prop) hw.1).add
      (ContinuousAt.clog (f := fun t => t + 1) (by fun_prop)
        (add_one_mem_slitPlane_of_sub_one_mem_slitPlane hw.1))).continuousWithinAt)
    (fun w hw => ?_) (x₀ := 2) ⟨by norm_num, by simp⟩ (by norm_num) ⟨hz, hre⟩
  simp only [Function.comp_apply]
  rw [exp_add, exp_log (slitPlane_ne_zero (hsq w hw)), exp_log (slitPlane_ne_zero hw.1),
    exp_log (slitPlane_ne_zero (add_one_mem_slitPlane_of_sub_one_mem_slitPlane hw.1))]
  ring

/-- In the right half-plane the arguments of `z - 1` and `z + 1` add up to a value in the principal
range `(-π, π]`. -/
theorem arg_sub_one_add_arg_add_one_mem_Ioc {z : ℂ} (hre : 0 < z.re) :
    arg (z - 1) + arg (z + 1) ∈ Ioc (-Real.pi) Real.pi := by
  by_cases hz : z - 1 ∈ slitPlane
  · have h := congrArg im (log_sq_sub_one_of_sub_one_mem_slitPlane hz hre)
    rw [add_im, log_im, log_im, log_im] at h
    exact h ▸ arg_mem_Ioc _
  · have him : z.im = 0 := by simpa using im_eq_zero_of_notMem_slitPlane hz
    have harg : arg (z + 1) = 0 := arg_eq_zero_iff.2 ⟨by simp; linarith, by simp [him]⟩
    rw [harg, add_zero]
    exact arg_mem_Ioc _

/-- In the right half-plane, `log (z² - 1) = log (z - 1) + log (z + 1)` for `z ≠ 1`. -/
theorem log_sq_sub_one {z : ℂ} (hre : 0 < z.re) (hz : z ≠ 1) :
    log (z ^ 2 - 1) = log (z - 1) + log (z + 1) := by
  have h₁ : z + 1 ≠ 0 := fun h => by
    have := congrArg re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring]
  exact log_mul (sub_ne_zero.2 hz) h₁ (arg_sub_one_add_arg_add_one_mem_Ioc hre)

/-- In the right half-plane the product `(z - 1)^s (z + 1)^s` is the principal power of
`z² - 1`. -/
theorem sq_sub_one_cpow {z : ℂ} (hre : 0 < z.re) (s : ℂ) :
    (z ^ 2 - 1) ^ s = (z - 1) ^ s * (z + 1) ^ s := by
  rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring]
  exact TauCeti.mul_cpow_of_arg_add_mem (arg_sub_one_add_arg_add_one_mem_Ioc hre) s

/-- On `[1, ∞)` the product `(x - 1)^s (x + 1)^s` is the principal real power `(x² - 1)^s`. -/
theorem ofReal_sub_one_cpow_mul_ofReal_add_one_cpow {x : ℝ} (hx : 1 ≤ x) (s : ℝ) :
    ((x : ℂ) - 1) ^ (s : ℂ) * ((x : ℂ) + 1) ^ (s : ℂ) = (((x ^ 2 - 1) ^ s : ℝ) : ℂ) := by
  rw [← sq_sub_one_cpow (by simp; linarith), ofReal_cpow (by nlinarith)]
  norm_cast

/-- `z ↦ ((z + 1) / (z - 1))^s` is holomorphic on the cut plane `ℂ \ (-∞, 1]`. -/
theorem differentiableOn_add_one_div_sub_one_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => ((z + 1) / (z - 1)) ^ s) {z | z - 1 ∈ slitPlane} := by
  refine DifferentiableOn.cpow_const ?_ fun z hz => add_one_div_sub_one_mem_slitPlane hz
  exact (differentiableOn_id.add (differentiableOn_const 1)).div
    (differentiableOn_id.sub (differentiableOn_const 1)) fun z hz => slitPlane_ne_zero hz

/-- `z ↦ (z - 1)^s (z + 1)^s` is holomorphic on the cut plane `ℂ \ (-∞, 1]`. -/
theorem differentiableOn_sub_one_cpow_mul_add_one_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ s * (z + 1) ^ s) {z | z - 1 ∈ slitPlane} :=
  ((differentiableOn_id.sub (differentiableOn_const 1)).cpow_const fun _ hz => hz).mul
    ((differentiableOn_id.add (differentiableOn_const 1)).cpow_const
      fun _ hz => add_one_mem_slitPlane_of_sub_one_mem_slitPlane hz)

end Complex
