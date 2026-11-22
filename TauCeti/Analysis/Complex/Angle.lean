/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle

/-!
# The angle between `a` and `a * w`, and a rotation identity

For a nonzero complex number `a`, the unoriented angle between `a` and `a * w` is
`arccos (Re w / |w|)` (`Complex.angle_self_mul_right`); for `w` in the open upper half-plane this
is the argument of `w`. The file also records two rotation identities for `exp (-θ I)`: the
rotation of a real multiple of `exp (θ I)` (`Complex.im_exp_neg_mul_mul_ofReal_mul_exp`), and the
height of a horizontal step (`Complex.im_exp_neg_mul_mul_sub`).

## Main results

* `Complex.angle_self_mul_right`: `angle a (a * w) = arccos (w.re / ‖w‖)` for `a ≠ 0`.
* `Complex.im_exp_neg_mul_mul_ofReal_mul_exp`: `(exp (-θ I) * (r * exp (θ I))).im = 0`.
* `Complex.im_exp_neg_mul_mul_sub`: the height of a horizontal step `y - x` (`x.im = y.im`) rotated
  by `exp (-θ * I)` is its signed length `(y - x).re` times `sin (-θ)`.
* `Real.eq_two_mul_cos_pi_div_of_norm_one_add_sq_div_le`: if `exp (arccos (λ / 2) * I) ^ 2` is an
  `h`-th root of unity and `‖(1 + exp (2πi / h)) ^ 2 / exp (2πi / h)‖ ≤ λ ^ 2` for
  `0 ≤ λ < 2`, then `λ = 2 * cos (π / h)`.
-/

public section

namespace Complex

/-- For `a ≠ 0`, the angle between `a` and `a * w` is `arccos (Re w / |w|)`; for `w` in the upper
half-plane this is the argument of `w`. -/
theorem angle_self_mul_right {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    InnerProductGeometry.angle a (a * w) = Real.arccos (w.re / ‖w‖) := by
  simpa [InnerProductGeometry.angle] using angle_mul_left ha 1 w

/-- Rotating a real multiple of `exp (θ I)` by `exp (-θ I)` gives a real number. -/
theorem im_exp_neg_mul_mul_ofReal_mul_exp (θ r : ℝ) :
    (Complex.exp (-θ * Complex.I) * ((r : ℂ) * Complex.exp (θ * Complex.I))).im = 0 := by
  rw [mul_left_comm, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one,
    Complex.ofReal_im]

/-- **A horizontal step, rotated by `-θ`, has height `r * sin (-θ)`.**  If `x` and `y` have the same
imaginary part, then after multiplying `y - x` by `exp (-θ * I)` its imaginary part is the signed
length `(y - x).re` times `sin (-θ)`. -/
lemma im_exp_neg_mul_mul_sub (θ : ℝ) {x y : ℂ} (hxy : x.im = y.im) :
    (Complex.exp (-θ * Complex.I) * (y - x)).im = (y - x).re * Real.sin (-θ) := by
  have hu : (Complex.exp (-θ * Complex.I)).im = Real.sin (-θ) := by
    have h := Complex.exp_ofReal_mul_I_im (-θ)
    push_cast at h
    exact h
  simp only [Complex.mul_im, Complex.sub_im, hxy, hu, sub_self, mul_zero, zero_add]
  ring

end Complex

namespace Real

/-- If `λ ∈ [0, 2)` satisfies `(exp (arccos (λ / 2) * I) ^ 2) ^ h = 1` for `2 ≤ h` and
`‖(1 + exp (2πi / h)) ^ 2 / exp (2πi / h)‖ ≤ λ ^ 2`, then `λ = 2 * cos (π / h)`. -/
theorem eq_two_mul_cos_pi_div_of_norm_one_add_sq_div_le {lam : ℝ} {h : ℕ}
    (hlam_nonneg : 0 ≤ lam) (hlam_lt : lam < 2) (h2le : 2 ≤ h)
    (hζ_pow : (Complex.exp ((arccos (lam / 2) : ℂ) * Complex.I) ^ 2) ^ h = 1)
    (hbound : ‖(1 + Complex.exp (2 * π * Complex.I / h)) ^ 2 /
      Complex.exp (2 * π * Complex.I / h)‖ ≤ lam ^ 2) :
    lam = 2 * cos (π / h) := by
  set θ : ℝ := arccos (lam / 2)
  have hcosθ : cos θ = lam / 2 := cos_arccos (by linarith) (by linarith)
  have hθ_pos : 0 < θ := by
    rw [← arccos_one]
    exact arccos_lt_arccos (by linarith) (by linarith) le_rfl
  have hθ_le : θ ≤ π / 2 := by
    rw [← arccos_zero]
    exact arccos_le_arccos (by linarith : (0 : ℝ) ≤ lam / 2)
  set ω₀ : ℂ := Complex.exp (2 * π * Complex.I / h)
  have hval_ω₀ : (1 + ω₀) ^ 2 / ω₀ = (((2 * cos (π / h)) ^ 2 : ℝ) : ℂ) := by
    set ξ : ℂ := Complex.exp (((π / h : ℝ) : ℂ) * Complex.I)
    rw [show ω₀ = ξ ^ 2 by
        simp only [ω₀, ξ, sq, ← Complex.exp_add]
        congr 1
        push_cast
        ring,
      show (1 + ξ ^ 2) ^ 2 / ξ ^ 2 = (ξ + ξ⁻¹) ^ 2 by
        field_simp [Complex.exp_ne_zero _]
        ring]
    dsimp only [ξ]
    rw [← Complex.exp_neg, ← neg_mul, ← Complex.two_cos]
    push_cast
    ring
  rw [hval_ω₀, Complex.norm_real, norm_of_nonneg (sq_nonneg _)] at hbound
  have hh_pos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hpi_le_θ : π / h ≤ θ := by
    have hexp1 : Complex.exp (((2 * (h : ℝ) * θ : ℝ) : ℂ) * Complex.I) = 1 := by
      simp only [← Complex.exp_natCast_mul] at hζ_pow
      convert hζ_pow using 2
      push_cast
      ring
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
    have hre : 2 * (h : ℝ) * θ = (m : ℝ) * (2 * π) := Complex.ofReal_injective
      (mul_right_cancel₀ Complex.I_ne_zero (by simpa [mul_assoc] using hm))
    have hm_pos : (0 : ℤ) < m := by
      exact_mod_cast (show (0 : ℝ) < m by nlinarith [pi_pos, mul_pos hh_pos hθ_pos])
    have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    rw [div_le_iff₀ hh_pos]
    nlinarith [pi_pos]
  have hcos_le : cos (π / h) ≤ cos θ := by
    have hcos_nonneg_pi : 0 ≤ cos (π / h) := by
      refine cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, div_nonneg pi_pos.le hh_pos.le], ?_⟩
      have h2 : (2 : ℝ) ≤ h := by exact_mod_cast h2le
      rw [div_le_div_iff₀ hh_pos (by norm_num)]
      nlinarith [pi_pos]
    have : cos (π / h) ^ 2 ≤ cos θ ^ 2 := by
      rw [show lam = 2 * cos θ by linarith] at hbound
      nlinarith
    nlinarith
  have hcos_ge : cos θ ≤ cos (π / h) := strictAntiOn_cos.antitoneOn
    ⟨by positivity, le_trans hpi_le_θ (le_trans hθ_le (by linarith [pi_pos]))⟩
    ⟨hθ_pos.le, le_trans hθ_le (by linarith [pi_pos])⟩ hpi_le_θ
  linarith [le_antisymm hcos_ge hcos_le]

end Real
