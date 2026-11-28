/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Bounds for the Barnes kernels of the parabolic cylinder functions

The Barnes integrals DLMF 12.5.8–12.5.9 of `U(a, z)` and `V(a, z)` integrate the kernel
`Γ(t) Γ(A - 2t) 2^t z^(2t)`, with `A = a + 1/2` (respectively `A = 1/2 - a`, with an extra factor
`cos (π t)`), over a vertical line `Re t = c` (`c > 0` in DLMF) that avoids the poles of `Γ(t)`
and the poles `t = (A + n) / 2` of `Γ(A - 2t)`. On such a line the kernel is bounded by
`C (1 + |y|)^K exp (-κ |y|)` at `t = c + iy`, with `κ = 3π/2 - 2|arg z|`: the two Gamma factors
decay like `exp (-π|y|/2)` and `exp (-π|y|)` up to powers of `|y|`, and
`|2^t z^(2t)| = 2^c |z|^(2c) exp (-2y arg z)`. The factor `cos (π t)` grows like `exp (π|y|)`
and lowers the rate to `π/2 - 2|arg z|`. The same bounds hold for `|y| ≥ T₀` uniformly on every
compact strip `c₁ ≤ Re t ≤ c₂`, poles or not. When the rate is positive, that is for
`|arg z| < 3π/4` (respectively `|arg z| < π/4`), the kernels are integrable on admissible lines,
and the horizontal connectors of every strip tend to zero; these are the integrability and
connector hypotheses of the vertical line shift
`TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue`. At a pole `t = (A + n) / 2`
of `Γ(A - 2t)` that is not a pole of `Γ(t)`, that is when `(A + n) / 2` is not a nonpositive
integer, the kernel has the residue of `Complex.tendsto_sub_mul_Gamma_sub_two_mul` times the
regular factor `Γ(t) 2^t z^(2t)`; where the two poles collide the kernel can have a double pole.

## Main results

* `Complex.norm_two_cpow_mul_cpow_two_mul`: `‖2^t z^(2t)‖ = 2^c ‖z‖^(2c) exp (-2y arg z)` at
  `t = c + iy`.
* `TauCeti.exists_norm_barnes_kernel_le`: the bound with `κ = 3π/2 - 2|arg z|` on an admissible
  line, and `TauCeti.exists_norm_barnes_kernel_mul_cos_le`: the bound with `κ = π/2 - 2|arg z|`
  for the kernel times `cos (π t)`.
* `Complex.exists_norm_barnes_kernel_le_of_mem_Icc`,
  `Complex.exists_norm_barnes_kernel_mul_cos_le_of_mem_Icc`: the same tail bounds for `|y| ≥ T₀`,
  uniformly for `Re t` in a compact interval `[c₁, c₂]`.
* `Complex.integrable_barnes_kernel`, `Complex.integrable_barnes_kernel_mul_cos`: integrability on
  admissible lines.
* `Complex.tendsto_intervalIntegral_barnes_kernel`,
  `Complex.tendsto_intervalIntegral_barnes_kernel_mul_cos`: the horizontal connectors vanish.
* `Complex.tendsto_sub_mul_barnes_kernel`: the residue
  `(-1)^(n+1) Γ((A + n)/2) 2^((A + n)/2) z^(A + n) / (2 n!)` of the kernel at `t = (A + n) / 2`,
  when `(A + n) / 2` is not a nonpositive integer.

## References

The bounds follow the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ParabolicCylinder/BarnesContinuation.lean` (`CylinderBarnesContinuation.norm_integrand_le`,
`integrand_integrable`, `integrand_horizontal`, `removableIntegrand_pole`), with its Gamma bounds
replaced by Tau Ceti's Stirling bounds on vertical strips
(`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Vertical.lean`).
-/

public section

open Complex Filter Set MeasureTheory TauCeti
open scoped Real Topology Interval Nat

namespace Complex

/-- **The power factor of the Barnes kernel.** For `z ≠ 0` and `t = x + iy`,
`‖2^t z^(2t)‖ = 2^x ‖z‖^(2x) exp (-2y arg z)`; this is the source of the term `2|arg z|` in the
decay rates of the Barnes kernels. -/
theorem norm_two_cpow_mul_cpow_two_mul {z : ℂ} (hz : z ≠ 0) (x y : ℝ) :
    ‖(2 : ℂ) ^ ((x : ℂ) + y * I) * z ^ (2 * ((x : ℂ) + y * I))‖ =
      2 ^ x * ‖z‖ ^ (2 * x) * Real.exp (-(2 * y * arg z)) := by
  have h2 := norm_cpow_eq_rpow_re_of_pos two_pos ((x : ℂ) + y * I)
  push_cast at h2
  rw [norm_mul, h2, norm_cpow_of_ne_zero hz, Real.exp_neg]
  simp [div_eq_mul_inv, mul_comm (arg z), mul_assoc]

/-- The bound `‖2^t z^(2t)‖ ≤ 2^x ‖z‖^(2x) exp (2|arg z| |y|)` at `t = x + iy`, for every `z`. -/
theorem norm_two_cpow_mul_cpow_two_mul_le (z : ℂ) (x y : ℝ) :
    ‖(2 : ℂ) ^ ((x : ℂ) + y * I) * z ^ (2 * ((x : ℂ) + y * I))‖ ≤
      2 ^ x * ‖z‖ ^ (2 * x) * Real.exp (2 * |arg z| * |y|) := by
  rcases eq_or_ne z 0 with rfl | hz
  · by_cases h : (2 : ℂ) * ((x : ℂ) + y * I) = 0
    · have hx : x = 0 := by simpa using congrArg re h
      have hy : y = 0 := by simpa using congrArg im h
      simp [hx, hy]
    · rw [zero_cpow h, mul_zero, norm_zero]
      positivity
  · rw [norm_two_cpow_mul_cpow_two_mul hz]
    have h := neg_le_abs (y * arg z)
    rw [abs_mul] at h
    gcongr
    linarith

/-- **The Barnes kernel bound from bounds on its two Gamma factors.** If at `t = x + iy`,
`‖Γ(t)‖ ≤ C₁ (1 + |y|)^K₁ exp (-π|y|/2)` and `‖Γ(A - 2t)‖ ≤ C₂ (1 + |y|)^K₂ exp (-π|y|)`, then
`‖Γ(t) Γ(A - 2t) 2^t z^(2t)‖ ≤ C₁ C₂ 2^x ‖z‖^(2x) (1 + |y|)^(K₁ + K₂) exp (-κ|y|)` with
`κ = 3π/2 - 2|arg z|`. -/
theorem norm_barnes_kernel_le_of_norm_Gamma_le (A z : ℂ) {x y C₁ C₂ : ℝ} {K₁ K₂ : ℕ}
    (h₁ : ‖Gamma (x + y * I)‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2))
    (h₂ : ‖Gamma (A - 2 * (x + y * I))‖ ≤ C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|))) :
    ‖Gamma (x + y * I) * Gamma (A - 2 * (x + y * I)) * 2 ^ ((x : ℂ) + y * I) *
        z ^ (2 * ((x : ℂ) + y * I))‖ ≤
      C₁ * C₂ * 2 ^ x * ‖z‖ ^ (2 * x) * (1 + |y|) ^ (K₁ + K₂) *
        Real.exp (-(3 * π / 2 - 2 * |arg z|) * |y|) := by
  rw [mul_assoc _ ((2 : ℂ) ^ _), norm_mul, norm_mul]
  have hC₁ := (norm_nonneg _).trans h₁
  calc _ ≤ (C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) *
        (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|))) *
        (2 ^ x * ‖z‖ ^ (2 * x) * Real.exp (2 * |arg z| * |y|)) :=
      mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) hC₁)
        (norm_two_cpow_mul_cpow_two_mul_le z x y) (norm_nonneg _)
        (mul_nonneg hC₁ ((norm_nonneg _).trans h₂))
    _ = _ := by
      have he : -(3 * π / 2 - 2 * |arg z|) * |y| =
          -(π * |y|) / 2 + -(π * |y|) + 2 * |arg z| * |y| := by ring
      rw [pow_add, he, Real.exp_add, Real.exp_add]
      ring

end Complex

namespace TauCeti

/-- **The Barnes kernel of `U` on a vertical line.** On a line `Re t = c` avoiding the poles
of `Γ(t)` and the poles `t = (A + n) / 2` of `Γ(A - 2t)`,
`‖Γ(t) Γ(A - 2t) 2^t z^(2t)‖ ≤ C (1 + |y|)^K exp (-(3π/2 - 2|arg z|) |y|)` at `t = c + iy`. -/
theorem exists_norm_barnes_kernel_le (A z : ℂ) {c : ℝ} (hc : ∀ n : ℕ, c ≠ -n)
    (havoid : ∀ n : ℕ, 2 * c ≠ A.re + n) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ y : ℝ,
      ‖Gamma ((c : ℂ) + y * I) * Gamma (A - 2 * ((c : ℂ) + y * I)) * 2 ^ ((c : ℂ) + y * I) *
          z ^ (2 * ((c : ℂ) + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(3 * π / 2 - 2 * |arg z|) * |y|) := by
  -- Stirling's bounds for `Γ(t)` and for `Γ(A - 2t) = Γ((A - 2c) - 2iy)` on the two lines.
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_Gamma_add_I_le (w := (c : ℂ)) (by simpa using hc)
  have hΓ₁ (y : ℝ) : ‖Gamma ((c : ℂ) + y * I)‖ ≤
      C₁ * (1 + |y|) ^ ⌈c - 1 / 2⌉₊ * Real.exp (-(π * |y|) / 2) := by
    refine (h₁ y).trans ?_
    rw [ofReal_re, neg_div]
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y])
      (Nat.le_ceil _)).trans_eq (Real.rpow_natCast _ _)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_Gamma_sub_I_le (w := A - 2 * c) fun n hn ↦
    havoid n (by simp at hn; linarith)
  set p := (A - 2 * (c : ℂ)).re - 1 / 2
  have hΓ (y : ℝ) : ‖Gamma (A - 2 * ((c : ℂ) + y * I))‖ ≤
      C₂ * 2 ^ ⌈p⌉₊ * (1 + |y|) ^ ⌈p⌉₊ * Real.exp (-(π * |y|)) := by
    have hy := h₂ (2 * y)
    have harg : A - 2 * c - ((2 * y : ℝ) : ℂ) * I = A - 2 * ((c : ℂ) + y * I) := by
      push_cast
      ring
    have hexp : π * (2 * |y|) / 2 = π * |y| := by ring
    rw [harg, abs_mul, abs_two, hexp] at hy
    calc _ ≤ C₂ * (2 * (1 + |y|)) ^ (⌈p⌉₊ : ℝ) * Real.exp (-(π * |y|)) := by
          refine hy.trans ?_
          gcongr
          exact (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y])
            (Nat.le_ceil p)).trans (by gcongr; linarith)
      _ = _ := by rw [Real.rpow_natCast, mul_pow]; ring
  refine ⟨C₁ * (C₂ * 2 ^ ⌈p⌉₊) * 2 ^ c * (‖z‖ ^ (2 * c) + 1), by positivity,
    ⌈c - 1 / 2⌉₊ + ⌈p⌉₊, fun y ↦
      (norm_barnes_kernel_le_of_norm_Gamma_le A z (hΓ₁ y) (hΓ y)).trans ?_⟩
  gcongr
  linarith

/-- **The Barnes kernel of `V` on a vertical line.** The factor `cos (π t)` lowers the decay
rate of `TauCeti.exists_norm_barnes_kernel_le` by `π`: at `t = c + iy`,
`‖Γ(t) Γ(A - 2t) 2^t z^(2t) cos (π t)‖ ≤ C (1 + |y|)^K exp (-(π/2 - 2|arg z|) |y|)`. -/
theorem exists_norm_barnes_kernel_mul_cos_le (A z : ℂ) {c : ℝ} (hc : ∀ n : ℕ, c ≠ -n)
    (havoid : ∀ n : ℕ, 2 * c ≠ A.re + n) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ y : ℝ,
      ‖Gamma ((c : ℂ) + y * I) * Gamma (A - 2 * ((c : ℂ) + y * I)) * 2 ^ ((c : ℂ) + y * I) *
          z ^ (2 * ((c : ℂ) + y * I)) * cos (π * ((c : ℂ) + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(π / 2 - 2 * |arg z|) * |y|) := by
  obtain ⟨C, hC, K, h⟩ := exists_norm_barnes_kernel_le A z hc havoid
  refine ⟨C, hC, K, fun y ↦ ?_⟩
  have hcos : ‖cos (π * ((c : ℂ) + y * I))‖ ≤ Real.exp (π * |y|) := by
    simpa [abs_mul, abs_of_pos Real.pi_pos] using norm_cos_le_exp_abs_im (π * ((c : ℂ) + y * I))
  rw [norm_mul]
  calc _ ≤ C * (1 + |y|) ^ K * Real.exp (-(3 * π / 2 - 2 * |arg z|) * |y|) *
        Real.exp (π * |y|) := mul_le_mul (h y) hcos (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

end TauCeti

namespace Complex

/-- Stirling's tail bound for the second Gamma factor of the Barnes kernel on a strip: there are
`D`, `K` and `T₀` such that `‖Γ(A - 2(x + iy))‖ ≤ D (1 + |y|)^K exp (-π|y|)` for `x ∈ [c₁, c₂]`
and `|y| ≥ T₀`. This is `TauCeti.exists_norm_Gamma_add_vertical_strip_le` at `-2x` and `-2y`. -/
private theorem exists_norm_Gamma_sub_two_mul_le_of_mem_Icc (A : ℂ) (c₁ c₂ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∃ K : ℕ, ∃ T₀ : ℝ, ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ, T₀ ≤ |y| →
      ‖Gamma (A - 2 * ((x : ℂ) + y * I))‖ ≤ D * (1 + |y|) ^ K * Real.exp (-(π * |y|)) := by
  obtain ⟨C, hC, K, T₀, h⟩ := exists_norm_Gamma_add_vertical_strip_le A (-2 * c₂) (-2 * c₁)
  refine ⟨(C + 1) * 2 ^ ⌈K⌉₊, by positivity, ⌈K⌉₊, T₀ / 2, fun x hx y hy ↦ ?_⟩
  have hx' : -2 * x ∈ Icc (-2 * c₂) (-2 * c₁) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have habs : |-2 * y| = 2 * |y| := by rw [abs_mul, abs_neg, abs_two]
  have harg : A + (((-2 * x : ℝ) : ℂ) + ((-2 * y : ℝ) : ℂ) * I) = A - 2 * ((x : ℂ) + y * I) := by
    push_cast
    ring
  have hexp : -(π * (2 * |y|) / 2) = -(π * |y|) := by ring
  have hb := h (-2 * x) hx' (-2 * y) (by rw [habs]; linarith)
  rw [harg, habs, hexp] at hb
  -- `(1 + 2|y|)^K ≤ (2 (1 + |y|))^⌈K⌉₊ = 2^⌈K⌉₊ (1 + |y|)^⌈K⌉₊`
  have hpow : (1 + 2 * |y|) ^ K ≤ 2 ^ ⌈K⌉₊ * (1 + |y|) ^ ⌈K⌉₊ := by
    rw [← mul_pow, ← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil K)).trans
      (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity))
  have hC1 : C ≤ C + 1 := by linarith
  calc _ ≤ C * (1 + 2 * |y|) ^ K * Real.exp (-(π * |y|)) := hb
    _ ≤ (C + 1) * (2 ^ ⌈K⌉₊ * (1 + |y|) ^ ⌈K⌉₊) * Real.exp (-(π * |y|)) := by gcongr
    _ = _ := by ring

/-- **Tail bound for the Barnes kernel of `U`, uniform on a strip.** There are `C`, `K` and
`T₀` such that at `t = x + iy`,
`‖Γ(t) Γ(A - 2t) 2^t z^(2t)‖ ≤ C (1 + |y|)^K exp (-(3π/2 - 2|arg z|) |y|)` for all `x ∈ [c₁, c₂]`
and `|y| ≥ T₀`. -/
theorem exists_norm_barnes_kernel_le_of_mem_Icc (A z : ℂ) (c₁ c₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∃ T₀ : ℝ, ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ, T₀ ≤ |y| →
      ‖Gamma ((x : ℂ) + y * I) * Gamma (A - 2 * ((x : ℂ) + y * I)) * 2 ^ ((x : ℂ) + y * I) *
          z ^ (2 * ((x : ℂ) + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(3 * π / 2 - 2 * |arg z|) * |y|) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_Gamma_vertical_strip_le c₁ c₂ one_pos
  set K₁ := ⌈c₂ - 1 / 2⌉₊
  -- Stirling's bound for `Γ(t)`, once `|y| ≥ 1`.
  have hΓ₁ : ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ, 1 ≤ |y| →
      ‖Gamma ((x : ℂ) + y * I)‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2) := by
    intro x hx y hy
    refine (h₁ _ (by simpa using hx) (by simpa using hy)).trans ?_
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, neg_div]
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y])
      (by linarith [hx.2, Nat.le_ceil (c₂ - 1 / 2)])).trans_eq (Real.rpow_natCast _ _)
  obtain ⟨D, hD, K₂, T₂, hΓ⟩ := exists_norm_Gamma_sub_two_mul_le_of_mem_Icc A c₁ c₂
  -- On `[c₁, c₂]`, `2^x ≤ 2^c₂` and `‖z‖^(2x) ≤ ‖z‖^(2c₁) + ‖z‖^(2c₂) + 1`.
  have hz : ∀ x ∈ Icc c₁ c₂, ‖z‖ ^ (2 * x) ≤ ‖z‖ ^ (2 * c₁) + ‖z‖ ^ (2 * c₂) + 1 := by
    intro x hx
    have h₁ := Real.rpow_nonneg (norm_nonneg z) (2 * c₁)
    have h₂ := Real.rpow_nonneg (norm_nonneg z) (2 * c₂)
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [norm_zero] at h₁ h₂ ⊢
      linarith [Real.zero_rpow_le_one (2 * x)]
    rcases le_total 1 ‖z‖ with h | h
    · have hx₂ : 2 * x ≤ 2 * c₂ := by linarith [hx.2]
      linarith [Real.rpow_le_rpow_of_exponent_le h hx₂]
    · have hx₁ : 2 * c₁ ≤ 2 * x := by linarith [hx.1]
      linarith [Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hz0) h hx₁]
  refine ⟨C₁ * D * 2 ^ c₂ * (‖z‖ ^ (2 * c₁) + ‖z‖ ^ (2 * c₂) + 1), by positivity, K₁ + K₂,
    max 1 T₂, fun x hx y hy ↦ (norm_barnes_kernel_le_of_norm_Gamma_le A z
      (hΓ₁ x hx y (le_of_max_le_left hy)) (hΓ x hx y (le_of_max_le_right hy))).trans ?_⟩
  gcongr
  · norm_num
  · exact hx.2
  · exact hz x hx

/-- **Tail bound for the Barnes kernel of `V`, uniform on a strip.** The cosine factor
lowers the rate of `Complex.exists_norm_barnes_kernel_le_of_mem_Icc` by `π`. -/
theorem exists_norm_barnes_kernel_mul_cos_le_of_mem_Icc (A z : ℂ) (c₁ c₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∃ T₀ : ℝ, ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ, T₀ ≤ |y| →
      ‖Gamma ((x : ℂ) + y * I) * Gamma (A - 2 * ((x : ℂ) + y * I)) * 2 ^ ((x : ℂ) + y * I) *
          z ^ (2 * ((x : ℂ) + y * I)) * cos (π * ((x : ℂ) + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(π / 2 - 2 * |arg z|) * |y|) := by
  obtain ⟨C, hC, K, T₀, h⟩ := exists_norm_barnes_kernel_le_of_mem_Icc A z c₁ c₂
  refine ⟨C, hC, K, T₀, fun x hx y hy ↦ ?_⟩
  have hcos : ‖cos (π * ((x : ℂ) + y * I))‖ ≤ Real.exp (π * |y|) := by
    simpa [abs_mul, abs_of_pos Real.pi_pos] using norm_cos_le_exp_abs_im (π * ((x : ℂ) + y * I))
  rw [norm_mul]
  calc _ ≤ C * (1 + |y|) ^ K * Real.exp (-(3 * π / 2 - 2 * |arg z|) * |y|) *
        Real.exp (π * |y|) := mul_le_mul (h x hx y hy) hcos (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-- The Barnes kernel `y ↦ Γ(t) Γ(A - 2t) 2^t z^(2t)`, `t = c + iy`, is continuous on every line
`Re t = c` that avoids the poles of `Γ(t)` and the poles `t = (A + n) / 2` of `Γ(A - 2t)`. -/
theorem continuous_barnes_kernel (A z : ℂ) {c : ℝ} (hc : ∀ n : ℕ, c ≠ -n)
    (havoid : ∀ n : ℕ, 2 * c ≠ A.re + n) :
    Continuous fun y : ℝ ↦ Gamma ((c : ℂ) + y * I) * Gamma (A - 2 * ((c : ℂ) + y * I)) *
      2 ^ ((c : ℂ) + y * I) * z ^ (2 * ((c : ℂ) + y * I)) := by
  have h₁ : Continuous fun y : ℝ ↦ Gamma ((c : ℂ) + y * I) :=
    continuous_Gamma_add_mul_I (by simpa using hc)
  have h₂ : Continuous fun y : ℝ ↦ Gamma (A - 2 * ((c : ℂ) + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (continuousAt_Gamma_of_re_ne_neg_nat fun n hn ↦ havoid n (by simp at hn; linarith)).comp
        (by fun_prop)
  have hne : ∀ y : ℝ, 2 * ((c : ℂ) + y * I) ≠ 0 := fun y h ↦ hc 0 (by simpa using congrArg re h)
  have h₃ : Continuous fun y : ℝ ↦ (2 : ℂ) ^ ((c : ℂ) + y * I) :=
    (by fun_prop : Continuous fun y : ℝ ↦ (c : ℂ) + y * I).const_cpow (.inl two_ne_zero)
  have h₄ : Continuous fun y : ℝ ↦ z ^ (2 * ((c : ℂ) + y * I)) :=
    (by fun_prop : Continuous fun y : ℝ ↦ 2 * ((c : ℂ) + y * I)).const_cpow (.inr hne)
  exact ((h₁.mul h₂).mul h₃).mul h₄

/-- For `|arg z| < 3π/4` the Barnes kernel of `U` is integrable on every line
`Re t = c` that avoids the poles of `Γ(t)` and of `Γ(A - 2t)`. -/
theorem integrable_barnes_kernel {A z : ℂ} (hz : |arg z| < 3 * π / 4) {c : ℝ}
    (hc : ∀ n : ℕ, c ≠ -n)
    (havoid : ∀ n : ℕ, 2 * c ≠ A.re + n) :
    Integrable fun y : ℝ ↦ Gamma ((c : ℂ) + y * I) * Gamma (A - 2 * ((c : ℂ) + y * I)) *
      2 ^ ((c : ℂ) + y * I) * z ^ (2 * ((c : ℂ) + y * I)) := by
  obtain ⟨C, -, K, h⟩ := TauCeti.exists_norm_barnes_kernel_le A z hc havoid
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs K
    (a := 3 * π / 2 - 2 * |arg z|) (by linarith)).const_mul C).mono'
    (continuous_barnes_kernel A z hc havoid).aestronglyMeasurable
    (.of_forall fun y ↦ (h y).trans_eq ?_)
  rw [Real.rpow_natCast, neg_mul]
  ring

/-- For `|arg z| < π/4` the Barnes kernel of `V` (with the factor `cos (π t)`) is
integrable on every line `Re t = c` that avoids the poles of `Γ(t)` and of `Γ(A - 2t)`. -/
theorem integrable_barnes_kernel_mul_cos {A z : ℂ} (hz : |arg z| < π / 4) {c : ℝ}
    (hc : ∀ n : ℕ, c ≠ -n)
    (havoid : ∀ n : ℕ, 2 * c ≠ A.re + n) :
    Integrable fun y : ℝ ↦ Gamma ((c : ℂ) + y * I) * Gamma (A - 2 * ((c : ℂ) + y * I)) *
      2 ^ ((c : ℂ) + y * I) * z ^ (2 * ((c : ℂ) + y * I)) * cos (π * ((c : ℂ) + y * I)) := by
  obtain ⟨C, -, K, h⟩ := TauCeti.exists_norm_barnes_kernel_mul_cos_le A z hc havoid
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs K
    (a := π / 2 - 2 * |arg z|) (by linarith)).const_mul C).mono'
    ((continuous_barnes_kernel A z hc havoid).mul (by fun_prop)).aestronglyMeasurable
    (.of_forall fun y ↦ (h y).trans_eq ?_)
  rw [Real.rpow_natCast, neg_mul]
  ring

/-- **Horizontal connectors for the Barnes kernel of `U`.** For `|arg z| < 3π/4`,
`∫ x in c₁..c₂, Γ(t) Γ(A - 2t) 2^t z^(2t)` at `t = x + iT` tends to `0` as
`|T| → ∞`, in particular along `atTop` and `atBot`. -/
theorem tendsto_intervalIntegral_barnes_kernel {A z : ℂ} (hz : |arg z| < 3 * π / 4) (c₁ c₂ : ℝ)
    {l : Filter ℝ} (hl : l ≤ cocompact ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x in c₁..c₂, Gamma ((x : ℂ) + T * I) *
      Gamma (A - 2 * ((x : ℂ) + T * I)) * 2 ^ ((x : ℂ) + T * I) * z ^ (2 * ((x : ℂ) + T * I)))
      l (𝓝 0) := by
  obtain ⟨C, -, K, T₀, h⟩ :=
    exists_norm_barnes_kernel_le_of_mem_Icc A z (c₁ ⊓ c₂) (c₁ ⊔ c₂)
  have hκ : 0 < 3 * π / 2 - 2 * |arg z| := by linarith
  refine TauCeti.intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le
    (by simpa using ((tendsto_one_add_abs_rpow_mul_exp_neg_mul_abs K hκ).mono_left hl).const_mul C)
    ?_
  filter_upwards [(tendsto_norm_cocompact_atTop.mono_left hl).eventually_ge_atTop T₀] with T hT
  refine .of_forall fun x hx ↦ (h x (uIoc_subset_uIcc hx) T hT).trans_eq ?_
  rw [neg_mul, mul_assoc]

/-- **Horizontal connectors for the Barnes kernel of `V`.** For `|arg z| < π/4`,
`∫ x in c₁..c₂, Γ(t) Γ(A - 2t) 2^t z^(2t) cos (π t)` at `t = x + iT` tends to `0` as
`|T| → ∞`, in particular along `atTop` and `atBot`. -/
theorem tendsto_intervalIntegral_barnes_kernel_mul_cos {A z : ℂ} (hz : |arg z| < π / 4)
    (c₁ c₂ : ℝ) {l : Filter ℝ} (hl : l ≤ cocompact ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x in c₁..c₂, Gamma ((x : ℂ) + T * I) *
      Gamma (A - 2 * ((x : ℂ) + T * I)) * 2 ^ ((x : ℂ) + T * I) * z ^ (2 * ((x : ℂ) + T * I)) *
        cos (π * ((x : ℂ) + T * I))) l (𝓝 0) := by
  obtain ⟨C, -, K, T₀, h⟩ := exists_norm_barnes_kernel_mul_cos_le_of_mem_Icc A z
    (c₁ ⊓ c₂) (c₁ ⊔ c₂)
  have hκ : 0 < π / 2 - 2 * |arg z| := by linarith
  refine TauCeti.intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le
    (by simpa using ((tendsto_one_add_abs_rpow_mul_exp_neg_mul_abs K hκ).mono_left hl).const_mul C)
    ?_
  filter_upwards [(tendsto_norm_cocompact_atTop.mono_left hl).eventually_ge_atTop T₀] with T hT
  refine .of_forall fun x hx ↦ (h x (uIoc_subset_uIcc hx) T hT).trans_eq ?_
  rw [neg_mul, mul_assoc]

/-- **The residues of the Barnes kernel.** At a pole `t = (A + n) / 2` of `Γ(A - 2t)` that
is not a pole of `Γ(t)`, `(t - (A + n) / 2) Γ(t) Γ(A - 2t) 2^t z^(2t)` tends to
`(-1)^(n+1) Γ((A + n) / 2) 2^((A + n) / 2) z^(A + n) / (2 n!)`. -/
theorem tendsto_sub_mul_barnes_kernel (A z : ℂ) (n : ℕ) (hA : ∀ m : ℕ, (A + n) / 2 ≠ -m) :
    Tendsto (fun t : ℂ ↦ (t - (A + n) / 2) * (Gamma t * Gamma (A - 2 * t) * 2 ^ t * z ^ (2 * t)))
      (𝓝[≠] ((A + n) / 2))
      (𝓝 ((-1 : ℂ) ^ (n + 1) * Gamma ((A + n) / 2) * 2 ^ ((A + n) / 2) * z ^ (A + n) /
        (2 * (n ! : ℂ)))) := by
  have hp : 2 * ((A + n) / 2) ≠ 0 := mul_ne_zero two_ne_zero (by simpa using hA 0)
  have hg : ContinuousAt (fun t : ℂ ↦ Gamma t * 2 ^ t * z ^ (2 * t)) ((A + n) / 2) :=
    ((continuousAt_Gamma _ hA).mul (continuousAt_const_cpow two_ne_zero)).mul
      ((continuousAt_const_cpow' hp).comp (continuousAt_id.const_mul 2))
  have h := (tendsto_sub_mul_Gamma_sub_two_mul A n).mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  have hA2 : 2 * ((A + n) / 2) = A + n := by ring
  rw [hA2] at h
  convert h using 2
  · ring
  · ring

end Complex
