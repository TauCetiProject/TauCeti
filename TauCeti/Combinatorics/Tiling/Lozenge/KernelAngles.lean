/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.InverseKernel
import TauCeti.Analysis.Fourier.InvAddMulExp
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos

/-!
# Angles of the lozenge kernel

For positive type weights `w = (w₁, w₂, w₃)` with `1 / P_w` integrable on the torus, in
particular for liquid weights (`TauCeti.IsLiquidWeights.integrableOn_inv_lozengeCharFun`), the
kernel
`G_w(d) = (4π²)⁻¹ ∫∫_{[0,2π]²} e^{i(d₁θ + d₂φ)} / P_w(θ, φ) dθ dφ` (`TauCeti.lozengeKernel`)
takes explicit values along the row `d₂ = −1` and the column `d₁ = 1`, given by the angles
`θ₁`, `θ₂`, `θ₃` opposite `w₁`, `w₂`, `w₃` in the triangle with these sides
(`TauCeti.lozengeTriangleAngle`):

* `w₁ G_w(−e₂) = θ₁ / π`, `w₂ G_w(e₁) = θ₂ / π` and `w₃ G_w(0) = θ₃ / π`
  (`TauCeti.mul_lozengeKernel_zero_neg_one`, `TauCeti.mul_lozengeKernel_one_zero`,
  `TauCeti.mul_lozengeKernel_zero`);
* for `m ≠ 0`, `w₁ G_w((m, −1)) = (−1)^m sin(θ₁ m) / (π m)` and
  `w₂ G_w((1, m)) = (−1)^m sin(θ₂ m) / (π m)` (`TauCeti.mul_lozengeKernel_row_of_ne_zero`,
  `TauCeti.mul_lozengeKernel_column_of_ne_zero`).

Each angle lies in `[0, π]` (`TauCeti.lozengeTriangleAngle_mem_Icc`), in `(0, π)` for a
nondegenerate triangle (`TauCeti.lozengeTriangleAngle_mem_Ioo`), and satisfies the law of cosines
(`TauCeti.cos_lozengeTriangleAngle`). The angles sum to `π`
(`TauCeti.lozengeTriangleAngle_add_add_eq_pi`), and `θ₁ = π − θ₀`,
`θ₂ = π − φ₀` for the zero angles `θ₀`, `φ₀` (`TauCeti.lozengeZeroAngleFst`,
`TauCeti.lozengeZeroAngleSnd`). When one weight is at least the sum of the other two, the angle
opposite it is `π` and the other two are `0`, matching the frozen value `w₃ G_w(0) = 1` of the
weights `(1, 1, 3)`.

## Proof

By Fubini (`TauCeti.lozengeKernel_eq_integral_integral`,
`TauCeti.lozengeKernel_eq_integral_integral_swap`) `G_w(d)` is an iterated integral. For
`d = (m, −1)`, integrate `φ` first: the integrand is `e^{imθ}` times `1 / (w₁ + a e^{iφ})` with
`a = w₃ + w₂ e^{iθ}`, whose integral over a period is `2π / w₁` when `|a| < w₁` and `0` when
`|a| > w₁` (`TauCeti.integral_exp_div_add_of_norm_lt_of_nonpos`,
`TauCeti.integral_exp_div_add_of_lt_norm_of_nonpos`;
`TauCeti.integral_lozengeKernel_integrand_row`). Since `|a|² = w₂² + w₃² + 2 w₂ w₃ cos θ`
(`Complex.sq_norm_ofReal_add_mul_exp`), the condition `|a| < w₁` says `cos θ < cos θ₀`, that
is `θ ∈ (θ₀, 2π − θ₀)` (`Real.cos_lt_cos_iff_mem_Ioo`), an arc of length `2θ₁`, and the
boundary case `cos θ = cos θ₀` is a null set (`Real.volume_setOf_cos_eq`;
`TauCeti.setIntegral_Ioc_eq_mul_intervalIntegral_arc`). Hence
`w₁ G_w((m, −1)) = (2π)⁻¹ ∫_{θ₀}^{2π−θ₀} e^{imθ} dθ` (`TauCeti.mul_lozengeKernel_row`). The column
`d = (1, m)` is the same with `θ` integrated first (`TauCeti.mul_lozengeKernel_column`). The value
at `d = 0` follows from the three-term identity `w₃ G_w(0) + w₂ G_w(e₁) + w₁ G_w(−e₂) = 1`
(`TauCeti.lozengeKernel_three_term_of_integrableOn`) and `θ₁ + θ₂ + θ₃ = π`.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Theorem 6.1.
-/

public section

noncomputable section

open Complex Set MeasureTheory
open scoped Real

namespace TauCeti

/-- The angle `arccos ((b² + c² − a²) / (2 b c))` opposite the side `a` in a triangle with sides
`a`, `b`, `c`; `arccos` clamps its argument to `[−1, 1]`, so for positive `a`, `b`, `c`, when
`a ≥ b + c` the angle is `π` (`TauCeti.lozengeTriangleAngle_eq_pi`), and when `b ≥ a + c` or
`c ≥ a + b` it is `0` (`TauCeti.lozengeTriangleAngle_eq_zero`). For type weights
`w = (w₁, w₂, w₃)` the angles `θ₁`, `θ₂`, `θ₃` opposite `w₁`, `w₂`, `w₃` are
`lozengeTriangleAngle w₁ w₂ w₃`, `lozengeTriangleAngle w₂ w₁ w₃` and
`lozengeTriangleAngle w₃ w₁ w₂`. -/
def lozengeTriangleAngle (a b c : ℝ) : ℝ :=
  Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c))

/-- The value of the triangle angle. -/
theorem lozengeTriangleAngle_def (a b c : ℝ) :
    lozengeTriangleAngle a b c = Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c)) :=
  (rfl)

/-- The triangle angle is symmetric in the two adjacent sides. -/
theorem lozengeTriangleAngle_comm (a b c : ℝ) :
    lozengeTriangleAngle a c b = lozengeTriangleAngle a b c := by
  simp only [lozengeTriangleAngle_def]
  congr 1
  ring

/-- The triangle angle lies in `[0, π]`. -/
theorem lozengeTriangleAngle_mem_Icc (a b c : ℝ) : lozengeTriangleAngle a b c ∈ Icc 0 π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- **Law of cosines**: if `b, c > 0` and `a, b, c` satisfy the triangle inequalities, the
cosine of the angle opposite `a` is `(b² + c² − a²) / (2 b c)`. -/
theorem cos_lozengeTriangleAngle {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : a ≤ b + c)
    (hb' : b ≤ a + c) (hc' : c ≤ a + b) :
    Real.cos (lozengeTriangleAngle a b c) = (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) := by
  have hbc : 0 < 2 * b * c := by positivity
  rw [lozengeTriangleAngle_def, Real.cos_arccos]
  · rw [le_div_iff₀ hbc]
    nlinarith
  · rw [div_le_iff₀ hbc]
    nlinarith

/-- For a nondegenerate triangle, with all three triangle inequalities strict, the angle lies in
`(0, π)`. -/
theorem lozengeTriangleAngle_mem_Ioo {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : a < b + c)
    (hb' : b < a + c) (hc' : c < a + b) : lozengeTriangleAngle a b c ∈ Ioo 0 π := by
  have hbc : 0 < 2 * b * c := by positivity
  rw [lozengeTriangleAngle_def]
  refine ⟨Real.arccos_pos.2 ?_, Real.arccos_lt_pi.2 ?_⟩
  · rw [div_lt_iff₀ hbc]
    nlinarith
  · rw [lt_div_iff₀ hbc]
    nlinarith

variable {w₁ w₂ w₃ : ℝ}

/-- `θ₁ = π − θ₀`: the angle opposite `w₁` is the exterior angle at the first zero angle. -/
theorem lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleFst (w₁ w₂ w₃ : ℝ) :
    lozengeTriangleAngle w₁ w₂ w₃ = π - lozengeZeroAngleFst w₁ w₂ w₃ := by
  rw [lozengeTriangleAngle_def, lozengeZeroAngleFst_def, ← Real.arccos_neg]
  congr 1
  ring

/-- `θ₂ = π − φ₀`: the angle opposite `w₂` is the exterior angle at the second zero angle. -/
theorem lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleSnd (w₁ w₂ w₃ : ℝ) :
    lozengeTriangleAngle w₂ w₁ w₃ = π - lozengeZeroAngleSnd w₁ w₂ w₃ := by
  rw [lozengeTriangleAngle_def, lozengeZeroAngleSnd_def, ← Real.arccos_neg]
  congr 1
  ring

/-- The angle opposite a side at least the sum of the other two is `π`. -/
theorem lozengeTriangleAngle_eq_pi {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : b + c ≤ a) :
    lozengeTriangleAngle a b c = π := by
  rw [lozengeTriangleAngle_def, Real.arccos_of_le_neg_one]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The angle adjacent to a side `b` at least the sum of the other two is `0`. -/
theorem lozengeTriangleAngle_eq_zero {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (h : a + c ≤ b) : lozengeTriangleAngle a b c = 0 := by
  rw [lozengeTriangleAngle_def, Real.arccos_of_one_le]
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-- For liquid weights, `θ₃ = θ₀ + φ₀ − π` at the zero `(θ₀, φ₀)` of `P_w`, so the angles sum
to `π`. -/
private theorem lozengeTriangleAngle_add_add_eq_pi_of_isLiquidWeights
    (hw : IsLiquidWeights w₁ w₂ w₃) :
    lozengeTriangleAngle w₁ w₂ w₃ + lozengeTriangleAngle w₂ w₁ w₃ +
      lozengeTriangleAngle w₃ w₁ w₂ = π := by
  have h1 := hw.pos_fst
  have h2 := hw.pos_snd
  set θ₀ := lozengeZeroAngleFst w₁ w₂ w₃ with hθ₀
  set φ₀ := lozengeZeroAngleSnd w₁ w₂ w₃ with hφ₀
  have hθ := hw.lozengeZeroAngleFst_mem_Ioo
  have hφ := hw.lozengeZeroAngleSnd_mem_Ioo
  have hz : lozengeCharFun w₁ w₂ w₃ θ₀ φ₀ = 0 :=
    (lozengeCharFun_eq_zero_iff hw).2 ⟨0, 0, Or.inl ⟨by simp [hθ₀], by simp [hφ₀]⟩⟩
  obtain ⟨hre, him⟩ := lozengeCharFun_eq_zero_iff_re_im.1 hz
  have hsin := mul_sin_add_eq_of_lozengeCharFun_eq_zero hz
  have hs₀ : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  -- `θ₀ + φ₀ > π`, since `w₁ sin (θ₀ + φ₀) = −w₃ sin θ₀ < 0`
  have hgt : π < θ₀ + φ₀ := by
    by_contra hle
    have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, hφ.1]) (not_lt.1 hle)
    nlinarith [hw.pos_thd]
  have h3 : lozengeTriangleAngle w₃ w₁ w₂ = θ₀ + φ₀ - π := by
    rw [lozengeTriangleAngle_def]
    have hc : (w₁ ^ 2 + w₂ ^ 2 - w₃ ^ 2) / (2 * w₁ * w₂) = Real.cos (θ₀ + φ₀ - π) := by
      rw [Real.cos_sub_pi, Real.cos_add, div_eq_iff (by positivity)]
      linear_combination (-(w₃ - w₂ * Real.cos θ₀ - w₁ * Real.cos φ₀)) * hre +
        (w₂ * Real.sin θ₀ - w₁ * Real.sin φ₀) * him - w₁ ^ 2 * Real.sin_sq_add_cos_sq φ₀ -
        w₂ ^ 2 * Real.sin_sq_add_cos_sq θ₀
    rw [hc, Real.arccos_cos (by linarith) (by linarith [hθ.2, hφ.2])]
  rw [lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleFst,
    lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleSnd, h3]
  ring

/-- **The angles of the triangle with sides `w₁, w₂, w₃` sum to `π`**:
`θ₁ + θ₂ + θ₃ = π`, where `θ_k` is the angle opposite `w_k`. For liquid weights this is the
angle sum of a genuine triangle, with `θ₃ = θ₀ + φ₀ − π` for the zero `(θ₀, φ₀)` of `P_w`;
otherwise one side is at least the sum of the other two, and the clamped angles are `π`, `0`, `0`.
-/
theorem lozengeTriangleAngle_add_add_eq_pi (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃) :
    lozengeTriangleAngle w₁ w₂ w₃ + lozengeTriangleAngle w₂ w₁ w₃ +
      lozengeTriangleAngle w₃ w₁ w₂ = π := by
  rcases le_or_gt (w₂ + w₃) w₁ with ha | ha
  · rw [lozengeTriangleAngle_eq_pi h₂ h₃ ha, lozengeTriangleAngle_eq_zero h₂ h₃ ha,
      lozengeTriangleAngle_eq_zero h₃ h₂ (by linarith)]
    ring
  rcases le_or_gt (w₁ + w₃) w₂ with hb | hb
  · rw [lozengeTriangleAngle_eq_pi h₁ h₃ hb, lozengeTriangleAngle_eq_zero h₁ h₃ hb,
      ← lozengeTriangleAngle_comm w₃, lozengeTriangleAngle_eq_zero h₃ h₁ (by linarith)]
    ring
  rcases le_or_gt (w₁ + w₂) w₃ with hc | hc
  · rw [lozengeTriangleAngle_eq_pi h₁ h₂ hc, ← lozengeTriangleAngle_comm w₁,
      lozengeTriangleAngle_eq_zero h₁ h₂ hc, ← lozengeTriangleAngle_comm w₂,
      lozengeTriangleAngle_eq_zero h₂ h₁ (by linarith)]
    ring
  exact lozengeTriangleAngle_add_add_eq_pi_of_isLiquidWeights (isLiquidWeights_iff.2 ⟨ha, hb, hc⟩)

/-! ### The inner integrals along a row and a column -/

/-- The `φ`-integral of the integrand of `G_w((m, −1))` at `θ`: it is `2π e^{imθ} / w₁` when
`|w₃ + w₂ e^{iθ}| < w₁`, that is `cos θ < cos θ₀`, and `0` when `cos θ > cos θ₀`. -/
theorem integral_lozengeKernel_integrand_row (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃) (m : ℤ)
    {θ : ℝ} (hθ : Real.cos θ ≠ Real.cos (lozengeZeroAngleFst w₁ w₂ w₃)) :
    ∫ φ in Ioc 0 (2 * π), exp ((m * θ + ((-1 : ℤ) : ℝ) * φ : ℝ) * I) /
        lozengeCharFun w₁ w₂ w₃ θ φ =
      if Real.cos θ < Real.cos (lozengeZeroAngleFst w₁ w₂ w₃) then
        exp (m * θ * I) * (2 * π / w₁) else 0 := by
  set a : ℂ := (w₃ : ℂ) + w₂ * exp (θ * I) with ha
  have hpt : ∀ φ : ℝ, exp ((m * θ + ((-1 : ℤ) : ℝ) * φ : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ θ φ =
      exp (m * θ * I) * (exp (((0 : ℤ) : ℂ) * φ * I) / (w₁ + a * exp (φ * I))) := by
    intro φ
    have hee : exp (φ * I) * exp (-(φ * I)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    have hQ : (w₁ : ℂ) + a * exp (φ * I) = exp (φ * I) * lozengeCharFun w₁ w₂ w₃ θ φ := by
      rw [lozengeCharFun_def, ha]
      linear_combination (-(w₁ : ℂ)) * hee
    have e : exp ((m * θ + ((-1 : ℤ) : ℝ) * φ : ℝ) * I) = exp (m * θ * I) * exp (-(φ * I)) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [hQ, e]
    simp only [Int.cast_zero, zero_mul, exp_zero, exp_neg]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity)]
  rw [lozengeZeroAngleFst_def] at hθ ⊢
  have hθ' : Real.cos θ ∈ Icc (-1) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  split_ifs with hlt
  · have hn : ‖a‖ < ‖(w₁ : ℂ)‖ := by
      rw [norm_real, Real.norm_of_nonneg h₁.le, ha, norm_ofReal_add_mul_exp_lt_iff h₃ h₂ h₁]
      exact (Real.lt_iff_lt_cos_arccos hθ' hθ).2 hlt
    rw [integral_exp_div_add_of_norm_lt_of_nonpos hn le_rfl]
    simp only [neg_zero, zpow_zero, mul_one, zero_sub, zpow_neg_one]
    ring
  · have hn : ‖(w₁ : ℂ)‖ < ‖a‖ := by
      rw [norm_real, Real.norm_of_nonneg h₁.le, ha, lt_norm_ofReal_add_mul_exp_iff h₃ h₂ h₁]
      exact (Real.lt_iff_cos_arccos_lt hθ' hθ).2 (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hθ))
    rw [integral_exp_div_add_of_lt_norm_of_nonpos hn le_rfl, mul_zero]

/-- The `θ`-integral of the integrand of `G_w((1, m))` at `φ`: it is `2π e^{imφ} / w₂` when
`|w₃ + w₁ e^{−iφ}| < w₂`, that is `cos φ < cos φ₀`, and `0` when `cos φ > cos φ₀`. -/
theorem integral_lozengeKernel_integrand_column (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (m : ℤ) {φ : ℝ} (hφ : Real.cos φ ≠ Real.cos (lozengeZeroAngleSnd w₁ w₂ w₃)) :
    ∫ θ in Ioc 0 (2 * π), exp ((((1 : ℤ) : ℝ) * θ + m * φ : ℝ) * I) /
        lozengeCharFun w₁ w₂ w₃ θ φ =
      if Real.cos φ < Real.cos (lozengeZeroAngleSnd w₁ w₂ w₃) then
        exp (m * φ * I) * (2 * π / w₂) else 0 := by
  set b : ℂ := (w₃ : ℂ) + w₁ * exp ((-φ : ℝ) * I) with hb
  have hpt : ∀ θ : ℝ, exp ((((1 : ℤ) : ℝ) * θ + m * φ : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ θ φ =
      exp (m * φ * I) * (exp (((1 : ℤ) : ℂ) * θ * I) / (b + w₂ * exp (θ * I))) := by
    intro θ
    have hQ : b + w₂ * exp (θ * I) = lozengeCharFun w₁ w₂ w₃ θ φ := by
      rw [lozengeCharFun_def, hb, ofReal_neg, neg_mul]
      ring
    have e : exp ((((1 : ℤ) : ℝ) * θ + m * φ : ℝ) * I) =
        exp (m * φ * I) * exp (((1 : ℤ) : ℂ) * θ * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [hQ, e, mul_div_assoc]
  simp_rw [hpt]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity)]
  rw [lozengeZeroAngleSnd_def] at hφ ⊢
  have hφ' : Real.cos φ ∈ Icc (-1) 1 := ⟨Real.neg_one_le_cos φ, Real.cos_le_one φ⟩
  have hcos : Real.cos (-φ) = Real.cos φ := Real.cos_neg φ
  split_ifs with hlt
  · have hn : ‖b‖ < ‖(w₂ : ℂ)‖ := by
      rw [norm_real, Real.norm_of_nonneg h₂.le, hb, norm_ofReal_add_mul_exp_lt_iff h₃ h₁ h₂, hcos]
      exact (Real.lt_iff_lt_cos_arccos hφ' hφ).2 hlt
    rw [integral_exp_div_add_of_lt_norm_of_pos hn one_pos]
    simp only [sub_self, zpow_zero, mul_one, Int.reduceNeg, zpow_neg_one]
    ring
  · have hn : ‖(w₂ : ℂ)‖ < ‖b‖ := by
      rw [norm_real, Real.norm_of_nonneg h₂.le, hb, lt_norm_ofReal_add_mul_exp_iff h₃ h₁ h₂, hcos]
      exact (Real.lt_iff_cos_arccos_lt hφ' hφ).2 (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hφ))
    rw [integral_exp_div_add_of_norm_lt_of_pos hn one_pos, mul_zero]

/-! ### The kernel along a row and a column, and the angles -/

/-- **The kernel along the row `d₂ = −1`.** For positive weights with `1 / P_w` integrable on
the torus and `m ∈ ℤ`,
`w₁ G_w((m, −1)) = (2π)⁻¹ ∫_{θ₀}^{2π−θ₀} e^{imθ} dθ`, where
`θ₀ = lozengeZeroAngleFst w₁ w₂ w₃`. -/
theorem mul_lozengeKernel_row (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π))) (m : ℤ) :
    (w₁ : ℂ) * lozengeKernel w₁ w₂ w₃ (m, -1) =
      (2 * π : ℂ)⁻¹ * ∫ θ in lozengeZeroAngleFst w₁ w₂ w₃..2 * π - lozengeZeroAngleFst w₁ w₂ w₃,
        exp (m * θ * I) := by
  rw [lozengeKernel_eq_integral_integral hP,
    setIntegral_Ioc_eq_mul_intervalIntegral_arc (lozengeZeroAngleFst_mem_Icc w₁ w₂ w₃) m
      (2 * π / w₁) fun θ hθ => integral_lozengeKernel_integrand_row h₁ h₂ h₃ m hθ, real_smul]
  have h1 : (w₁ : ℂ) ≠ 0 := ofReal_ne_zero.2 h₁.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  set X := ∫ θ in lozengeZeroAngleFst w₁ w₂ w₃..2 * π - lozengeZeroAngleFst w₁ w₂ w₃,
    exp (m * θ * I)
  push_cast
  field_simp
  ring

/-- **The kernel along the column `d₁ = 1`.** For positive weights with `1 / P_w` integrable on
the torus and `m ∈ ℤ`,
`w₂ G_w((1, m)) = (2π)⁻¹ ∫_{φ₀}^{2π−φ₀} e^{imφ} dφ`, where
`φ₀ = lozengeZeroAngleSnd w₁ w₂ w₃`. -/
theorem mul_lozengeKernel_column (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π))) (m : ℤ) :
    (w₂ : ℂ) * lozengeKernel w₁ w₂ w₃ (1, m) =
      (2 * π : ℂ)⁻¹ * ∫ φ in lozengeZeroAngleSnd w₁ w₂ w₃..2 * π - lozengeZeroAngleSnd w₁ w₂ w₃,
        exp (m * φ * I) := by
  rw [lozengeKernel_eq_integral_integral_swap hP,
    setIntegral_Ioc_eq_mul_intervalIntegral_arc (lozengeZeroAngleSnd_mem_Icc w₁ w₂ w₃) m
      (2 * π / w₂) fun φ hφ => integral_lozengeKernel_integrand_column h₁ h₂ h₃ m hφ, real_smul]
  have h2 : (w₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 h₂.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  set X := ∫ φ in lozengeZeroAngleSnd w₁ w₂ w₃..2 * π - lozengeZeroAngleSnd w₁ w₂ w₃,
    exp (m * φ * I)
  push_cast
  field_simp
  ring

/-- **The angle `θ₁`**: for positive weights with `1 / P_w` integrable on the torus,
`w₁ G_w(−e₂) = θ₁ / π`, where `θ₁` is the angle
opposite `w₁` in the triangle with sides `w₁, w₂, w₃`. -/
theorem mul_lozengeKernel_zero_neg_one (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π))) :
    (w₁ : ℂ) * lozengeKernel w₁ w₂ w₃ (0, -1) = (lozengeTriangleAngle w₁ w₂ w₃ / π : ℝ) := by
  have h := mul_lozengeKernel_row h₁ h₂ h₃ hP 0
  rw [Int.cast_zero] at h
  rw [h, inv_mul_integral_cexp_zero_mul_mul_I_arc,
    lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleFst]

/-- **The angle `θ₂`**: for positive weights with `1 / P_w` integrable on the torus,
`w₂ G_w(e₁) = θ₂ / π`, where `θ₂` is the angle
opposite `w₂` in the triangle with sides `w₁, w₂, w₃`. -/
theorem mul_lozengeKernel_one_zero (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π))) :
    (w₂ : ℂ) * lozengeKernel w₁ w₂ w₃ (1, 0) = (lozengeTriangleAngle w₂ w₁ w₃ / π : ℝ) := by
  have h := mul_lozengeKernel_column h₁ h₂ h₃ hP 0
  rw [Int.cast_zero] at h
  rw [h, inv_mul_integral_cexp_zero_mul_mul_I_arc,
    lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleSnd]

/-- **The angle `θ₃`**: for positive weights with `1 / P_w` integrable on the torus,
`w₃ G_w(0) = θ₃ / π`, where `θ₃` is the angle
opposite `w₃` in the triangle with sides `w₁, w₂, w₃`. -/
theorem mul_lozengeKernel_zero (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π))) :
    (w₃ : ℂ) * lozengeKernel w₁ w₂ w₃ 0 = (lozengeTriangleAngle w₃ w₁ w₂ / π : ℝ) := by
  have h := lozengeKernel_three_term_of_integrableOn hP
    (ae_restrict_of_ae (ae_lozengeCharFun_ne_zero_of_ne_zero h₂.ne' h₃.ne')) 0
  rw [zero_add, zero_sub, ite_eq_left rfl] at h
  have h3 : lozengeTriangleAngle w₃ w₁ w₂ =
      π - lozengeTriangleAngle w₁ w₂ w₃ - lozengeTriangleAngle w₂ w₁ w₃ := by
    linarith [lozengeTriangleAngle_add_add_eq_pi h₁ h₂ h₃]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have e₁ := mul_lozengeKernel_zero_neg_one h₁ h₂ h₃ hP
  have e₂ := mul_lozengeKernel_one_zero h₁ h₂ h₃ hP
  rw [Prod.neg_mk, neg_zero] at h
  rw [h3]
  push_cast at e₁ e₂ ⊢
  rw [eq_div_iff hπ] at e₁ e₂ ⊢
  linear_combination π * h - e₁ - e₂

/-- **The kernel along the row `d₂ = −1`, explicitly.** For positive weights with `1 / P_w`
integrable on the torus and `m ≠ 0`,
`w₁ G_w((m, −1)) = (−1)^m sin(θ₁ m) / (π m)`, where `θ₁` is the angle opposite `w₁`. -/
theorem mul_lozengeKernel_row_of_ne_zero (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π)))
    {m : ℤ} (hm : m ≠ 0) :
    (w₁ : ℂ) * lozengeKernel w₁ w₂ w₃ (m, -1) =
      ((-1 : ℝ) ^ m * Real.sin (m * lozengeTriangleAngle w₁ w₂ w₃) / (π * m) : ℝ) := by
  rw [mul_lozengeKernel_row h₁ h₂ h₃ hP, inv_mul_integral_cexp_intCast_mul_mul_I_arc _ hm,
    lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleFst]

/-- **The kernel along the column `d₁ = 1`, explicitly.** For positive weights with `1 / P_w`
integrable on the torus and `m ≠ 0`,
`w₂ G_w((1, m)) = (−1)^m sin(θ₂ m) / (π m)`, where `θ₂` is the angle opposite `w₂`. -/
theorem mul_lozengeKernel_column_of_ne_zero (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π)))
    {m : ℤ} (hm : m ≠ 0) :
    (w₂ : ℂ) * lozengeKernel w₁ w₂ w₃ (1, m) =
      ((-1 : ℝ) ^ m * Real.sin (m * lozengeTriangleAngle w₂ w₁ w₃) / (π * m) : ℝ) := by
  rw [mul_lozengeKernel_column h₁ h₂ h₃ hP, inv_mul_integral_cexp_intCast_mul_mul_I_arc _ hm,
    lozengeTriangleAngle_eq_pi_sub_lozengeZeroAngleSnd]

end TauCeti
