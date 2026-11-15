/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The half-angle quantities `1 - cos θ`, `1 + cos θ` and their quotient

The quantity `1 - cos θ = 2 sin² (θ/2)` is positive for `θ ∈ (0, 2π)`, and
`1 + cos θ = 2 cos² (θ/2)` is positive for `θ ∈ (-π, π)`. Their quotient
`(1 - cos θ)/(1 + cos θ) = tan² (θ/2)` maps `(0, π)` bijectively onto `(0, ∞)`. This is the
substitution that turns integrals over a half-line into integrals over `(0, π)`.

## Main declarations

* `TauCeti.one_sub_cos_pos`, `TauCeti.one_add_cos_pos`: positivity of `1 ∓ cos θ`.
* `TauCeti.injOn_one_sub_cos_div_one_add_cos`: `θ ↦ (1 - cos θ)/(1 + cos θ)` is injective on
  `[0, π)`.
* `TauCeti.image_one_sub_cos_div_one_add_cos_Ioo`: it maps `(0, π)` onto `(0, ∞)`.
* `TauCeti.tan_half_mul_one_add_exp`: `tan (θ/2) (1 + e^{iθ}) = i (1 - e^{iθ})` when
  `cos (θ/2) ≠ 0`; for `θ ∈ (-π, π)`, `1 + e^{iθ} ≠ 0`
  (`TauCeti.one_add_exp_ofReal_mul_I_ne_zero`).
* `TauCeti.sign_tan_half`: `tan (θ/2)` has the sign of `θ` for `θ ∈ (-π, π)`.
-/

public section

open Real Set

namespace TauCeti

/-- For `θ ∈ (0, 2π)`, `1 - cos θ` is positive. -/
theorem one_sub_cos_pos {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ < 2 * π) : 0 < 1 - cos θ :=
  sub_pos.2 <| (cos_le_one θ).lt_of_ne fun h ↦
    h₀.ne' ((cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) h₁).1 h)

/-- For `θ ∈ (-π, π)`, `1 + cos θ` is positive. -/
theorem one_add_cos_pos {θ : ℝ} (h₀ : -π < θ) (h₁ : θ < π) : 0 < 1 + cos θ := by
  simpa [cos_add_pi] using one_sub_cos_pos (θ := θ + π) (by linarith) (by linarith)

/-- The map `θ ↦ (1 - cos θ)/(1 + cos θ)` is injective on `[0, π)`. -/
theorem injOn_one_sub_cos_div_one_add_cos :
    InjOn (fun θ ↦ (1 - cos θ) / (1 + cos θ)) (Ico 0 π) := by
  intro s hs t ht hst
  have hs' := one_add_cos_pos (by linarith [hs.1, pi_pos]) hs.2
  have ht' := one_add_cos_pos (by linarith [ht.1, pi_pos]) ht.2
  rw [div_eq_div_iff hs'.ne' ht'.ne'] at hst
  exact injOn_cos (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) (by linarith)

/-- The map `θ ↦ (1 - cos θ)/(1 + cos θ)` sends `(0, π)` onto `(0, ∞)`. -/
theorem image_one_sub_cos_div_one_add_cos_Ioo :
    (fun θ ↦ (1 - cos θ) / (1 + cos θ)) '' Ioo 0 π = Ioi 0 := by
  ext u
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact div_pos (one_sub_cos_pos hθ.1 (by linarith [hθ.2, pi_pos]))
      (one_add_cos_pos (by linarith [hθ.1, pi_pos]) hθ.2)
  · -- The preimage is `θ = arccos ((1 - u)/(1 + u))`.
    have hu : 0 < u := hu
    have hy₁ : (1 - u) / (1 + u) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have hy₂ : -1 < (1 - u) / (1 + u) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    refine ⟨arccos ((1 - u) / (1 + u)), ⟨arccos_pos.2 hy₁, arccos_lt_pi.2 hy₂⟩, ?_⟩
    have : 1 + u ≠ 0 := by linarith
    simp only
    rw [cos_arccos hy₂.le hy₁.le]
    field_simp
    ring

/-- For `θ ∈ (-π, π)`, `1 + e^{iθ} ≠ 0`: its real part `1 + cos θ` is positive. -/
theorem one_add_exp_ofReal_mul_I_ne_zero {θ : ℝ} (h₀ : -π < θ) (h₁ : θ < π) :
    1 + Complex.exp (θ * Complex.I) ≠ 0 := fun h ↦
  (one_add_cos_pos h₀ h₁).ne' (by simpa [Complex.exp_ofReal_mul_I_re] using congrArg Complex.re h)

/-- If `cos (θ/2) ≠ 0`, for instance for `θ ∈ (-π, π)`, then
`tan (θ/2) (1 + e^{iθ}) = i (1 - e^{iθ})`: the Cayley transform of `e^{iθ}` is `tan (θ/2)`. -/
theorem tan_half_mul_one_add_exp {θ : ℝ} (hc : cos (θ / 2) ≠ 0) :
    (tan (θ / 2) : ℂ) * (1 + Complex.exp (θ * Complex.I)) =
      Complex.I * (1 - Complex.exp (θ * Complex.I)) := by
  have hθ : θ = 2 * (θ / 2) := by ring
  apply Complex.ext <;>
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [hθ, cos_two_mul, sin_two_mul, tan_eq_sin_div_cos]
    field_simp
    linarith [congrArg (cos (θ / 2) * ·) (sin_sq_add_cos_sq (θ / 2))]

/-- For `θ ∈ (-π, π)`, `tan (θ/2)` has the sign of `θ`. -/
theorem sign_tan_half {θ : ℝ} (h₀ : -π < θ) (h₁ : θ < π) :
    Real.sign (tan (θ / 2)) = Real.sign θ := by
  rcases lt_trichotomy θ 0 with h | rfl | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (tan_neg_of_neg_of_pi_div_two_lt (by linarith)
      (by linarith))]
  · simp
  · rw [Real.sign_of_pos h, Real.sign_of_pos (tan_pos_of_pos_of_lt_pi_div_two (by linarith)
      (by linarith))]

end TauCeti
