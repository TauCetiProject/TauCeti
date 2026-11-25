/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Elementary Gaussian bounds and derivatives

A polynomial weight times a real Gaussian is bounded above, and completing the square absorbs a
linear tilt into half the Gaussian weight. This file records an explicit upper bound for
`(1 + r) ^ m * exp (-a r²)` (the scalar estimate behind the decay of Gaussian Schwartz functions),
the uniform bound `exp (-b u² - c u) ≤ exp (c² / (2 b)) * exp (-(b / 2) u²)` for `0 < b`,
the cocompact decay of `t ↦ exp (c - δ * t ^ 2)`, and modulus and vertical-shift bounds for
`z ↦ exp (δ * (z - θ) ^ 2)`, together with the complex derivative of `w ↦ exp (a (w - b)²)`.

## Main results

* `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`: an explicit upper bound for
  `(1 + r) ^ m * exp (-a r²)`.
* `TauCeti.exp_neg_mul_sq_sub_mul_le`: uniform completing-the-square bound for
  `exp (-b u² - c u)` when `0 < b`.
* `TauCeti.norm_exp_ofReal_mul_sub_sq`, `TauCeti.exp_mul_sq_add_mul`: modulus and
  square-completion for complex Gaussians.
* `TauCeti.norm_exp_ofReal_mul_sq_add_ofReal_mul_le`: the bound `exp (δ + |ω|)` for
  `exp (δ z² + ω z)` on the closed strip `0 ≤ re z ≤ 1`.
* `TauCeti.exp_neg_mul_intCast_sq_le`, `TauCeti.norm_exp_ofReal_mul_add_mul_I_sq_le`,
  `TauCeti.norm_exp_ofReal_mul_add_intCast_mul_I_sq_le`,
  `TauCeti.norm_exp_ofReal_mul_sq_mul_add_mul_I_sq_le`: vertical-shift Gaussian decay bounds.
* `TauCeti.tendsto_exp_sub_mul_sq_cocompact`,
  `TauCeti.tendstoUniformly_exp_ofReal_mul_add_mul_I_sq_smul`: cocompact decay and uniform damping.
* `Complex.hasDerivAt_cexp_mul_sub_sq`: the complex derivative of `w ↦ exp (a (w - b)²)`, for
  complex `a` and `b`; Gaussian kernels such as `z ↦ exp (-(c (t - z))²)` and
  `w ↦ exp (-(z + w)² / 2)` are the cases `a = -c²`, `b = t` and `a = -1/2`, `b = -z`.
-/

public section

open Filter
open scoped Nat Topology

namespace TauCeti

/-- For `0 < a`, the function `r ↦ (1 + r) ^ m * exp (-a r²)` is bounded above by the explicit
constant `m! / (a / 2) ^ m * exp a`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ} :
    (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! / (a / 2) ^ m * Real.exp a := by
  set u := 1 + r
  rcases lt_or_ge |u| 1 with hu | hu
  · -- `|u| < 1`: the left-hand side is at most `1`, and so is no larger than the constant.
    have h := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at h
    have hC : 1 ≤ m ! / (a / 2) ^ m * Real.exp a := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
      calc (a / 2) ^ m ≤ Real.exp (a / 2) * m ! := h
        _ ≤ Real.exp a * m ! := by gcongr; linarith
        _ = m ! * Real.exp a := mul_comm _ _
    refine le_trans ?_ hC
    calc u ^ m * Real.exp (-a * r ^ 2) ≤ |u| ^ m * Real.exp (-a * r ^ 2) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (abs_pow u m))
            (Real.exp_pos _).le
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg u) hu.le)
          (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])) (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  · -- `r² ≥ u² / 2 - 1`, so `exp (-a r²) ≤ exp a * exp (-(a / 2) u²)`.
    have hexp : Real.exp (-a * r ^ 2) ≤ Real.exp a * Real.exp (-(a / 2 * u ^ 2)) := by
      rw [← Real.exp_add]
      gcongr
      nlinarith [sq_nonneg (r - 1)]
    -- `u ^ m ≤ (u²) ^ m ≤ m! exp ((a / 2) u²) / (a / 2) ^ m`.
    have hpow : u ^ m ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by
      have h := Real.pow_div_factorial_le_exp (x := a / 2 * u ^ 2) (by positivity) m
      rw [div_le_iff₀ (by positivity), mul_pow] at h
      calc u ^ m ≤ |u| ^ m := (le_abs_self _).trans_eq (abs_pow u m)
        _ ≤ (|u| ^ 2) ^ m := by
            rw [← pow_mul]; exact pow_le_pow_right₀ hu (by omega)
        _ = (u ^ 2) ^ m := by rw [sq_abs]
        _ = (a / 2) ^ m * (u ^ 2) ^ m / (a / 2) ^ m := by field_simp
        _ ≤ Real.exp (a / 2 * u ^ 2) * m ! / (a / 2) ^ m := by gcongr
        _ = m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by ring
    calc u ^ m * Real.exp (-a * r ^ 2)
        ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) *
            (Real.exp a * Real.exp (-(a / 2 * u ^ 2))) := by gcongr
      _ = m ! / (a / 2) ^ m * Real.exp a := by
        rw [mul_assoc, mul_left_comm (Real.exp (a / 2 * u ^ 2)), ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]

/-- For `0 < b`, `exp (-b u² - c u) ≤ exp (c² / (2 b)) * exp (-(b / 2) u²)` uniformly in
`c u : ℝ`. -/
theorem exp_neg_mul_sq_sub_mul_le {b : ℝ} (hb : 0 < b) (c u : ℝ) :
    Real.exp (-b * u ^ 2 - c * u) ≤ Real.exp (c ^ 2 / (2 * b)) * Real.exp (-(b / 2) * u ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : 0 ≤ b / 2 * (u + c / b) ^ 2 := by positivity
  have hexpand : b / 2 * (u + c / b) ^ 2 = b / 2 * u ^ 2 + c * u + c ^ 2 / (2 * b) := by
    field_simp
    ring
  linarith

/-- For `0 < δ` and any `c : ℝ`, `t ↦ exp (c - δ * t ^ 2)` tends to `0` along `cocompact ℝ`. -/
theorem tendsto_exp_sub_mul_sq_cocompact {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (c - δ * t ^ 2)) (cocompact ℝ) (𝓝 0) :=
  Real.tendsto_exp_atBot.comp <| by
    have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
        fun _ => by simp
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_left _ c ((tendsto_neg_atTop_atBot.comp hsq).const_mul_atBot hδ)

/-- Modulus of the complex Gaussian factor `exp (δ * (z - θ) ^ 2)`. -/
theorem norm_exp_ofReal_mul_sub_sq (δ θ : ℝ) (z : ℂ) :
    ‖Complex.exp (δ * (z - θ) ^ 2)‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

/-- Modulus of the complex Gaussian factor `exp (δ * z ^ 2)`. -/
theorem norm_exp_ofReal_mul_sq (δ : ℝ) (z : ℂ) :
    ‖Complex.exp (δ * z ^ 2)‖ = Real.exp (δ * (z.re ^ 2 - z.im ^ 2)) := by
  simpa using norm_exp_ofReal_mul_sub_sq δ 0 z

/-- Modulus of `exp (δ * (a + t * I) ^ 2)` along a vertical line. -/
theorem norm_exp_ofReal_mul_add_mul_I_sq (δ a t : ℝ) :
    ‖Complex.exp (δ * ((a : ℂ) + t * Complex.I) ^ 2)‖ = Real.exp (δ * (a ^ 2 - t ^ 2)) := by
  simpa using norm_exp_ofReal_mul_sq δ (a + t * Complex.I)

/-- Completing the square for the complex Gaussian (`δ ≠ 0`). -/
theorem exp_mul_sq_add_mul {δ : ℂ} (hδ : δ ≠ 0) (ω z : ℂ) :
    Complex.exp (δ * z ^ 2 + ω * z) =
      Complex.exp (-(ω ^ 2 / (4 * δ))) * Complex.exp (δ * (z + ω / (2 * δ)) ^ 2) := by
  rw [← Complex.exp_add]; congr 1; field_simp; ring

/-- On the closed strip `0 ≤ re z ≤ 1`, the factor `exp (δ z² + ω z)` of the elementary admissible
functions of the complex method has modulus at most `exp (δ + |ω|)` for `0 ≤ δ`. -/
theorem norm_exp_ofReal_mul_sq_add_ofReal_mul_le {δ : ℝ} (hδ : 0 ≤ δ) (ω : ℝ) {z : ℂ}
    (hz : z.re ∈ Set.Icc 0 1) : ‖Complex.exp (δ * z ^ 2 + ω * z)‖ ≤ Real.exp (δ + |ω|) := by
  rw [Complex.norm_exp, Real.exp_le_exp]
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hω : ω * z.re ≤ |ω| := by
    calc ω * z.re ≤ |ω * z.re| := le_abs_self _
      _ = |ω| * z.re := by rw [abs_mul, abs_of_nonneg hz.1]
      _ ≤ |ω| := mul_le_of_le_one_right (abs_nonneg ω) hz.2
  have h1 : z.re * z.re ≤ 1 := by nlinarith [hz.1, hz.2]
  have h2 : δ * (z.re * z.re - z.im * z.im) ≤ δ := by
    nlinarith [mul_nonneg hδ (mul_self_nonneg z.im)]
  linarith

/-- Quadratic Gaussian decay on `ℤ` dominates geometric decay (`0 ≤ a`). -/
theorem exp_neg_mul_intCast_sq_le {a : ℝ} (ha : 0 ≤ a) (k : ℤ) :
    Real.exp (-a * (k : ℝ) ^ 2) ≤ Real.exp (-a) ^ k.natAbs := by
  rw [← Real.exp_natCast_mul]
  have hk : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
    simpa [Int.cast_pow] using (Int.cast_le (R := ℝ)).2 (Int.natAbs_le_self_sq k)
  exact Real.exp_le_exp.2 (by nlinarith)

/-- Vertical shift bound for the complex Gaussian (`0 ≤ δ`). -/
theorem norm_exp_ofReal_mul_add_mul_I_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (z : ℂ) (y : ℝ) :
    ‖Complex.exp ((δ : ℂ) * (z + y * Complex.I) ^ 2)‖ ≤
      Real.exp (δ * (z.re ^ 2 + z.im ^ 2)) * Real.exp (-(δ * y ^ 2 / 2)) := by
  rw [norm_exp_ofReal_mul_sq, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by simp; nlinarith [mul_nonneg hδ (sq_nonneg (2 * z.im + y))])

/-- Vertical integer-lattice shift bound for the complex Gaussian (`0 ≤ δ`). -/
theorem norm_exp_ofReal_mul_add_intCast_mul_I_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (T : ℝ) (k : ℤ)
    (z : ℂ) : ‖Complex.exp ((δ : ℂ) * (z + k * T * Complex.I) ^ 2)‖ ≤
      Real.exp (δ * (z.re ^ 2 + z.im ^ 2)) * Real.exp (-(δ * T ^ 2 / 2)) ^ k.natAbs := by
  have hc : z + (k : ℂ) * T * Complex.I = z + ((k * T : ℝ) : ℂ) * Complex.I := by push_cast; rfl
  have he : -(δ * (k * T) ^ 2 / 2) = -(δ * T ^ 2 / 2) * (k : ℝ) ^ 2 := by ring
  exact hc ▸ (norm_exp_ofReal_mul_add_mul_I_sq_le hδ z (k * T)).trans
    (mul_le_mul_of_nonneg_left (he ▸ exp_neg_mul_intCast_sq_le (by positivity) k)
      (Real.exp_pos _).le)

/-- Product bound for a complex Gaussian and its vertical shift by `y * I` (`0 ≤ δ`). -/
theorem norm_exp_ofReal_mul_sq_mul_add_mul_I_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (z : ℂ) (y : ℝ) :
    ‖Complex.exp ((δ : ℂ) * z ^ 2) * Complex.exp ((δ : ℂ) * (z + y * Complex.I) ^ 2)‖ ≤
      Real.exp (2 * δ * z.re ^ 2) * Real.exp (-(δ * y ^ 2 / 2)) := by
  rw [norm_mul, norm_exp_ofReal_mul_sq, norm_exp_ofReal_mul_sq, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by simp; nlinarith [mul_nonneg hδ (sq_nonneg (2 * z.im + y))])

/-- Gaussian damping along `a + t * I` converges uniformly on `ℝ` to `f` along `𝓝[≥] 0`, for any
bounded `f : ℝ → E` vanishing along `cocompact ℝ`. -/
theorem tendstoUniformly_exp_ofReal_mul_add_mul_I_sq_smul {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (a : ℝ) {f : ℝ → E}
    (hb : Bornology.IsBounded (Set.range f)) (hf : Tendsto f (cocompact ℝ) (𝓝 0)) :
    TendstoUniformly (fun (δ : ℝ) (t : ℝ) ↦
      Complex.exp ((δ : ℂ) * ((a : ℂ) + t * Complex.I) ^ 2) • f t) f (𝓝[≥] 0) := by
  rw [Metric.tendstoUniformly_iff]; intro ε hε
  obtain ⟨M, hM, hfM⟩ := hb.exists_pos_norm_le
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 <|
    Metric.tendsto_nhds.1 hf (ε / (Real.exp 1 + 1)) (by positivity)
  obtain ⟨B, hB, hKB⟩ := (hK.image (by fun_prop : Continuous fun t : ℝ ↦
    ((a : ℂ) + t * Complex.I) ^ 2)).isBounded.exists_pos_norm_le
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.1
    (Complex.continuous_exp.continuousAt (x := 0)) (ε / M) (div_pos hε hM)
  filter_upwards [Ico_mem_nhdsGE (lt_min (by positivity : 0 < 1 / (a ^ 2 + 1))
    (div_pos hηpos hB))] with δ ⟨hδ0, hδlt⟩ t
  rw [dist_comm, dist_eq_norm]
  by_cases ht : t ∈ K
  · have hw : dist ((δ : ℂ) * ((a : ℂ) + t * Complex.I) ^ 2) 0 < η := by
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ0]
      exact (mul_lt_mul_of_nonneg_of_pos (hδlt.trans_le (min_le_right _ _))
        (hKB _ ⟨t, ht, rfl⟩) hδ0 hB).trans_eq (div_mul_cancel₀ η hB.ne')
    nth_rw 2 [← one_smul ℂ (f t)]; rw [← sub_smul, norm_smul]
    exact (mul_lt_mul_of_nonneg_of_pos (by simpa [dist_eq_norm] using hη hw)
      (hfM _ ⟨t, rfl⟩) (norm_nonneg _) hM).trans_eq (div_mul_cancel₀ ε hM.ne')
  · have hft : ‖f t‖ < ε / (Real.exp 1 + 1) := by simpa [dist_zero_right] using hKc ht
    have hexp : ‖Complex.exp ((δ : ℂ) * ((a : ℂ) + t * Complex.I) ^ 2)‖ ≤ Real.exp 1 := by
      rw [norm_exp_ofReal_mul_add_mul_I_sq]; refine Real.exp_le_exp.2 ?_
      have := (lt_div_iff₀ (by positivity : 0 < a ^ 2 + 1)).1 (hδlt.trans_le (min_le_left _ _))
      nlinarith [sq_nonneg t, hδ0]
    refine (norm_sub_le _ _).trans_lt ?_; rw [norm_smul]
    have := (mul_lt_mul_of_pos_left hft (by positivity : 0 < Real.exp 1 + 1)).trans_eq
      (mul_div_cancel₀ ε (by positivity))
    linarith [mul_le_mul_of_nonneg_right hexp (norm_nonneg (f t))]

end TauCeti

namespace Complex

/-- The complex derivative of the translated quadratic exponential `w ↦ exp (a (w - b)²)` is
`exp (a (w - b)²) · 2a (w - b)`, for complex `a` and `b`. -/
theorem hasDerivAt_cexp_mul_sub_sq (a b w : ℂ) :
    HasDerivAt (fun w : ℂ => cexp (a * (w - b) ^ 2)) (cexp (a * (w - b) ^ 2) * (2 * a * (w - b)))
      w := by
  have h := (((hasDerivAt_id' w).sub_const b).fun_pow 2).const_mul a |>.cexp
  convert h using 1
  ring

end Complex
