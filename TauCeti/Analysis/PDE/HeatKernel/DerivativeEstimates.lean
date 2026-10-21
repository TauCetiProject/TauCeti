/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Analysis.PDE.HeatKernel.Bounds

/-!
# Scale-invariant estimates for the derivatives of the heat kernel

On a finite-dimensional real inner product space `E` of dimension `n`, the heat kernel
`K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` is invariant under the parabolic scaling
`K_t(x) = (√t)⁻¹ ^ n K_1((√t)⁻¹ • x)`, so each spatial derivative costs a factor `t^(-1/2)`.
This file records the resulting estimates, whose constants do not depend on the time, together
with the cancellation of the derivatives:

* `D^m K_t(x) = (√t)⁻¹ ^ (n + m) • D^m K_1((√t)⁻¹ • x)`;
* `‖D^m K_t(x)‖ ≤ C t^(-m/2) K_{2t}(x)`, equivalently
  `‖D^m K_t(x)‖ ≤ C t^(-(n+m)/2) exp(-‖x‖² / (8t))`, for all `t > 0` and all `x`;
* `‖x‖^α K_t(x) ≤ C t^(α/2) K_{2t}(x)` and `‖D^m K_t(x)‖ ‖x‖^α ≤ C t^((α - m)/2) K_{4t}(x)`
  for `α ≥ 0`;
* `∫ ‖D^m K_t‖ ≤ C t^(-m/2)` and `∫ ‖D^m K_t(x)‖ ‖x‖^α dx ≤ C t^((α - m)/2)` for all `t > 0`;
* `∫ D^m K_t = 0` for `m ≥ 1`.

The constants depend only on `m`, `α` and `E`. In contrast, the constant of the fixed-time bound
`TauCeti.exists_norm_iteratedFDeriv_heatKernel_le` depends on `t`, which is enough to
differentiate a heat convolution at one positive time but not to estimate heat potentials, whose
integrals run over all times down to `0`. The cancellation `∫ D^m K_t = 0` is what allows the
differentiated kernel to act on differences `f(y) - f(x)` in such estimates.

## Main declarations

* `TauCeti.iteratedFDeriv_heatKernel_eq_smul_iteratedFDeriv_heatKernel_one`: parabolic scaling of
  the derivatives.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel`: the bound by
  `C t^(-m/2) K_{2t}(x)`.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_exp`: the bound by
  `C t^(-(n+m)/2) exp(-‖x‖² / (8t))`.
* `TauCeti.exists_norm_rpow_mul_heatKernel_le`: absorbing the weight `‖x‖^α` into `K_{2t}`.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le`: the weighted bound by
  `C t^((α - m)/2) K_{4t}(x)`.
* `TauCeti.integrable_norm_iteratedFDeriv_heatKernel_mul_rpow`: integrability of the weighted
  derivatives.
* `TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_le`: the `L¹` bound.
* `TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le`: the weighted `L¹` bound.
* `TauCeti.integral_iteratedFDeriv_heatKernel_eq_zero`: the cancellation.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Parabolic scaling of the derivatives of the heat kernel.** For `t > 0`,
`D^m K_t(x) = (√t)⁻¹ ^ (n + m) • D^m K_1((√t)⁻¹ • x)` with `n = dim E`: each spatial derivative
costs a factor `t^(-1/2)`. -/
theorem iteratedFDeriv_heatKernel_eq_smul_iteratedFDeriv_heatKernel_one {t : ℝ} (ht : 0 < t)
    (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (heatKernel t) x =
      (√t)⁻¹ ^ (finrank ℝ E + m) • iteratedFDeriv ℝ m (heatKernel 1) ((√t)⁻¹ • x) := by
  have hK : heatKernel t = fun y : E => (√t)⁻¹ ^ finrank ℝ E • heatKernel 1 ((√t)⁻¹ • y) :=
    funext fun y => heatKernel_eq_mul_heatKernel_one_smul ht y
  have hc : ContDiff ℝ m fun y : E => heatKernel 1 ((√t)⁻¹ • y) :=
    (contDiff_heatKernel 1).comp (contDiff_const_smul _)
  rw [hK, iteratedFDeriv_const_smul_apply' hc.contDiffAt,
    iteratedFDeriv_comp_const_smul _ (contDiff_heatKernel 1), smul_smul, pow_add]

/-- **Scale-invariant Gaussian bounds on the derivatives of the heat kernel.** For every order `m`
there is a constant `C`, independent of the time, with `‖D^m K_t(x)‖ ≤ C t^(-m/2) K_{2t}(x)` for
all `t > 0` and all `x`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel (m : ℕ) :
    ∃ C, ∀ t, 0 < t → ∀ x : E,
      ‖iteratedFDeriv ℝ m (heatKernel t) x‖ ≤ C * t ^ (-(m : ℝ) / 2) * heatKernel (2 * t) x := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le (E := E) one_pos m
  simp only [mul_one] at hC
  refine ⟨C, fun t ht x => ?_⟩
  rw [iteratedFDeriv_heatKernel_eq_smul_iteratedFDeriv_heatKernel_one ht, norm_smul,
    norm_of_nonneg (by positivity), ← inv_sqrt_pow_eq_rpow ht.le, mul_comm 2 t,
    heatKernel_mul_eq_mul_heatKernel_smul ht two_pos, pow_add]
  calc (√t)⁻¹ ^ finrank ℝ E * (√t)⁻¹ ^ m * ‖iteratedFDeriv ℝ m (heatKernel 1) ((√t)⁻¹ • x)‖
      ≤ (√t)⁻¹ ^ finrank ℝ E * (√t)⁻¹ ^ m * (C * heatKernel 2 ((√t)⁻¹ • x)) := by
        gcongr
        exact hC _
    _ = C * (√t)⁻¹ ^ m * ((√t)⁻¹ ^ finrank ℝ E * heatKernel 2 ((√t)⁻¹ • x)) := by ring

/-- **Scale-invariant Gaussian bounds on the derivatives of the heat kernel**, in the form
`‖D^m K_t(x)‖ ≤ C t^(-(n+m)/2) exp(-‖x‖² / (8t))` for all `t > 0` and all `x`, with `n = dim E`
and `C` independent of the time. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_exp (m : ℕ) :
    ∃ C, ∀ t, 0 < t → ∀ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖ ≤
      C * t ^ (-((finrank ℝ E : ℝ) + m) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel (E := E) m
  refine ⟨C * (8 * π) ^ (-(finrank ℝ E : ℝ) / 2), fun t ht x => (hC t ht x).trans_eq ?_⟩
  have hπ : 4 * π * (2 * t) = 8 * π * t := by ring
  have h8 : 4 * (2 * t) = 8 * t := by ring
  have hexp : -((finrank ℝ E : ℝ) + m) / 2 = -(m : ℝ) / 2 + -(finrank ℝ E : ℝ) / 2 := by ring
  rw [heatKernel_apply, hπ, h8, mul_rpow (by positivity) ht.le, hexp, rpow_add ht]
  ring

/-- **Scale-invariant polynomial weights.** For `α ≥ 0` there is a constant `C`, independent of
the time, with `‖x‖^α K_t(x) ≤ C t^(α/2) K_{2t}(x)` for all `t > 0` and all `x`. -/
theorem exists_norm_rpow_mul_heatKernel_le {α : ℝ} (hα : 0 ≤ α) :
    ∃ C, ∀ t, 0 < t → ∀ x : E,
      ‖x‖ ^ α * heatKernel t x ≤ C * t ^ (α / 2) * heatKernel (2 * t) x := by
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_heatKernel_le (E := E) one_pos ⌈α⌉₊
  simp only [mul_one] at hC
  refine ⟨C, fun t ht x => ?_⟩
  set y : E := (√t)⁻¹ • x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxα : ‖x‖ ^ α = t ^ (α / 2) * ‖y‖ ^ α := by
    have hx : ‖x‖ = √t * ‖y‖ := by
      rw [norm_smul, norm_inv, norm_of_nonneg (sqrt_nonneg t),
        mul_inv_cancel_left₀ (sqrt_pos.2 ht).ne']
    rw [hx, mul_rpow (sqrt_nonneg t) hy, rpow_div_two_eq_sqrt _ ht.le]
  have hyα : ‖y‖ ^ α ≤ (1 + ‖y‖) ^ ⌈α⌉₊ :=
    calc ‖y‖ ^ α ≤ (1 + ‖y‖) ^ α := rpow_le_rpow hy (by linarith) hα
      _ ≤ (1 + ‖y‖) ^ (⌈α⌉₊ : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil α)
      _ = (1 + ‖y‖) ^ ⌈α⌉₊ := rpow_natCast _ _
  rw [heatKernel_eq_mul_heatKernel_one_smul ht, mul_comm 2 t,
    heatKernel_mul_eq_mul_heatKernel_smul ht two_pos, hxα]
  calc t ^ (α / 2) * ‖y‖ ^ α * ((√t)⁻¹ ^ finrank ℝ E * heatKernel 1 y)
      = t ^ (α / 2) * (√t)⁻¹ ^ finrank ℝ E * (‖y‖ ^ α * heatKernel 1 y) := by ring
    _ ≤ t ^ (α / 2) * (√t)⁻¹ ^ finrank ℝ E * ((1 + ‖y‖) ^ ⌈α⌉₊ * heatKernel 1 y) := by
        gcongr
        exact (heatKernel_pos one_pos y).le
    _ ≤ t ^ (α / 2) * (√t)⁻¹ ^ finrank ℝ E * (C * heatKernel 2 y) :=
        mul_le_mul_of_nonneg_left (hC y) (by positivity)
    _ = C * t ^ (α / 2) * ((√t)⁻¹ ^ finrank ℝ E * heatKernel 2 y) := by ring

/-- **Scale-invariant weighted Gaussian bounds on the derivatives of the heat kernel.** For every
order `m` and every `α ≥ 0` there is a constant `C`, independent of the time, with
`‖D^m K_t(x)‖ ‖x‖^α ≤ C t^((α - m)/2) K_{4t}(x)` for all `t > 0` and all `x`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C, ∀ t, 0 < t → ∀ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖ * ‖x‖ ^ α ≤
      C * t ^ ((α - m) / 2) * heatKernel (4 * t) x := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel (E := E) m
  obtain ⟨C₂, hC₂⟩ := exists_norm_rpow_mul_heatKernel_le (E := E) hα
  have hC₁0 : 0 ≤ C₁ := by
    have h := (norm_nonneg _).trans (hC₁ 1 one_pos 0)
    rw [one_rpow, mul_one] at h
    exact (mul_nonneg_iff_of_pos_right (heatKernel_pos (by norm_num) 0)).1 h
  refine ⟨C₁ * C₂ * 2 ^ (α / 2), fun t ht x => ?_⟩
  have h4 : 2 * (2 * t) = 4 * t := by ring
  have hpow : t ^ (-(m : ℝ) / 2) * (2 * t) ^ (α / 2) = 2 ^ (α / 2) * t ^ ((α - m) / 2) := by
    rw [mul_rpow (by norm_num) ht.le, mul_left_comm, ← rpow_add ht]
    ring_nf
  calc ‖iteratedFDeriv ℝ m (heatKernel t) x‖ * ‖x‖ ^ α
      ≤ C₁ * t ^ (-(m : ℝ) / 2) * heatKernel (2 * t) x * ‖x‖ ^ α := by
        gcongr
        exact hC₁ t ht x
    _ = C₁ * t ^ (-(m : ℝ) / 2) * (‖x‖ ^ α * heatKernel (2 * t) x) := by ring
    _ ≤ C₁ * t ^ (-(m : ℝ) / 2) * (C₂ * (2 * t) ^ (α / 2) * heatKernel (2 * (2 * t)) x) :=
        mul_le_mul_of_nonneg_left (hC₂ (2 * t) (by positivity) x) (by positivity)
    _ = C₁ * C₂ * (t ^ (-(m : ℝ) / 2) * (2 * t) ^ (α / 2)) * heatKernel (2 * (2 * t)) x := by
        ring
    _ = _ := by rw [hpow, h4]; ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For `t > 0` and `α ≥ 0`, the weighted derivative `x ↦ ‖D^m K_t(x)‖ ‖x‖^α` of the heat kernel
is integrable. -/
theorem integrable_norm_iteratedFDeriv_heatKernel_mul_rpow {t : ℝ} (ht : 0 < t) (m : ℕ) {α : ℝ}
    (hα : 0 ≤ α) :
    Integrable fun x : E => ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x‖ * ‖x‖ ^ α := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m hα
  refine ((integrable_heatKernel (by positivity : 0 < 4 * t)).const_mul
    (C * t ^ ((α - m) / 2))).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (((contDiff_heatKernel (k := ⊤) t).continuous_iteratedFDeriv le_top).norm.mul
      (continuous_norm.rpow_const fun _ => Or.inr hα)).aestronglyMeasurable
  · rw [norm_of_nonneg (by positivity)]
    exact hC t ht x

/-- **Weighted `L¹` bounds on the derivatives of the heat kernel.** For every order `m` and every
`α ≥ 0` there is a constant `C`, independent of the time, with
`∫ ‖D^m K_t(x)‖ ‖x‖^α dx ≤ C t^((α - m)/2)` for all `t > 0`. Combined with the cancellation
`∫ D^m K_t = 0`, this is the kernel estimate behind Hölder bounds for heat convolutions. -/
theorem exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C, ∀ t, 0 < t →
      ∫ x, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x‖ * ‖x‖ ^ α ≤ C * t ^ ((α - m) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m hα
  refine ⟨C, fun t ht => ?_⟩
  have h4t : 0 < 4 * t := by positivity
  calc ∫ x, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x‖ * ‖x‖ ^ α
      ≤ ∫ x, C * t ^ ((α - m) / 2) * heatKernel (4 * t) x :=
        integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
          ((integrable_heatKernel h4t).const_mul _) (ae_of_all _ (hC t ht))
    _ = C * t ^ ((α - m) / 2) := by rw [integral_const_mul, integral_heatKernel h4t, mul_one]

/-- **`L¹` bounds on the derivatives of the heat kernel.** For every order `m` there is a constant
`C`, independent of the time, with `∫ ‖D^m K_t‖ ≤ C t^(-m/2)` for all `t > 0`. -/
theorem exists_integral_norm_iteratedFDeriv_heatKernel_le (m : ℕ) :
    ∃ C, ∀ t, 0 < t →
      ∫ x, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x‖ ≤ C * t ^ (-(m : ℝ) / 2) := by
  simpa using exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m le_rfl

/-- **Cancellation of the derivatives of the heat kernel.** For `m ≥ 1` and `t > 0`,
`∫ D^m K_t = 0`. -/
theorem integral_iteratedFDeriv_heatKernel_eq_zero {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : m ≠ 0) :
    ∫ x, iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hg : Differentiable ℝ (iteratedFDeriv ℝ k (heatKernel t : E → ℝ)) :=
    (contDiff_heatKernel (k := ⊤) t).differentiable_iteratedFDeriv (WithTop.coe_lt_top _)
  have hint (j : ℕ) (w : Fin j → E) :
      Integrable fun x => iteratedFDeriv ℝ j (heatKernel t : E → ℝ) x w :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) ℝ w).integrable_comp
      (integrable_iteratedFDeriv_heatKernel ht j)
  ext v
  rw [ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv_heatKernel ht _),
    zero_apply]
  -- `D^(k+1) K_t(x) v` is the derivative of `h = D^k K_t(·) (tail v)` at `x` in the direction
  -- `v 0`, and integrating by parts against the constant `1` shows that its integral vanishes.
  set h : E → ℝ := fun y => iteratedFDeriv ℝ k (heatKernel t) y (Fin.tail v)
  have hD (x : E) : iteratedFDeriv ℝ (k + 1) (heatKernel t) x v = fderiv ℝ h x (v 0) := by
    rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply (hg x)]
  have := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun _ : E => (1 : ℝ)) (g := h) (v := v 0) (by simp)
    ((hint (k + 1) v).congr (Filter.Eventually.of_forall fun x => by simp [hD]))
    (by simpa using hint k (Fin.tail v)) (fun _ _ => differentiableAt_const _)
    (fun x _ => (hg x).continuousMultilinear_apply_const _)
  simpa [hD] using this

end TauCeti
