/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Analysis.Calculus.GaussianDecay
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import TauCeti.Analysis.PDE.HeatKernel.Bounds

/-!
# Scale-invariant bounds on the space-time derivatives of the heat kernel

On a finite-dimensional real inner product space `E` of dimension `n`, the heat kernel
`K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` has the parabolic scaling
`D^m K_t(x) = t^(-(n + m) / 2) D^m K_1(t^(-1/2) x)`. This file turns that scaling into estimates
whose constants do not depend on the time, as needed for the Hölder estimates of heat potentials:

* for all orders `j` in time and `m` in space,
  `‖∂ₜ^j D^m K_t(x)‖ ≤ C t^(-(n + m + 2j) / 2) exp(-‖x‖² / (8t))` for all `t > 0`;
* equivalently for `j = 0`, `‖D^m K_t(x)‖ ≤ C t^(-m / 2) K_{2t}(x)`;
* `‖D^m K_t(x)‖ ‖x‖^α ≤ C t^((α - m) / 2) K_{4t}(x)` for `α ≥ 0`;
* consequently `∫ ‖D^m K_t(x)‖ ‖x‖^α dx ≤ C t^((α - m) / 2)`, in particular
  `∫ ‖D^m K_t‖ ≤ C t^(-m / 2)`;
* `∫ D^m K_t = 0` for `m ≥ 1`.

Every time derivative of `D^m K_s(x)` at `s = t` again has the scaling form `s^(-b) Ψ(s^(-1/2) x)`
for a profile `Ψ` all of whose derivatives decay like `exp(-‖y‖² / 8)`, so the time bound
reduces to a bound on the profile. The vanishing integral follows by integrating by parts against
the constant function `1`.

## Main declarations

* `TauCeti.iteratedFDeriv_heatKernel_eq_rpow_smul`: parabolic scaling of the derivatives.
* `TauCeti.exists_norm_iteratedDeriv_iteratedFDeriv_heatKernel_le`: Gaussian bounds on the
  space-time derivatives.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_le_rpow_mul_exp`: the case of spatial
  derivatives.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel`: the bound by
  `C t^(-m / 2) K_{2t}(x)`.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le`: the weighted bound by
  `C t^((α - m) / 2) K_{4t}(x)`.
* `TauCeti.integrable_norm_iteratedFDeriv_heatKernel_mul_rpow`: integrability of the weighted
  derivatives.
* `TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le`: the weighted `L¹` bound.
* `TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_le`: the `L¹` bound.
* `TauCeti.integral_iteratedFDeriv_heatKernel_eq_zero`: the derivatives have integral zero.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1 (Gaussian bounds on
  the derivatives of the fundamental solution).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Chapter 4 (weighted kernel estimates for
  heat potentials).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Real
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Parabolic scaling of the derivatives of the heat kernel.** For `t > 0`,
`D^m K_t(x) = t^(-(n + m) / 2) D^m K_1(t^(-1/2) x)`, where `n = dim E`. -/
theorem iteratedFDeriv_heatKernel_eq_rpow_smul {t : ℝ} (ht : 0 < t) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (heatKernel t) x = t ^ (-(finrank ℝ E + m : ℝ) / 2) •
      iteratedFDeriv ℝ m (heatKernel 1) (t ^ (-1 / 2 : ℝ) • x) := by
  have hc : (√t)⁻¹ = t ^ (-1 / 2 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_neg ht.le]
    norm_num
  have hK : heatKernel t =
      fun y : E => (t ^ (-1 / 2 : ℝ)) ^ finrank ℝ E • heatKernel 1 (t ^ (-1 / 2 : ℝ) • y) :=
    funext fun y => by rw [heatKernel_eq_mul_heatKernel_one_smul ht y, hc, smul_eq_mul]
  have hsmooth : ContDiffAt ℝ m (fun y : E => heatKernel 1 (t ^ (-1 / 2 : ℝ) • y)) x :=
    ((contDiff_heatKernel 1).comp (contDiff_const_smul _)).contDiffAt
  rw [hK, iteratedFDeriv_const_smul_apply' hsmooth,
    iteratedFDeriv_comp_const_smul _ (contDiff_heatKernel 1), smul_smul, ← pow_add,
    ← rpow_natCast, ← rpow_mul ht.le]
  congr 2
  push_cast
  ring

section TimeDerivatives

/-! ### Time derivatives

By parabolic scaling, `D^m K_s(x) = s^(-a) Ψ(s^(-1/2) x)` with `a = (n + m) / 2` and
`Ψ = D^m K_1`. Differentiating such an expression in `s` gives one of the same shape,
`s^(-(a + 1)) Ψ'(s^(-1/2) x)` with `Ψ'(y) = -a Ψ(y) - (1/2) DΨ(y) y`. Since `Ψ` has Gaussian
decay at rate `1 / 8` and that class is closed under `Ψ ↦ Ψ'`
(`exists_gaussianDecay_iteratedDeriv_rpow_smul`), every time derivative has a Gaussian bound. -/

/-- The derivatives of `K_1` have Gaussian decay at rate `1 / 8`. -/
private theorem gaussianDecay_iteratedFDeriv_heatKernel_one (m : ℕ) :
    GaussianDecay (1 / 8) (iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ)) := by
  refine ⟨(contDiff_heatKernel 1 (k := ω)).iteratedFDeriv_right le_top, fun i p => ?_⟩
  obtain ⟨C, -, hC⟩ :=
    exists_one_add_norm_pow_mul_norm_iteratedFDeriv_heatKernel_le (E := E) one_pos (i + m) p
  refine ⟨C * (4 * π * 2) ^ (-(finrank ℝ E : ℝ) / 2), fun y => ?_⟩
  rw [norm_iteratedFDeriv_iteratedFDeriv]
  calc (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ (i + m) (heatKernel 1) y‖
      ≤ C * heatKernel (2 * 1) y := hC y
    _ = _ := by
        rw [mul_one, heatKernel_apply]
        ring_nf

/-- **Gaussian bounds on the space-time derivatives of the heat kernel.** For all orders `j` in
time and `m` in space there is a constant `C`, independent of the time, such that
`‖∂ₜ^j D^m K_t(x)‖ ≤ C t^(-(n + m + 2j) / 2) exp(-‖x‖² / (8t))` for all `t > 0` and all `x`,
where `n = dim E`. -/
theorem exists_norm_iteratedDeriv_iteratedFDeriv_heatKernel_le (j m : ℕ) :
    ∃ C, ∀ t, 0 < t → ∀ x : E,
      ‖iteratedDeriv j (fun s => iteratedFDeriv ℝ m (heatKernel s) x) t‖ ≤
        C * t ^ (-(finrank ℝ E + m + 2 * j : ℝ) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) := by
  obtain ⟨Φ, hΦ, hj⟩ := exists_gaussianDecay_iteratedDeriv_rpow_smul j
    ((finrank ℝ E + m : ℝ) / 2) (gaussianDecay_iteratedFDeriv_heatKernel_one (E := E) m)
  obtain ⟨C, hC⟩ := hΦ.exists_bound 0 0
  refine ⟨C, fun t ht x => ?_⟩
  have heq : (fun s => iteratedFDeriv ℝ m (heatKernel s) x) =ᶠ[nhds t]
      fun s => s ^ (-((finrank ℝ E + m : ℝ) / 2)) •
        iteratedFDeriv ℝ m (heatKernel 1) (s ^ (-1 / 2 : ℝ) • x) :=
    (eventually_gt_nhds ht).mono fun s hs => by
      simp only [iteratedFDeriv_heatKernel_eq_rpow_smul hs, neg_div]
  have htwo : (-1 / 2 : ℝ) * (2 : ℕ) = -1 := by norm_num
  have hexp : -(1 / 8) * ‖t ^ (-1 / 2 : ℝ) • x‖ ^ 2 = -‖x‖ ^ 2 / (8 * t) := by
    rw [norm_smul, norm_of_nonneg (by positivity), mul_pow, ← rpow_natCast, ← rpow_mul ht.le,
      htwo, rpow_neg_one]
    field_simp
  have hΦx := hC (t ^ (-1 / 2 : ℝ) • x)
  rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, hexp] at hΦx
  have hpow :
      t ^ (-((finrank ℝ E + m : ℝ) / 2 + j)) = t ^ (-(finrank ℝ E + m + 2 * j : ℝ) / 2) := by
    congr 1
    ring
  rw [heq.iteratedDeriv_eq, hj x t ht, norm_smul, norm_of_nonneg (by positivity), hpow]
  calc t ^ (-(finrank ℝ E + m + 2 * j : ℝ) / 2) * ‖Φ (t ^ (-1 / 2 : ℝ) • x)‖
      ≤ t ^ (-(finrank ℝ E + m + 2 * j : ℝ) / 2) * (C * exp (-‖x‖ ^ 2 / (8 * t))) :=
        mul_le_mul_of_nonneg_left hΦx (by positivity)
    _ = _ := by ring

end TimeDerivatives

/-- **Scale-invariant Gaussian bounds on the derivatives of the heat kernel.** For every order
`m` there is a constant `C`, independent of the time, such that
`‖D^m K_t(x)‖ ≤ C t^(-(n + m) / 2) exp(-‖x‖² / (8t))` for all `t > 0` and all `x`, where
`n = dim E`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le_rpow_mul_exp (m : ℕ) :
    ∃ C, ∀ t, 0 < t → ∀ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖ ≤
      C * t ^ (-(finrank ℝ E + m : ℝ) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) := by
  simpa using exists_norm_iteratedDeriv_iteratedFDeriv_heatKernel_le (E := E) 0 m

/-- **Scale-invariant Gaussian bounds on the derivatives of the heat kernel**, against the heat
kernel at the doubled time. For every order `m` there is a constant `C > 0`, independent of the
time, such that `‖D^m K_t(x)‖ ≤ C t^(-m / 2) K_{2t}(x)` for all `t > 0` and all `x`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel (m : ℕ) :
    ∃ C > 0, ∀ t, 0 < t → ∀ x : E,
      ‖iteratedFDeriv ℝ m (heatKernel t) x‖ ≤ C * t ^ (-(m : ℝ) / 2) * heatKernel (2 * t) x := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le_rpow_mul_exp (E := E) m
  refine ⟨max C 1 * (8 * π) ^ ((finrank ℝ E : ℝ) / 2), by positivity, fun t ht x => ?_⟩
  -- The Gaussian `exp(-‖x‖² / (8t))` is `(8πt)^(n/2) K_{2t}(x)`.
  have hG : exp (-‖x‖ ^ 2 / (8 * t)) =
      (8 * π * t) ^ ((finrank ℝ E : ℝ) / 2) * heatKernel (2 * t) x := by
    have hc : 4 * π * (2 * t) = 8 * π * t := by ring
    have he : -‖x‖ ^ 2 / (4 * (2 * t)) = -‖x‖ ^ 2 / (8 * t) := by ring
    rw [heatKernel_apply, ← mul_assoc, hc, he, neg_div (2 : ℝ),
      rpow_neg (by positivity), mul_inv_cancel₀ (by positivity), one_mul]
  have hexp : t ^ (-(finrank ℝ E + m : ℝ) / 2) * t ^ ((finrank ℝ E : ℝ) / 2) =
      t ^ (-(m : ℝ) / 2) := by
    rw [← rpow_add ht]
    congr 1
    ring
  calc ‖iteratedFDeriv ℝ m (heatKernel t) x‖
      ≤ C * t ^ (-(finrank ℝ E + m : ℝ) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) := hC t ht x
    _ ≤ max C 1 * t ^ (-(finrank ℝ E + m : ℝ) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) := by
        gcongr
        exact le_max_left C 1
    _ = _ := by
        rw [hG, mul_rpow (by positivity) ht.le, ← hexp]
        ring

/-- **Scale-invariant weighted Gaussian bounds on the derivatives of the heat kernel.** For every
order `m` and every `α ≥ 0` there is a constant `C > 0`, independent of the time, with
`‖D^m K_t(x)‖ ‖x‖^α ≤ C t^((α - m)/2) K_{4t}(x)` for all `t > 0` and all `x`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C > 0, ∀ t, 0 < t → ∀ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖ * ‖x‖ ^ α ≤
      C * t ^ ((α - m) / 2) * heatKernel (4 * t) x := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_norm_iteratedFDeriv_heatKernel_le_mul_rpow_mul_heatKernel (E := E) m
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_rpow_mul_heatKernel_le (E := E) hα
  refine ⟨C₁ * C₂ * 2 ^ (α / 2), by positivity, fun t ht x => ?_⟩
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
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m hα
  refine ((integrable_heatKernel (by positivity : 0 < 4 * t)).const_mul
    (C * t ^ ((α - m) / 2))).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (((contDiff_heatKernel (k := ⊤) t).continuous_iteratedFDeriv le_top).norm.mul
      (continuous_norm.rpow_const fun _ => Or.inr hα)).aestronglyMeasurable
  · rw [norm_of_nonneg (by positivity)]
    exact hC t ht x

/-- **Weighted `L¹` bounds on the derivatives of the heat kernel.** For every order `m` and every
`α ≥ 0` there is a constant `C > 0`, independent of the time, with
`∫ ‖D^m K_t(x)‖ ‖x‖^α dx ≤ C t^((α - m)/2)` for all `t > 0`. Combined with the cancellation
`∫ D^m K_t = 0`, this is the kernel estimate behind Hölder bounds for heat convolutions. -/
theorem exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C > 0, ∀ t, 0 < t →
      ∫ x, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x‖ * ‖x‖ ^ α ≤ C * t ^ ((α - m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m hα
  refine ⟨C, hC0, fun t ht => ?_⟩
  have h4t : 0 < 4 * t := by positivity
  calc ∫ x, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x‖ * ‖x‖ ^ α
      ≤ ∫ x, C * t ^ ((α - m) / 2) * heatKernel (4 * t) x :=
        integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
          ((integrable_heatKernel h4t).const_mul _) (ae_of_all _ (hC t ht))
    _ = C * t ^ ((α - m) / 2) := by rw [integral_const_mul, integral_heatKernel h4t, mul_one]


/-- **Scale-invariant `L¹` bounds on the derivatives of the heat kernel.** For every order `m`
there is a constant `C`, independent of the time, such that `‖D^m K_t‖_{L¹} ≤ C t^(-m / 2)` for
all `t > 0`. -/
theorem exists_integral_norm_iteratedFDeriv_heatKernel_le (m : ℕ) :
    ∃ C, ∀ t, 0 < t → ∫ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖ ≤ C * t ^ (-(m : ℝ) / 2) := by
  obtain ⟨C, -, hC⟩ := exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m le_rfl
  exact ⟨C, fun t ht => by simpa using hC t ht⟩

/-- **The derivatives of the heat kernel have integral zero.** For every order `m ≥ 1` and every
`t > 0`, `∫ D^m K_t = 0`. -/
@[simp]
theorem integral_iteratedFDeriv_heatKernel_eq_zero {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : m ≠ 0) :
    ∫ x : E, iteratedFDeriv ℝ m (heatKernel t) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hD := contDiff_heatKernel (E := E) t (k := ⊤)
  ext v
  rw [ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv_heatKernel ht (k + 1)),
    zero_apply]
  -- `D^(k+1) K_t(x) v` is the derivative in the direction `v 0` of `y ↦ D^k K_t(y) (tail v)`.
  set h : E → ℝ := fun y => iteratedFDeriv ℝ k (heatKernel t) y (Fin.tail v)
  have hh : Differentiable ℝ h := fun y =>
    (hD.differentiable_iteratedFDeriv (WithTop.coe_lt_top _) y).continuousMultilinear_apply_const _
  have hderiv : ∀ x, iteratedFDeriv ℝ (k + 1) (heatKernel t) x v = fderiv ℝ h x (v 0) := fun x =>
    (hD.differentiable_iteratedFDeriv (WithTop.coe_lt_top _) x).iteratedFDeriv_succ_apply_left'
  have hint : ∀ m, Integrable fun x => iteratedFDeriv ℝ m (heatKernel t : E → ℝ) x := fun m =>
    integrable_iteratedFDeriv_heatKernel ht m
  simp only [hderiv]
  simpa using integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (f := fun _ : E => (1 : ℝ))
    (g := h) (v := v 0) (by simp)
    (by simpa [← hderiv] using
      (ContinuousMultilinearMap.apply ℝ _ ℝ v).integrable_comp (hint (k + 1)))
    (by simpa using (ContinuousMultilinearMap.apply ℝ _ ℝ (Fin.tail v)).integrable_comp (hint k))
    (fun x _ => differentiableAt_const _) (fun x _ => hh x)

end TauCeti
