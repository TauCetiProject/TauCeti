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
* consequently `∫ ‖D^m K_t‖ ≤ C t^(-m / 2)`;
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
* `TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_le`: the `L¹` bound.
* `TauCeti.integral_iteratedFDeriv_heatKernel_eq_zero`: the derivatives have integral zero.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1 (Gaussian bounds on
  the derivatives of the fundamental solution).
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
  obtain ⟨C, hC⟩ :=
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

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Scale-invariant `L¹` bounds on the derivatives of the heat kernel.** For every order `m`
there is a constant `C`, independent of the time, such that `‖D^m K_t‖_{L¹} ≤ C t^(-m / 2)` for
all `t > 0`. -/
theorem exists_integral_norm_iteratedFDeriv_heatKernel_le (m : ℕ) :
    ∃ C, ∀ t, 0 < t → ∫ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖ ≤ C * t ^ (-(m : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le_rpow_mul_exp (E := E) m
  refine ⟨C * (8 * π) ^ ((finrank ℝ E : ℝ) / 2), fun t ht => ?_⟩
  -- The Gaussian `exp(-‖x‖² / (8t))` is `(8πt)^(n/2) K_{2t}(x)`, of integral `(8πt)^(n/2)`.
  have hG : ∀ x : E, exp (-‖x‖ ^ 2 / (8 * t)) =
      (8 * π * t) ^ ((finrank ℝ E : ℝ) / 2) * heatKernel (2 * t) x := fun x => by
    have hc : 4 * π * (2 * t) = 8 * π * t := by ring
    have he : -‖x‖ ^ 2 / (4 * (2 * t)) = -‖x‖ ^ 2 / (8 * t) := by ring
    rw [heatKernel_apply, ← mul_assoc, hc, he, neg_div (2 : ℝ),
      rpow_neg (by positivity), mul_inv_cancel₀ (by positivity), one_mul]
  have h2t : 0 < 2 * t := by positivity
  calc ∫ x : E, ‖iteratedFDeriv ℝ m (heatKernel t) x‖
      ≤ ∫ x : E, C * t ^ (-(finrank ℝ E + m : ℝ) / 2) *
          ((8 * π * t) ^ ((finrank ℝ E : ℝ) / 2) * heatKernel (2 * t) x) := by
        refine integral_mono (integrable_iteratedFDeriv_heatKernel ht m).norm
          (((integrable_heatKernel h2t).const_mul _).const_mul _) fun x => ?_
        simpa only [hG] using hC t ht x
    _ = C * (8 * π) ^ ((finrank ℝ E : ℝ) / 2) * t ^ (-(m : ℝ) / 2) := by
        have hexp : t ^ (-(finrank ℝ E + m : ℝ) / 2) * t ^ ((finrank ℝ E : ℝ) / 2) =
            t ^ (-(m : ℝ) / 2) := by
          rw [← rpow_add ht]
          congr 1
          ring
        rw [integral_const_mul, integral_const_mul, integral_heatKernel h2t, mul_one,
          mul_rpow (by positivity) ht.le, ← hexp]
        ring

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
