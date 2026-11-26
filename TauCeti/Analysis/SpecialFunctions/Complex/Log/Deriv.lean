/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Derivatives of the complex logarithm

This file records the derivative of a logarithm with a scaled argument on its slit domain, the
first two derivatives of `u * log` on `Complex.slitPlane`, and the smoothness and higher
derivatives along the real parameter `t : ℝ` of the shifted principal complex logarithm
`t ↦ Complex.log ((t : ℂ) + z)` whenever `(u : ℂ) + z` lies in `Complex.slitPlane`.

## Main results

* `Complex.hasDerivAt_log_div_const`: the derivative of `w ↦ log (w / c)` is `z⁻¹` on the
  resulting slit domain.
* `Complex.deriv_mul_log`, `Complex.deriv_deriv_mul_log`: at a point of `Complex.slitPlane`, the
  first two derivatives of `u * log` are `u' log + u / z` and `u'' log + 2 u' / z - u / z²`.
* `Complex.contDiffAt_log_ofReal_add`: arbitrary-order real smoothness of `t ↦ Complex.log (t + z)`
  at `u : ℝ` when `(u : ℂ) + z ∈ Complex.slitPlane`.
* `Complex.iteratedDeriv_log_ofReal_add`: for `k ≥ 1` and `(u : ℂ) + z ∈ Complex.slitPlane`,
  `iteratedDeriv k (fun t : ℝ ↦ Complex.log ((t : ℂ) + z)) u = (-1)^(k - 1) * (k - 1)! / (u + z)^k`.
-/

public section

open Filter Topology
open scoped ContDiff Nat

namespace Complex

/-- The derivative of the logarithm of `z / c` is `z⁻¹` on the resulting slit domain. -/
theorem hasDerivAt_log_div_const (z : ℂ) {c : ℂ} (hz : z / c ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ log (w / c)) z⁻¹ z := by
  obtain ⟨hz0, hc⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hz)
  have h : HasDerivAt (fun w : ℂ ↦ w / c) (1 / c) z :=
    (hasDerivAt_id z).div_const c
  convert h.clog hz using 1
  field_simp [hc, hz0]

/-- At a point `z` of the slit plane at which `u` is differentiable, the derivative of `u * log`
is `u' log + u / z`. -/
theorem deriv_mul_log {u : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℂ u z) (hz : z ∈ slitPlane) :
    deriv (fun y ↦ u y * log y) z = deriv u z * log z + u z * z⁻¹ :=
  (hu.hasDerivAt.mul (hasDerivAt_log hz)).deriv

/-- At a point `z` of the slit plane near which `u` is differentiable and at which `u'` is
differentiable, the second derivative of `u * log` is `u'' log + 2 u' / z - u / z²`. -/
theorem deriv_deriv_mul_log {u : ℂ → ℂ} {z : ℂ} (hu : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ u y)
    (hu' : DifferentiableAt ℂ (deriv u) z) (hz : z ∈ slitPlane) :
    deriv (deriv fun y ↦ u y * log y) z =
      deriv (deriv u) z * log z + 2 * deriv u z * z⁻¹ - u z * (z ^ 2)⁻¹ := by
  have hev : deriv (fun y ↦ u y * log y) =ᶠ[𝓝 z] fun y ↦ deriv u y * log y + u y * y⁻¹ :=
    (hu.and (isOpen_slitPlane.mem_nhds hz)).mono fun y hy ↦ deriv_mul_log hy.1 hy.2
  have hd := (hu'.hasDerivAt.fun_mul (hasDerivAt_log hz)).fun_add
    (hu.self_of_nhds.hasDerivAt.fun_mul (hasDerivAt_inv (slitPlane_ne_zero hz)))
  rw [hev.deriv_eq, hd.deriv]
  ring

/-- For `(u : ℂ) + z ∈ Complex.slitPlane`, the shifted principal logarithm `t ↦ log (t + z)` is
smooth of arbitrary order at `u : ℝ`. -/
theorem contDiffAt_log_ofReal_add {u : ℝ} {z : ℂ} (h : (u : ℂ) + z ∈ slitPlane)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun t : ℝ ↦ log ((t : ℂ) + z)) u := by
  have hlin : ContDiffAt ℝ n (fun t : ℝ ↦ (t : ℂ) + z) u :=
    ofRealCLM.contDiff.contDiffAt.add contDiffAt_const
  exact ((contDiffAt_log h).restrict_scalars ℝ).comp u hlin

/-- For `k ≥ 1` and `(u : ℂ) + z ∈ Complex.slitPlane`, the `k`-th derivative of `t ↦ log (t + z)`
at `u : ℝ` is `(-1) ^ (k - 1) * (k - 1)! / (u + z) ^ k`. -/
theorem iteratedDeriv_log_ofReal_add {k : ℕ} (hk : 1 ≤ k) {u : ℝ} {z : ℂ}
    (h : (u : ℂ) + z ∈ slitPlane) :
    iteratedDeriv k (fun t : ℝ ↦ log ((t : ℂ) + z)) u =
      (-1 : ℂ) ^ (k - 1) * ((k - 1)! : ℂ) / ((u : ℂ) + z) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hU : IsOpen {w : ℂ | w + z ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_id.add continuous_const)
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ log (w + z)) {w : ℂ | w + z ∈ slitPlane} :=
    fun w hw ↦ ((hasDerivAt_log hw).comp_add_const w z).differentiableAt.differentiableWithinAt
  simp only [hf.iteratedDeriv_comp_ofReal hU (m + 1) h, iteratedDeriv_comp_add_const,
    _root_.iteratedDeriv_succ_log h, Nat.add_sub_cancel]
  have hexp : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, div_eq_mul_inv]

end Complex
