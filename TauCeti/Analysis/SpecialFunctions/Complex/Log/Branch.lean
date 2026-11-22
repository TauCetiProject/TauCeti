/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Regularity and right-inverse law of the centered complex logarithm branch

For any `a : ℂ`, the branch `v ↦ a + Complex.log (v / Complex.exp a)` centred at `a` is `C^n`
(over `ℂ`, hence holomorphic) wherever `v / Complex.exp a ∈ Complex.slitPlane`
(`Complex.contDiffAt_logBranch`). Specializing at `a = Complex.log z₀` for `z₀ ≠ 0` gives the
centered branch `z ↦ Complex.log z₀ + Complex.log (z / z₀)`, which avoids the principal branch cut
near `z₀` (`Complex.contDiffAt_log_add_log_div`) and satisfies `exp (log z₀ + log (z / z₀)) = z`
for every `z ≠ 0` (`Complex.exp_log_add_log_div`).

## Main declarations

* `Complex.exp_log_add_log_div`: `exp (log z₀ + log (z / z₀)) = z` for nonzero `z₀` and `z`.
* `Complex.contDiffAt_logBranch`: `v ↦ a + log (v / exp a)` is `C^n` where `v / exp a ∈ slitPlane`.
* `Complex.contDiffAt_log_add_log_div`: the centered logarithm branch is `C^n` at `z₀ ≠ 0`.
-/

public section

namespace Complex

/-- The centered branch `z ↦ log z₀ + log (z / z₀)` satisfies `exp (log z₀ + log (z / z₀)) = z`
for all nonzero `z₀` and `z`. -/
theorem exp_log_add_log_div {z₀ z : ℂ} (hz₀ : z₀ ≠ 0) (hz : z ≠ 0) :
    exp (log z₀ + log (z / z₀)) = z := by
  rw [exp_add, exp_log hz₀, exp_log (div_ne_zero hz hz₀), mul_div_cancel₀ _ hz₀]

/-- The branch `v ↦ a + log (v / exp a)` of the logarithm centred at `a` is `C^n` (over `ℂ`, hence
holomorphic) wherever `v / exp a` lies in the slit plane. -/
theorem contDiffAt_logBranch {a v : ℂ} (h : v / exp a ∈ slitPlane) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (fun z : ℂ ↦ a + log (z / exp a)) v :=
  contDiffAt_const.add ((contDiffAt_log h).comp v (contDiffAt_id.div_const _))

/-- The centered branch `z ↦ log z₀ + log (z / z₀)` is `C^n` (over `ℂ`, hence holomorphic) at any
nonzero `z₀`, even when `z₀` lies on the principal branch cut. -/
theorem contDiffAt_log_add_log_div {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (fun z : ℂ ↦ log z₀ + log (z / z₀)) z₀ := by
  simpa only [exp_log hz₀] using
    contDiffAt_logBranch (a := log z₀) (by rw [exp_log hz₀, div_self hz₀]; exact one_mem_slitPlane)

end Complex
