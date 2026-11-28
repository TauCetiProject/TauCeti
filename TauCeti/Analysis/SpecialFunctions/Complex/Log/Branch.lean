/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The centered complex logarithm branch

For any `a : ℂ`, the branch `Complex.logBranch a v = a + Complex.log (v / Complex.exp a)`
centred at `a` inverts `Complex.exp` on the strip `-π < (w - a).im ≤ π`
(`Complex.logBranch_exp`) and is `C^n` (over `ℂ`, hence holomorphic) wherever
`v / Complex.exp a ∈ Complex.slitPlane` (`Complex.contDiffAt_logBranch`). Specializing at
`a = Complex.log z₀` for `z₀ ≠ 0` gives the centered branch
`z ↦ Complex.log z₀ + Complex.log (z / z₀)`, which avoids the principal branch cut near `z₀`
(`Complex.contDiffAt_log_add_log_div`).

## Main declarations

* `Complex.logBranch`: the branch of the logarithm centred at `a`.
* `Complex.logBranch_exp`: `Complex.logBranch a` inverts `Complex.exp` on `-π < (w - a).im ≤ π`.
* `Complex.contDiffAt_logBranch`: `Complex.logBranch a` is `C^n` where `v / exp a ∈ slitPlane`.
* `Complex.contDiffAt_log_add_log_div`: the centered logarithm branch is `C^n` at `z₀ ≠ 0`.
-/

public section

namespace Complex

/-- The branch of the logarithm **based at `a`**: the translate of Mathlib's principal branch that
takes the value `a` at the point `Complex.exp a`, its branch cut rotated away from there. -/
noncomputable def logBranch (a v : ℂ) : ℂ := a + log (v / exp a)

/-- The defining formula for the centered logarithm branch `Complex.logBranch`. -/
theorem logBranch_apply (a v : ℂ) : logBranch a v = a + log (v / exp a) := (rfl)

/-- **The branch based at `a` inverts `Complex.exp`** on the strip of height `2 π` centred at `a`,
because `Complex.log_exp` inverts it on `-π < im ≤ π`. -/
theorem logBranch_exp {a w : ℂ} (h₁ : -Real.pi < (w - a).im) (h₂ : (w - a).im ≤ Real.pi) :
    logBranch a (exp w) = w := by
  rw [logBranch, ← exp_sub, log_exp h₁ h₂]
  ring

/-- The branch `Complex.logBranch a` of the logarithm centred at `a` is `C^n` (over `ℂ`, hence
holomorphic) wherever `v / exp a` lies in the slit plane. -/
theorem contDiffAt_logBranch {a v : ℂ} (h : v / exp a ∈ slitPlane) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (logBranch a) v :=
  contDiffAt_const.add ((contDiffAt_log h).comp v (contDiffAt_id.div_const _))

/-- The centered branch `z ↦ log z₀ + log (z / z₀)` is `C^n` (over `ℂ`, hence holomorphic) at any
nonzero `z₀`, even when `z₀` lies on the principal branch cut. -/
theorem contDiffAt_log_add_log_div {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (fun z : ℂ ↦ log z₀ + log (z / z₀)) z₀ := by
  rw [show (fun z : ℂ ↦ log z₀ + log (z / z₀)) = logBranch (log z₀) from
    funext fun z ↦ by rw [logBranch_apply, exp_log hz₀]]
  exact contDiffAt_logBranch (by rw [exp_log hz₀, div_self hz₀]; exact one_mem_slitPlane)

end Complex
