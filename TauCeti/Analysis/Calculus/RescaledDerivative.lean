/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rescaled derivative limits

This file records the normed-space limit obtained by sampling a differentiable map at `t / n`
and multiplying its value by `n`. The scalar field has characteristic zero and continuous
nonnegative-rational scalar multiplication, so `t / n` tends to zero. These assumptions hold
for both real and complex scalars.

## Main result

* `tendsto_nsmul_apply_div_of_hasDerivAt`: a map sending zero to zero with derivative `f'` satisfies
  `n • f (t / n) → t • f'`.
-/

public section

open Filter

/-- If `f` passes through zero with derivative `f'`, then `n • f (t / n)` tends to `t • f'`. -/
theorem tendsto_nsmul_apply_div_of_hasDerivAt
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {f' : F} (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) (t : 𝕜) :
    Tendsto (fun n : ℕ => n • f (t / n)) atTop (nhds (t • f')) := by
  have hscaled : Tendsto (fun n : ℕ => (n : 𝕜) • (t / n)) atTop (nhds t) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
    simp [smul_eq_mul, mul_div_cancel₀, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)]
  simpa [hf0, Nat.cast_smul_eq_nsmul] using
    hf.hasFDerivAt.hasFDerivWithinAt (s := Set.univ) |>.lim
      (tendsto_const_div_atTop_nhds_zero_nat t) (Eventually.of_forall fun _ => Set.mem_univ _)
      hscaled

end
