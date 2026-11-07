/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric series for the Herglotz–Riesz and Poisson kernels

When the pole `w` is strictly closer to the center `c` than the boundary point `z`, the
Herglotz–Riesz kernel `((z - c) + (w - c)) / ((z - c) - (w - c))` is a geometric series in the
ratio `q = (w - c) / (z - c)`:

`herglotzRieszKernel c w z = 1 + 2 * ∑ n ≥ 1, q ^ n`.

Taking real parts gives the corresponding expansion of the Poisson kernel. On the unit circle,
with `w = r * exp (i * φ)` and `z = exp (i * θ)`, this is the classical Fourier series

`(1 - r ^ 2) / (1 + r ^ 2 - 2 * r * cos (θ - φ)) = 1 + 2 * ∑ n ≥ 1, r ^ n * cos (n * (θ - φ))`,

which identifies, for instance, the Fourier coefficients of wrapped Cauchy densities.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), section 11.5.
-/

public section

noncomputable section

namespace TauCeti

open Complex

/-- **Geometric series of the Herglotz–Riesz kernel.** If `‖w - c‖ < ‖z - c‖`, then
`herglotzRieszKernel c w z = 1 + 2 * ∑ n ≥ 1, ((w - c) / (z - c)) ^ n`. -/
theorem hasSum_herglotzRieszKernel {c w z : ℂ} (h : ‖w - c‖ < ‖z - c‖) :
    HasSum (fun n : ℕ ↦ 2 * ((w - c) / (z - c)) ^ (n + 1))
      (herglotzRieszKernel c w z - 1) := by
  set q := (w - c) / (z - c) with hq
  have hz : z - c ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt h)
  have hq1 : ‖q‖ < 1 := by
    rwa [hq, norm_div, div_lt_one (norm_pos_iff.mpr hz)]
  have hzw : z - c - (w - c) ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    exact h.ne (congrArg norm h0).symm
  have h1q : 1 - q ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    exact hq1.ne (by rw [← h0, norm_one])
  convert ((hasSum_geometric_of_norm_lt_one hq1).mul_left (2 * q)) using 1
  · funext n
    ring
  · rw [herglotzRieszKernel_def]
    have hw : w - c = q * (z - c) := by rw [hq, div_mul_cancel₀ _ hz]
    rw [hw]
    field_simp
    ring

/-- **Fourier series of the Poisson kernel.** If `‖w - c‖ < ‖z - c‖`, then
`poissonKernel c w z = 1 + 2 * ∑ n ≥ 1, re (((w - c) / (z - c)) ^ n)`. -/
theorem hasSum_poissonKernel {c w z : ℂ} (h : ‖w - c‖ < ‖z - c‖) :
    HasSum (fun n : ℕ ↦ 2 * (((w - c) / (z - c)) ^ (n + 1)).re)
      (poissonKernel c w z - 1) := by
  have := reCLM.hasSum (hasSum_herglotzRieszKernel h)
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply]
  simpa using this

end TauCeti
