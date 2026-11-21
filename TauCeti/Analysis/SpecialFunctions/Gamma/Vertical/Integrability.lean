/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Exponentially weighted integrability of the Gamma function on vertical lines

On a vertical line `Re z = x` with `x` not a nonpositive integer, `Γ(z) exp (θ |Im z|)` is
integrable for every `θ < π / 2`. This follows from Stirling's bound
`‖Γ(x + i y)‖ ≤ C (1 + |y|) ^ (x - 1/2) exp (-π |y| / 2)`
(`TauCeti.exists_norm_Gamma_vertical_line_le`, [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
the weight leaves a factor `exp (-(π / 2 - θ) |y|)`, which absorbs the power.

## Main results

* `TauCeti.verticalIntegrable_Gamma_mul_exp_mul_abs_im`: `Γ(z) exp (θ |Im z|)` is integrable on
  every pole-free vertical line, for `θ < π / 2`.

The statement follows the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Gamma/VerticalStrips.lean`, whose proof goes through the product formula for `|Γ|`
instead of Stirling's formula.
-/

public section

open Real Set Filter MeasureTheory

namespace TauCeti

open Complex

/-- On a vertical line `Re z = x` with `x` not a nonpositive integer, `Γ(z) exp (θ |Im z|)` is
integrable for every `θ < π / 2`. -/
theorem verticalIntegrable_Gamma_mul_exp_mul_abs_im {x θ : ℝ} (hx : ∀ n : ℕ, x ≠ -n)
    (hθ : θ < π / 2) :
    VerticalIntegrable (fun z ↦ Gamma z * (Real.exp (θ * |z.im|) : ℂ)) x := by
  obtain ⟨C, hC, h⟩ := exists_norm_Gamma_vertical_line_le hx
  set c := (π / 2 - θ) / 2
  have hc : 0 < c := by simp only [c]; linarith
  obtain ⟨M, -, hM⟩ := exists_rpow_mul_exp_neg_mul_le (abs_nonneg (x - 1 / 2)) hc
  refine ((integrable_exp_neg_mul_abs hc).const_mul (C * M * Real.exp c)).mono'
    ((verticalIntegrable_Gamma hx).aestronglyMeasurable.mul (by fun_prop))
    (Eventually.of_forall fun y ↦ ?_)
  have hpow : (1 + |y|) ^ (x - 1 / 2) ≤ (1 + |y|) ^ |x - 1 / 2| :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (le_abs_self _)
  have hsplit : Real.exp (-(π * |y| / 2)) * Real.exp (θ * |y|) =
      Real.exp (-(c * (1 + |y|))) * Real.exp c * Real.exp (-(c * |y|)) := by
    simp only [← Real.exp_add, c]
    ring_nf
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp]
  calc ‖Gamma (x + y * I)‖ * Real.exp (θ * |y|)
      ≤ C * (1 + |y|) ^ |x - 1 / 2| * Real.exp (-(π * |y| / 2)) * Real.exp (θ * |y|) := by
        gcongr
        exact (h y).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
          (Real.exp_pos _).le)
    _ = C * ((1 + |y|) ^ |x - 1 / 2| * Real.exp (-(c * (1 + |y|)))) * Real.exp c *
          Real.exp (-(c * |y|)) := by
        rw [mul_assoc, hsplit]
        ring
    _ ≤ C * M * Real.exp c * Real.exp (-(c * |y|)) := by
        gcongr
        exact hM (1 + |y|) (by positivity)

end TauCeti
