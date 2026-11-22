/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Exponentially weighted integrability of the Gamma function on vertical lines

On a vertical line `Re z = x` with `x` not a nonpositive integer, `Γ(z) exp (θ |Im z|)` is
integrable for every `θ < π / 2`. This follows from Stirling's bound
`‖Γ(x + i y)‖ ≤ C (1 + |y|) ^ (x - 1/2) exp (-π |y| / 2)`
(`TauCeti.exists_norm_Gamma_vertical_line_le`, [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
the weight leaves a factor `exp (-(π / 2 - θ) |y|)`, and `(1 + |y|) ^ (x - 1/2)` times that
factor is integrable (`TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs`).

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
  obtain ⟨C, -, h⟩ := exists_norm_Gamma_vertical_line_le hx
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (x - 1 / 2) (sub_pos.mpr hθ)).const_mul
    C).mono' ((verticalIntegrable_Gamma hx).aestronglyMeasurable.mul (by fun_prop))
    (Eventually.of_forall fun y ↦ ?_)
  simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, norm_mul, norm_real,
    Real.norm_eq_abs, Real.abs_exp]
  calc ‖Gamma (x + y * I)‖ * Real.exp (θ * |y|)
      ≤ C * (1 + |y|) ^ (x - 1 / 2) * Real.exp (-(π * |y| / 2)) * Real.exp (θ * |y|) := by
        gcongr
        exact h y
    _ = C * ((1 + |y|) ^ (x - 1 / 2) * Real.exp (-((π / 2 - θ) * |y|))) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

end TauCeti
