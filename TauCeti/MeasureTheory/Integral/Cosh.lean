/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrals of hyperbolic cosines and secants

An integrand dominated by `C * cosh (k * t)` has a primitive bounded by
`C * cosh (k * t) / k` for `k > 0`, in either time direction. This estimate controls
Picard iteration in a weighted space of bounded continuous functions on the whole real line.

The hyperbolic secant `(cosh x)⁻¹` is square integrable on the line (`TauCeti.memLp_inv_cosh`),
because `(cosh x)⁻² ≤ 4 (1 + x²)⁻¹`. It is the decaying solution of the scalar equation
`v' = -tanh(s) v`, which describes both the kernel of `d/ds + tanh` and the cokernel (the kernel of
the formal adjoint) of `d/ds - tanh`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A hyperbolic-cosine bound on an integrand gives a hyperbolic-cosine bound on its interval
integral from zero, for either sign of the endpoint. Only an almost-everywhere bound on the
interval of integration is required. -/
theorem norm_intervalIntegral_le_cosh {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C)
    {F : ℝ → E} (t : ℝ)
    (hF : ∀ᵐ s ∂volume.restrict (uIoc 0 t), ‖F s‖ ≤ C * Real.cosh (k * s)) :
    ‖∫ s in (0 : ℝ)..t, F s‖ ≤ C * Real.cosh (k * t) / k := by
  have hg : Continuous fun s : ℝ ↦ C * Real.cosh (k * s) := by fun_prop
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ C * Real.sinh (k * s) / k)
      (C * Real.cosh (k * s)) s := by
    intro s
    simpa [← mul_assoc, hk.ne'] using
      (((hasDerivAt_id s).const_mul k).sinh.const_mul C).div_const k
  have hcalc : ∫ s in (0 : ℝ)..t, C * Real.cosh (k * s) =
      C * Real.sinh (k * t) / k := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
      (hg.intervalIntegrable _ _)]
    simp
  calc ‖∫ s in (0 : ℝ)..t, F s‖
      ≤ |∫ s in (0 : ℝ)..t, C * Real.cosh (k * s)| :=
        intervalIntegral.norm_integral_le_abs_of_norm_le hF
          (hg.intervalIntegrable _ _)
    _ = C * |Real.sinh (k * t)| / k := by
        rw [hcalc, abs_div, abs_mul, abs_of_nonneg hC, abs_of_pos hk]
    _ ≤ C * Real.cosh (k * t) / k := by
        gcongr
        rw [Real.abs_sinh, ← Real.cosh_abs (k * t)]
        exact (Real.sinh_lt_cosh _).le

/-- The hyperbolic secant `(cosh x)⁻¹` is square integrable on the line: it is dominated by
`2 (1 + x²)^(-1/2)`. -/
theorem memLp_inv_cosh : MemLp (fun x : ℝ ↦ (Real.cosh x)⁻¹) 2 := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 <|
    (integrable_inv_one_add_sq.const_mul 4).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  have hx : 1 + |x| ≤ 2 * Real.cosh x := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    linarith [Real.add_one_le_exp |x|, Real.exp_pos (-|x|)]
  have hx2 : 1 + x ^ 2 ≤ 4 * Real.cosh x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hc := Real.cosh_pos x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (Real.cosh x)⁻¹ ^ 2 = 4 * (4 * Real.cosh x ^ 2)⁻¹ := by field_simp
    _ ≤ 4 * (1 + x ^ 2)⁻¹ := by gcongr

end TauCeti
