/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Winding numbers of periodic curves

If a `C¹` curve `γ` of period `T` avoids `w`, its winding number around `w` over `n` whole
periods, starting anywhere, is `n` times its winding number over one period
(`TauCeti.Contour.windingNumber_add_mul_eq_of_periodic`): the index integrand is continuous and
periodic, so its integral over any interval of length `n T` is `n` times its integral over any
interval of length `T`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Contour

/-- **Winding numbers of a periodic curve over whole periods.** If a `C¹` curve `γ` of period `T`
avoids `w`, then its winding number around `w` over `n` periods, starting anywhere, is `n` times
its winding number over one period. -/
theorem windingNumber_add_mul_eq_of_periodic {γ : ℝ → ℂ} {T : ℝ} {w : ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ T) (hw : ∀ t, γ t ≠ w) (n : ℤ) (t s : ℝ) :
    windingNumber γ t (t + n * T) w = n * windingNumber γ s (s + T) w := by
  -- The index integrand is continuous and periodic.
  set K : ℝ → ℂ := fun u ↦ (γ u - w)⁻¹ * deriv γ u with hKdef
  have hKc : Continuous K :=
    ((hγ.continuous.sub continuous_const).inv₀ fun u ↦ sub_ne_zero.2 (hw u)).mul
      (hγ.continuous_deriv le_rfl)
  have hKper : Function.Periodic K T := fun u ↦ by
    have hd : deriv γ (u + T) = deriv γ u := by
      rw [← deriv_comp_add_const]
      exact congrArg (deriv · u) (funext hper)
    simp only [hKdef, hd, hper u]
  have hKint (t₁ t₂ : ℝ) : IntervalIntegrable K volume t₁ t₂ := hKc.intervalIntegrable _ _
  rw [windingNumber_eq_integral_of_avoidance hγ.continuous.continuousOn (fun u _ ↦ hw u)
      (hKint _ _),
    windingNumber_eq_integral_of_avoidance hγ.continuous.continuousOn (fun u _ ↦ hw u)
      (hKint _ _), ← zsmul_eq_mul, hKper.intervalIntegral_add_zsmul_eq n t hKint,
    hKper.intervalIntegral_add_eq t s, zsmul_eq_mul]
  ring

end TauCeti.Contour
