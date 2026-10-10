/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral

/-!
# Polar integration over a closed annulus

The polar-coordinate change of variables for a translated closed annulus is the integral on
`[a, b] × [-π, π]` with radial Jacobian `r`, when `a > 0`. The two angular endpoints have
measure zero, so the closed polar rectangle gives the same integral as the slit-plane chart.
This form of Mathlib's `Complex.integral_comp_polarCoord_symm` is suitable for combining polar
integration with Green's formula on a rectangle, without extending a map across the inner disc.
-/

public section

open MeasureTheory Set
open scoped Real

namespace Complex

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Polar integration over the closed annulus of radii `a` and `b` about `z₀`, with radial
Jacobian `p.1`. The angular interval includes both endpoints, whose contribution is null. -/
theorem integral_comp_polarCoord_symm_Icc (f : ℂ → W) (z₀ : ℂ) {a b : ℝ} (ha : 0 < a) :
    (∫ p in Icc (a, -π) (b, π), p.1 • f (z₀ + Complex.polarCoord.symm p)) =
      ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, f z := by
  let S : Set ℂ := {z | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hS : MeasurableSet S := by
    have hn : Continuous (fun z : ℂ ↦ ‖z - z₀‖) := by fun_prop
    exact (isClosed_le continuous_const hn).measurableSet.inter
      (isClosed_le hn continuous_const).measurableSet
  rw [← integral_indicator hS, ← integral_add_left_eq_self (S.indicator f) z₀,
    ← Complex.integral_comp_polarCoord_symm]
  have hEq : EqOn (fun p : ℝ × ℝ ↦ p.1 • S.indicator f (z₀ + Complex.polarCoord.symm p))
      ((Icc a b ×ˢ (univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ ↦ p.1 • f (z₀ + Complex.polarCoord.symm p)))
      _root_.polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hn : ‖z₀ + Complex.polarCoord.symm (r, θ) - z₀‖ = r := by
      simp only [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos (mem_Ioi.mp hr)]
    simp only [S, indicator_apply, mem_ofPred_eq, hn, mem_prod, mem_Icc, mem_univ, and_true]
    split_ifs <;> simp
  rw [setIntegral_congr_fun (by simp [_root_.polarCoord_target]; measurability) hEq,
    setIntegral_indicator (measurableSet_Icc.prod MeasurableSet.univ)]
  have he : _root_.polarCoord.target ∩ (Icc a b ×ˢ (univ : Set ℝ)) =
      Icc a b ×ˢ Ioo (-π) π := by
    ext ⟨r, θ⟩
    simp only [mem_inter_iff, _root_.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo, mem_Icc,
      mem_univ, and_true]
    constructor
    · exact fun h ↦ ⟨h.2, h.1.2⟩
    · exact fun h ↦ ⟨⟨lt_of_lt_of_le ha h.1.1, h.2⟩, h.1⟩
  rw [he, Icc_prod_eq, Measure.volume_eq_prod]
  exact setIntegral_congr_set (Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl)
    Ioo_ae_eq_Icc).symm

end Complex
