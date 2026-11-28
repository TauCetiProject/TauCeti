/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p

/-!
# The Dirichlet energy on an interval

On a bounded interval `(a, b)`, the Dirichlet form of two classes `u, v ∈ H¹(a, b)` is
`∫_a^b u' v'`, the `L²` inner product of their weak gradients
(`TauCeti.W1p.setIntegral_gradient_mul_gradient_eq_inner`). A class of zero energy,
`∫_a^b w'² = 0`, is constant: its continuous representative equals its value at `a` on all of
`[a, b]` (`TauCeti.W1p.intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero`). This
is the uniqueness step of the weak Neumann and mixed problems for `-u''` on an interval.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti.W1p

variable {a b : ℝ}

local instance instIsFiniteMeasureRestrictVolumeIooEnergy : IsFiniteMeasure (volume.restrict
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) := ⟨by simp⟩

/-- **Zero energy, constant function.** If `∫_a^b w'² = 0`, the continuous representative of `w`
is constant on `[a, b]`, equal to its value at `a`. -/
theorem intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero
    (hab : a < b) {w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2}
    (hw : ∫ t in Ioo a b, gradient w t * gradient w t = 0) (t : Icc a b) :
    intervalRepresentativeL hab w t = (intervalTraceL hab w).1 := by
  have h : ⟪gradient w, gradient w⟫_ℝ = 0 := by
    simpa only [Opens.coe_mk, hw] using (setIntegral_gradient_mul_gradient_eq_inner w w).symm
  rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h
  obtain ⟨c, rfl⟩ := exists_eq_const_of_gradient_eq_zero isPreconnected_Ioo h
  simp [intervalRepresentativeL_const]

end TauCeti.W1p
