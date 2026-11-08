/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.WithDensity

/-!
# Pointwise finite kernels

A kernel whose measures are individually finite is s-finite, even when their total masses
have no uniform bound. Normalizing by one plus the total mass gives a bounded kernel; the
original kernel is recovered by a finite measurable density. This allows the parametric
integration API to apply to random finite measures without artificial deterministic bounds.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- A pointwise finite kernel is s-finite. Uniform boundedness of the masses is unnecessary. -/
theorem isSFiniteKernel_of_isFiniteMeasure (κ : Kernel α β) [∀ a, IsFiniteMeasure (κ a)] :
    IsSFiniteKernel κ := by
  let c : α → ℝ≥0∞ := fun a ↦ 1 + κ a Set.univ
  have hc : Measurable c := measurable_const.add (κ.measurable_coe .univ)
  have hc_ne_zero (a : α) : c a ≠ 0 := by simp [c]
  have hc_ne_top (a : α) : c a ≠ ∞ := by simp [c, measure_ne_top]
  let η : Kernel α β := ⟨fun a ↦ (c a)⁻¹ • κ a, by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [smul_apply, smul_eq_mul]
    exact hc.inv.mul (κ.measurable_coe hs)⟩
  have : IsFiniteKernel η := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun a ↦ ?_⟩⟩
    calc η a Set.univ = (c a)⁻¹ * κ a Set.univ := by
          simp only [η, Kernel.coe_mk, smul_apply, smul_eq_mul]
      _ ≤ (c a)⁻¹ * c a := by gcongr; simp [c]
      _ = 1 := ENNReal.inv_mul_cancel (hc_ne_zero a) (hc_ne_top a)
  have hd : Measurable (Function.uncurry fun a (_ : β) ↦ c a) := hc.comp measurable_fst
  have heq : η.withDensity (fun a _ ↦ c a) = κ := by
    ext a s hs
    rw [Kernel.withDensity_apply' _ hd, MeasureTheory.lintegral_const,
      Measure.restrict_apply_univ]
    simp only [η, Kernel.coe_mk, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (hc_ne_zero a) (hc_ne_top a), one_mul]
  rw [← heq]
  exact isSFiniteKernel_withDensity_of_isFiniteKernel η (fun a _ ↦ hc_ne_top a)

end ProbabilityTheory.Kernel
