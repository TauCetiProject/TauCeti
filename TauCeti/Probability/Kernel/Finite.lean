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
original kernel is recovered by a finite measurable density. `Kernel.normalize` also applies
to arbitrary kernels, sending infinite-mass slices to zero, so it can be used with families
that are only almost everywhere finite. This allows the parametric integration API to apply
to random finite measures without artificial deterministic bounds.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Rescale each slice by one plus its total mass to obtain a kernel of mass at most one.
Infinite-mass slices become zero; this is not normalization to a probability kernel. -/
noncomputable def normalize (κ : Kernel α β) : Kernel α β where
  toFun a := (1 + κ a Set.univ)⁻¹ • κ a
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [smul_apply, smul_eq_mul]
    exact (measurable_const.add (κ.measurable_coe .univ)).inv.mul (κ.measurable_coe hs)

/-- The slices of the normalized kernel. -/
@[simp]
theorem normalize_apply (κ : Kernel α β) (a : α) :
    κ.normalize a = (1 + κ a Set.univ)⁻¹ • κ a := (rfl)

instance (κ : Kernel α β) : IsFiniteKernel κ.normalize := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun a ↦ ?_⟩⟩
  rw [normalize_apply, smul_apply, smul_eq_mul]
  rcases eq_or_ne (κ a Set.univ) ∞ with h | h
  · simp [h]
  rw [ENNReal.inv_mul_le_iff (by simp) (by simp [h]), mul_one]
  exact le_add_self

/-- Recover a pointwise finite kernel from its normalization by a measurable density. -/
@[simp]
theorem withDensity_normalize (κ : Kernel α β) [∀ a, IsFiniteMeasure (κ a)] :
    κ.normalize.withDensity (fun a _ ↦ 1 + κ a Set.univ) = κ := by
  have hd : Measurable (Function.uncurry fun a (_ : β) ↦ 1 + κ a Set.univ) :=
    (measurable_const.add (κ.measurable_coe .univ)).comp measurable_fst
  ext a s hs
  rw [Kernel.withDensity_apply' _ hd, MeasureTheory.lintegral_const,
    Measure.restrict_apply_univ, normalize_apply, smul_apply, smul_eq_mul,
    ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp [measure_ne_top]), one_mul]

/-- A pointwise finite kernel is s-finite. Uniform boundedness of the masses is unnecessary. -/
theorem isSFiniteKernel_of_isFiniteMeasure (κ : Kernel α β) [∀ a, IsFiniteMeasure (κ a)] :
    IsSFiniteKernel κ := by
  have h := isSFiniteKernel_withDensity_of_isFiniteKernel κ.normalize
    (f := fun a _ ↦ 1 + κ a Set.univ) (fun a _ ↦ by simp [measure_ne_top])
  rwa [withDensity_normalize] at h

end ProbabilityTheory.Kernel
