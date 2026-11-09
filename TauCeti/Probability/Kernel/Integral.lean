/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Probability.Kernel.Finite

/-!
# Integration and kernel normalization

Integrals against a finite slice of a kernel can be recovered from integrals against its
normalization by multiplying by one plus the slice's total mass. Only the chosen slice needs
to be finite; the kernel need not have uniformly bounded masses or even be s-finite.
These identities let finite-kernel integration results apply to individually finite slices.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Recover a nonnegative integral from the normalized kernel at a finite slice. -/
theorem lintegral_eq_mul_normalize (κ : Kernel α β) {a : α} (ha : κ a univ ≠ ∞)
    (f : β → ℝ≥0∞) :
    ∫⁻ x, f x ∂κ a = (1 + κ a univ) * ∫⁻ x, f x ∂κ.normalize a := by
  rw [normalize_apply, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp [ha]), one_mul]

/-- Recover a Bochner integral from the normalized kernel at a finite slice.
No integrability or completeness assumption is needed. -/
theorem integral_eq_smul_normalize {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (κ : Kernel α β) {a : α} (ha : κ a univ ≠ ∞) (f : β → F) :
    ∫ x, f x ∂κ a = (1 + κ a univ).toReal • ∫ x, f x ∂κ.normalize a := by
  have h0 : (1 + κ a univ).toReal ≠ 0 := (ENNReal.toReal_pos (by simp) (by simp [ha])).ne'
  rw [normalize_apply, integral_smul_measure, ENNReal.toReal_inv, smul_smul,
    mul_inv_cancel₀ h0, one_smul]

end ProbabilityTheory.Kernel
